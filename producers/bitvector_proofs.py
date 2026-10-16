#!/usr/bin/env python3
"""Untrusted SAT proof producer; Ink independently reconstructs and checks CNF.

Requires python-sat==1.9.dev5. The solver and hint search are never imported by Ink.
"""
import argparse
import hashlib
import json
import subprocess
import time
import threading
from pathlib import Path
if __package__ in (None, ""):
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from producers.inductive_proofs import SEMANTICS, var, binary

from producers.workspace import CORE_ROOT as ROOT, KNOWLEDGE_ROOT, compiler_path


def source(term):
    kind, value = next(iter(term.items()))
    if kind == 'U64': return {'Num': value}
    if kind in ('Var', 'Bool'): return term
    if kind == 'Binary': return {'Binary': [value['op'], source(value['left']), source(value['right'])]}
    if kind == 'If': return {'Call': ['choose', [source(value[k]) for k in ['condition', 'on_true', 'on_false']]]}
    raise ValueError(kind)


class HintBuilder:
    """Untrusted watched-literal RUP search. Rust replays every returned hint."""
    def __init__(self, clauses, deadline=None):
        self.deadline=deadline
        self.clauses=[];self.positions=[];self.watches={};self.units=[];self.empty=[]
        for clause in clauses:self.add(clause)
    def check_deadline(self):
        if self.deadline is not None and time.monotonic()>=self.deadline:
            raise ValueError('Proof authoring exceeded its total time budget')
    def add(self, clause):
        self.check_deadline()
        index=len(self.clauses);self.clauses.append(list(clause))
        if not clause:self.empty.append(index);self.positions.append([]);return
        if len(clause)==1:self.units.append(index);self.positions.append([0]);return
        self.positions.append([0,1])
        for lit in clause[:2]:self.watches.setdefault(lit,[]).append(index)
    def hints(self, clause):
        self.check_deadline()
        values={};queue=[];hints=[];reasons={}
        def state(lit):return None if abs(lit)not in values else values[abs(lit)]==(lit>0)
        def assign(lit,reason=None):values[abs(lit)]=lit>0;reasons[abs(lit)]=reason;queue.append(lit)
        def finish(conflict):
            needed={conflict};pending=[conflict]
            while pending:
                self.check_deadline()
                index=pending.pop()
                for lit in self.clauses[index]:
                    reason=reasons.get(abs(lit))
                    if reason is not None and reason not in needed:
                        needed.add(reason);pending.append(reason)
            return [i for i in hints if i in needed]+[conflict]
        for lit in clause:
            if state(-lit)is False:return []
            if state(-lit)is None:assign(-lit)
        if self.empty:return [self.empty[0]]
        for index in self.units:
            lit=self.clauses[index][0]
            if state(lit)is False:return finish(index)
            if state(lit)is None:hints.append(index);assign(lit,index)
        head=0
        while head<len(queue):
            self.check_deadline()
            false=-queue[head];head+=1;watched=self.watches.setdefault(false,[]);position=0
            while position<len(watched):
                if position%256==0:self.check_deadline()
                index=watched[position];candidate=self.clauses[index];ps=self.positions[index]
                slot=0 if candidate[ps[0]]==false else 1;other=candidate[ps[1-slot]]
                if state(other)is True:position+=1;continue
                replacement=next((i for i,lit in enumerate(candidate)if i not in ps and state(lit)is not False),None)
                if replacement is not None:
                    ps[slot]=replacement;watched[position]=watched[-1];watched.pop();self.watches.setdefault(candidate[replacement],[]).append(index);continue
                if state(other)is False:return finish(index)
                hints.append(index);assign(other,index);position+=1
        raise ValueError('Solver step is not RUP; no unchecked RAT steps accepted')

def hints_for(clause, clauses):
    return HintBuilder(clauses).hints(clause)


def certificate(problem, seconds=60, conflicts=100_000, total_seconds=None):
    # SAT solving is only part of authoring: expanding proof hints can dominate.
    # Callers can bound the whole acquisition without changing core authority.
    if total_seconds is not None and not 0<total_seconds<=600:
        raise ValueError('total proof authoring budget must be in (0,600] seconds')
    deadline=None if total_seconds is None else time.monotonic()+total_seconds
    def check_deadline():
        if deadline is not None and time.monotonic()>=deadline:
            raise ValueError('Proof authoring exceeded its total time budget')
    from pysat.solvers import Glucose3
    with Glucose3(bootstrap_with=problem['clauses'], with_proof=True) as solver:
        check_deadline()
        solver.conf_budget(conflicts)
        timer = threading.Timer(seconds if deadline is None else min(seconds,max(0.001,deadline-time.monotonic())), solver.interrupt)
        timer.daemon = True
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        if result is None: raise ValueError('Proof search exhausted its time or conflict budget')
        if result: raise ValueError('Proposed equality is false; solver found a counterexample')
        trace = solver.get_proof()
    check_deadline()
    clauses = [list(c) for c in problem['clauses']]; steps = []; builder=HintBuilder(clauses,deadline)
    for line in trace:
        check_deadline()
        if line.startswith('d '): continue  # Retaining earlier proved clauses is sound.
        numbers = [int(n) for n in line.split()]
        if not numbers or numbers[-1] != 0: raise ValueError('Malformed solver proof')
        clause = sorted(set(numbers[:-1]))
        hints = builder.hints(clause)
        steps.append(dict(clause=clause, hints=hints)); clauses.append(clause);builder.add(clause)
        if not clause: break
    if not steps or steps[-1]['clause']:
        steps.append(dict(clause=[], hints=builder.hints([])))
    # Keep the dependency closure of the final contradiction. Every retained
    # clause still carries its complete RUP justification, with remapped ids.
    original=len(problem['clauses']); needed={len(steps)-1}; pending=list(needed)
    while pending:
        check_deadline()
        for hint in steps[pending.pop()]['hints']:
            if hint>=original and hint-original not in needed:
                needed.add(hint-original);pending.append(hint-original)
    order=sorted(needed);remap={old:original+i for i,old in enumerate(order)}
    steps=[dict(clause=steps[i]['clause'],hints=[h if h<original else remap[h-original] for h in steps[i]['hints']])for i in order]
    check_deadline()
    result = dict(problem_sha256=problem['sha256'], steps=steps)
    if 'encoding' in problem:
        result['encoding'] = problem['encoding']
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--compiler', type=Path, default=compiler_path('target/debug/ink'))
    parser.add_argument('--case', action='append', help='generate only named examples')
    parser.add_argument('--solver-seconds', type=float, default=60)
    parser.add_argument('--conflicts', type=int, default=100_000)
    parser.add_argument('--compact-seconds', type=float, default=0,
                        help='opt-in root-unit factoring/inlining budget; ordinary replay still required')
    parser.add_argument('--pack-hints', action='store_true',
                        help='opt-in bounded lossless hint transport; ordinary replay still required')
    args = parser.parse_args(); directory = args.directory.resolve()
    if not 0 < args.solver_seconds <= 600 or not 0 < args.conflicts <= 1_000_000: parser.error('invalid proof-search budget')
    if not 0 <= args.compact_seconds <= 600: parser.error('invalid proof-compaction budget')
    (directory / 'objects').mkdir(parents=True, exist_ok=True)
    scratch = KNOWLEDGE_ROOT / 'build/bitvector-producer'; scratch.mkdir(parents=True, exist_ok=True)
    compiler = args.compiler.resolve(); names = {}; proposals = []; sources = []; measurements = []

    def store(name, kind, declaration, dependencies=()):
        data = (json.dumps(dict(schema=1,semantics=SEMANTICS,name=name,dependencies=list(dependencies),declaration={kind:declaration}),separators=(',',':'))+'\n').encode()
        identity = hashlib.sha256(data).hexdigest(); path = directory / 'objects' / f'{identity}.json'
        if path.exists(): assert path.read_bytes() == data
        else: path.write_bytes(data)
        names[name] = identity; return identity

    datatype = store('List64', 'Datatype', dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64','SelfType'])]))
    x, y = var('p0'), var('p1')
    examples = [
        ('add_zero', [['p0','U64']], binary('+',x,{'U64':0}), x),
        ('subtract_self', [['p0','U64']], binary('-',x,x), {'U64':0}),
        ('add_commute', [['p0','U64'],['p1','U64']], binary('+',x,y), binary('+',y,x)),
        ('cancel_add', [['p0','U64'],['p1','U64']], binary('-',binary('+',x,y),y), x),
        ('multiply_zero', [['p0','U64']], binary('*',x,{'U64':0}), {'U64':0}),
        ('unsigned_reflexive', [['p0','U64']], binary('<=',x,x), {'Bool':True}),
        ('unsigned_maximum', [['p0','U64']], binary('<=',x,{'U64':(1<<64)-1}), {'Bool':True}),
        ('choose_equal', [['p0','U64'],['p1','Bool']], {'If':dict(condition=y,on_true=x,on_false=x)}, x),
        ('given_equal', [['p0','U64'],['p1','U64']], binary('-',x,y), {'U64':0}),
    ]
    if args.case:
        known = {e[0] for e in examples}
        if set(args.case) - known: parser.error('unknown example name')
        examples = [e for e in examples if e[0] in args.case]
    from producers.collection_proofs import render
    for name, params, left, right in examples:
        conditions = [dict(**{'from':x,'to':y})] if name == 'given_equal' else []
        goal = dict(params=params,conditions=conditions,**{'from':left,'to':right})
        path = scratch / f'{name}.goal.json'; path.write_text(json.dumps(goal))
        cnf = scratch / f'{name}.cnf.json'
        subprocess.run([compiler,'bitvector-obligation',path,'-o',cnf],check=True,capture_output=True)
        problem = json.loads(cnf.read_text()); start = time.perf_counter()
        proof = certificate(problem,args.solver_seconds,args.conflicts); elapsed = time.perf_counter()-start
        compaction = None
        if args.compact_seconds:
            from producers.rup_compaction import compact_certificate
            proof, compaction = compact_certificate(problem, proof, args.compact_seconds)
        hints = sum(len(s['hints']) for s in proof['steps'])
        packing = None
        if args.pack_hints:
            from producers.rup_transport import pack_certificate
            before = len(json.dumps(proof, sort_keys=True, separators=(',', ':')).encode())
            proof = pack_certificate(proof)
            packing = dict(before_bytes=before,
                           after_bytes=len(json.dumps(proof, sort_keys=True, separators=(',', ':')).encode()),
                           decoded_hints=hints)
        derivation = {'BitVector':dict(**{'from':left,'to':right},hypotheses=list(range(len(conditions))),certificate=proof)}
        identity = store(name,'Theorem',dict(**goal,proof=derivation))
        if not conditions: proposals.append(dict(function=name,**{'from':source(left),'to':source(right)},datatype=datatype,from_definitions=[],to_definitions=[],proof={'Use':dict(theorem=identity,arguments=[var(n) for n,_ in params],premises=[])}))
        result = 'Bool' if name in ('unsigned_reflexive','unsigned_maximum') else 'u64'
        if not conditions: sources.append(f'fn {name}('+', '.join(n+': '+('u64' if t=='U64' else t) for n,t in params)+f') -> {result} {{ return {render(source(left))}; }}')
        measurements.append(dict(name=name,conditions=len(conditions),variables=problem['variables'],clauses=len(problem['clauses']),steps=len(proof['steps']),hints=hints,producer_seconds=elapsed,problem_sha256=problem['sha256']))
        if packing is not None:
            measurements[-1]['hint_transport'] = packing
            measurements[-1]['producer_seconds'] = time.perf_counter() - start
        if compaction is not None:
            measurements[-1]['compaction'] = compaction
            measurements[-1]['producer_seconds'] = time.perf_counter() - start
        print(f'{name}: {len(proof["steps"])} checked-step proposals, {elapsed:.3f}s producer time',flush=True)
    (directory/'lock.json').write_text(json.dumps(dict(schema=1,semantics=SEMANTICS,objects=list(names.values())),indent=2)+'\n')
    (directory/'names.json').write_text(json.dumps(names,indent=2)+'\n')
    (directory/'proposal.json').write_text(json.dumps(dict(schema=1,semantics='source-collections-v1',library='lock.json',proposals=proposals),indent=2)+'\n')
    (directory/'kernels.ink').write_text('module bitvector_proofs;\n\n'+'\n\n'.join(sources)+'\n')
    (directory/'production.json').write_text(json.dumps(dict(solver='PySAT Glucose3',compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),measurements=measurements),indent=2)+'\n')
    subprocess.run([compiler,'verify-library',directory/'lock.json'],check=True,capture_output=True)
    subprocess.run([compiler,'emit-rust',directory/'kernels.ink','--implementation',directory/'proposal.json','-o',scratch/'checked.rs'],check=True,capture_output=True)
    print(f'Ink independently checked {len(examples)} arithmetic theorems and {len(proposals)} exact source replacements.',flush=True)


if __name__ == '__main__': main()
