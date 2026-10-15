"""Author explicit source-bound correspondence laws with ordinary normalization.

Names select equations to attempt, never proof authority. Every equation and its
exact definition context replay before publication. This is neither an AD proof
rule nor a profitability decision; unsupported equalities simply fail admission.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from ink_knowledge import Store, canonical, identity, semantic_entry
from .definition_context28 import bind
from .semantic_laws import law, op, value, var


def acquire(source, compiler, directory, pairs, *, store_root=None):
    source, compiler, directory = Path(source).resolve(), Path(compiler).resolve(), Path(directory)
    pairs = list(pairs)
    if not 1 <= len(pairs) <= 8 or len({tuple(p) for p in pairs}) != len(pairs):
        raise ValueError('correspondence requires 1..8 distinct function pairs')
    directory.mkdir(parents=True, exist_ok=True)
    if (directory/'receipt.json').exists():
        raise ValueError('Choose a fresh acquisition directory')
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    compiler_hash = hashlib.sha256(compiler.read_bytes()).hexdigest()
    def invoke(*args):
        r = subprocess.run([str(compiler), *map(str,args)], capture_output=True, text=True, timeout=120)
        if r.returncode:
            raise ValueError(r.stderr[-4000:])
        return json.loads(r.stdout) if r.stdout.lstrip().startswith("{") else r.stdout
    core, subject = directory/'core.json', directory/'subject.json'
    invoke('emit-core', source, '-o', core)
    invoke('emit-semantic', core, '--core', '-o', subject)
    executable, semantic = json.loads(core.read_bytes()), json.loads(subject.read_bytes())
    functions = {f['name']:f for f in executable['program']['functions']}
    objects, names, equations = [], {}, []
    for left,right in pairs:
        if left not in functions or right not in functions:
            raise ValueError('correspondence requires two named pure functions')
        a,b = functions[left],functions[right]
        if a['result'] != b['result'] or [t for _,t in a['params']] != [t for _,t in b['params']]:
            raise ValueError('correspondence requires identical typed signatures')
        params = {n:value(t) for n,t in a['params']}
        args = [var(params[n],n) for n,_ in a['params']]
        theorem = bind(law(params, op(value(a['result']),'call:'+left,*args),
                         op(value(a['result']),'call:'+right,*args)),executable,semantic)
        obj = semantic_entry(theorem)
        objects.append(obj)
        ident = identity(obj)
        names['function-correspondence/'+left+'/'+right+'/'+ident] = ident
        equations.append(dict(left=left,right=right,law=ident))
    local = Store.publish(directory/'knowledge',objects,names)
    view = local.bundle([identity(o) for o in objects])
    view_path = directory/'view.json'
    view_path.write_bytes(canonical(view))
    admission = invoke('knowledge-check',core,view_path)
    if hashlib.sha256(source.read_bytes()).hexdigest()!=source_hash or hashlib.sha256(compiler.read_bytes()).hexdigest()!=compiler_hash:
        raise ValueError('Acquisition input changed')
    snapshot = None
    if store_root is not None:
        installed = Store(store_root).extend(objects,names)
        snapshot = installed.snapshot_id
    receipt = dict(schema=1,source_sha256=source_hash,compiler_sha256=compiler_hash,
                   input_core_sha256=semantic['input_core_sha256'],equations=equations,
                   admission=admission,snapshot=snapshot,
                   scope='Universal typed source equalities for these exact definitions; no AD-transform, backend-correctness or profitability theorem')
    (directory/'receipt.json').write_bytes(canonical(receipt)+b'\n')
    return view,receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path)
    p.add_argument('--compiler',type=Path,required=True)
    p.add_argument('--pair',nargs=2,action='append',required=True,metavar=('LEFT','RIGHT'))
    p.add_argument('-o',type=Path,required=True)
    p.add_argument('--output-store',type=Path)
    args = p.parse_args()
    _,receipt = acquire(args.source,args.compiler,args.o,args.pair,store_root=args.output_store)
    print(json.dumps(receipt))
if __name__=='__main__':
    main()
