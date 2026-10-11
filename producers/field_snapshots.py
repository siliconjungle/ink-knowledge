"""Author private, typed field deltas from a checked record declaration.

This is an untrusted source producer, not a compiler pattern or admission path.
The generated public entry returns final values; delta helpers own Buffers and
therefore cannot be called through the JavaScript public value ABI.
"""
import argparse
import json
import subprocess
from pathlib import Path


def spelling(t):
    if isinstance(t, str):
        return {'U32': 'u32', 'U64': 'u64', 'I32': 'i32', 'F32': 'f32'}.get(t, t)
    kind, arg = next(iter(t.items()))
    if kind == 'Named':
        return arg
    if kind == 'Vector':
        return f'Vec{arg[1]}<{spelling(arg[0])}>'
    if kind in ('List', 'Option'):
        return f'{kind}<{spelling(arg)}>'
    if kind == 'Result':
        return f'Result<{spelling(arg[0])},{spelling(arg[1])}>'
    raise ValueError('field snapshots require immutable value fields')


def source(program, record):
    fields = program['records'][record]
    if not fields:
        raise ValueError('record has no fields to edit')
    if len(fields)>64:
        raise ValueError('field replay exceeds the external authoring bound of 64 laws')
    # Discover only the schema closure, avoiding unrelated function/effect code.
    names = set()
    def visit(t):
        if isinstance(t, str):
            return
        kind, arg = next(iter(t.items()))
        if kind == 'Named':
            if arg in names:
                return
            names.add(arg)
            for _, ft in program['records'].get(arg, []):
                visit(ft)
        elif kind in ('List', 'Option'):
            visit(arg)
        elif kind in ('Result', 'Vector'):
            for ft in (arg if kind == 'Result' else arg[:1]):
                visit(ft)
        else:
            raise ValueError('owned or unsupported record field')
    visit({'Named': record})
    lines = ['module ink.knowledge.field_snapshots;']
    for name in sorted(names):
        if name in program['records']:
            lines.append('record ' + name + '{' + ','.join(f'{f}:{spelling(t)}' for f, t in program['records'][name]) + ',}')
        elif name in program['enums']:
            lines.append('enum ' + name + '{' + ','.join(program['enums'][name]) + ',}')
        elif name in program['ids']:
            lines.append('id ' + name + ';')
        else:
            raise ValueError('unknown named field type: ' + name)
    if any(n.startswith('InkField') for n in names):
        raise ValueError('generated schema namespace collision')
    lines.append('record InkFieldStored<T>{value:T,}')
    groups={}
    for i,(f,t) in enumerate(fields):groups.setdefault(json.dumps(t,sort_keys=True),[]).append((i,f,t))
    # Small carrier groups keep portable definition contexts within the kernel
    # depth bound. This is a producer limit, never a checker exception.
    groups=[group[i:i+2] for group in groups.values() for i in range(0,len(group),2)]
    for g,group in enumerate(groups):
        ty=spelling(group[0][2]);delta=f'InkFieldDelta{g}';values=f'InkFieldValues{g}'
        lines.extend([f'record {delta}{{field:u32,value:{ty},}}',
                      'record '+values+'{'+','.join(f'{f}:{spelling(t)}' for _,f,t in group)+',}',
                      f'fn build_fields{g}(a:{record},b:{record})->Buffer<{delta}>{{',
                      f'var out:Buffer<{delta}>=Buffer.empty();'])
        for i,f,t in group:
            carrier='InkFieldStored<'+spelling(t)+'>'
            condition=f'{carrier}{{value:a.{f}}}!={carrier}{{value:b.{f}}}'
            lines.append(f'if {condition}{{out=out.push({delta}{{field:{i},value:b.{f}}});}}')
        lines.extend(['return out;}',f'fn replay_fields{g}(a:{record},edits:Buffer<{delta}>)->{values}{{'])
        for i,f,t in group:lines.append(f'var v{i}:{spelling(t)}=a.{f};')
        lines.append('for edit in edits.freeze(){')
        for i,f,t in group:lines.append(f'if edit.field=={i}{{v{i}=edit.value;}}')
        lines.extend(['}','return '+values+'{'+','.join(f'{f}:v{i}' for i,f,t in group)+',};}'])
    lines.extend([f'fn reconcile_fields(before:List<{record}>,after:List<{record}>)->List<{record}>{{',
                  'if before==after{return before;}',
                  f'var out:Buffer<{record}>=buffer(before).truncate(length(after));var index:u32=0;',
                  'for row in after{if index>=length(before){out=out.push(row);}else{',
                  f'let previous:{record}=before.at_or(index,row);',
                  'if previous!=row{'])
    for g,group in enumerate(groups):lines.append(f'let fields{g}=replay_fields{g}(previous,build_fields{g}(previous,row));')
    replacement=record+'{'+','.join(f'{f}:fields{g}.{f}' for g,group in enumerate(groups) for _,f,t in group)+',}'
    lines.extend([f'out=out.set(index,{replacement});','}}index=index+1;}return out.freeze();}'])
    executable='\n'.join(lines)+'\n'
    laws=[]
    for g,group in enumerate(groups):
        for i,f,t in group:
            replacement=f'InkFieldValues{g}'+'{'+','.join(f'{name}:'+('value' if j==i else f'a.{name}') for j,name,_ in group)+',}'
            payload=f'InkFieldDelta{g}'+'{'+f'field:{i},value:value'+'}'
            laws.append(f'rewrite replay_field_{i}(a:{record},value:{spelling(t)}){{from replay_fields{g}(a,buffer_fill(1,{payload}));to {replacement};proof by normalize;}}')
    return executable,executable+'\n'.join(laws)+'\n'


def generate(compiler, input_source, record, output):
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    core = output.with_suffix('.core.json')
    subprocess.run([str(compiler), 'emit-core', str(input_source), '-o', str(core)], check=True, capture_output=True)
    program = json.loads(core.read_text())['program']
    executable,laws=source(program, record)
    output.write_text(executable)
    law_source=output.with_suffix(".laws.ink");law_source.write_text(laws)
    checked=subprocess.run([str(compiler), 'check', str(output)], capture_output=True, text=True)
    if checked.returncode:raise ValueError(checked.stderr.strip())
    bundle=output.with_suffix('.laws.json')
    authored=subprocess.run([str(compiler),'emit-laws',str(law_source),'-o',str(bundle)],capture_output=True,text=True)
    if authored.returncode:raise ValueError(authored.stderr.strip())
    return {'laws':str(bundle),'record': record, 'fields': len(program['records'][record]), 'source': str(output)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--record', required=True)
    parser.add_argument('-o', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(generate(args.compiler, args.source, args.record, args.o)))
