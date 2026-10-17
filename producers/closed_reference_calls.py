"""Bounded reference evaluations propose literals; complete proofs authorize them.

No evaluation-budget override, selection, state snapshot or generated helper is
passed to the reference evaluator. Failure leaves ordinary source execution.
"""
import json
from pathlib import Path
import subprocess
import tempfile

from producers.frozen_specialization import float_bits, literal


def argument_value(ty, expression, program):
    if ty in ('U32', 'U64') and set(expression) == {'Num'}:
        return expression['Num']
    if ty == 'Bool' and set(expression) == {'Bool'}:
        return expression['Bool']
    if ty == 'String' and set(expression) == {'String'}:
        return expression['String']
    if ty == 'F32':
        bits = float_bits(expression)
        if bits is not None:
            return {'F32Bits': bits}
    if ty == 'Unit' and expression == 'Unit':
        return None
    if isinstance(ty, dict):
        recur = lambda t, e: argument_value(t, e, program)
        if 'Named' in ty:
            name = ty['Named']
            if name in program['records'] and expression.get('Record', [None])[0] == name:
                fields = dict(expression['Record'][1])
                return {n: recur(t, fields[n]) for n, t in program['records'][name]}
            if name in program['enums']:
                if 'Field' in expression:
                    base, variant = expression['Field']
                    if base == {'Var': name} and variant in program['enums'][name]:
                        return name+'.'+variant
                if expression.get('Var') in [name+'.'+v for v in program['enums'][name]]:
                    return expression['Var']
        if 'Option' in ty and expression == {'Var': 'None'}:
            return {'None': None}
        if 'Call' in expression:
            name, args = expression['Call']
            if 'Option' in ty and name == 'Some' and len(args) == 1:
                return {'Some': recur(ty['Option'], args[0])}
            if 'Result' in ty and name in ('Ok','Err') and len(args) == 1:
                return {name: recur(ty['Result'][name == 'Err'], args[0])}
            if 'List' in ty and name == 'list':
                return [recur(ty['List'], x) for x in args]
    raise ValueError('unsupported closed reference argument')


class ReferenceCalls:
    MAX_CALLS = 16
    MAX_BYTES = 16_000_000

    def __init__(self, source, compiler):
        self.source = Path(source).resolve()
        self.compiler = Path(compiler).resolve()
        self.program = json.loads(self.source.read_bytes())['program']
        self.functions = {f['name']: f for f in self.program['functions']}
        self.cache = {}
        self.calls = 0

    def __call__(self, name, arguments):
        if name not in self.functions:
            return None
        function = self.functions[name]
        if len(arguments) != len(function['params']):
            return None
        try:
            values = [argument_value(t, x, self.program)
                      for (_, t), x in zip(function['params'], arguments)]
        except (ValueError, KeyError, TypeError):
            return None
        key = json.dumps([name, values], sort_keys=True, separators=(',', ':'))
        if key in self.cache:
            return self.cache[key]
        if self.calls >= self.MAX_CALLS or len(key.encode()) > self.MAX_BYTES:
            return None
        self.calls += 1
        result = None
        try:
            with tempfile.TemporaryDirectory(prefix='ink-closed-call-') as temporary:
                args = Path(temporary)/'arguments.json'
                args.write_text(json.dumps(values))
                checked = subprocess.run([str(self.compiler), 'run', str(self.source), name,
                                          str(args), '--core', '--input-receipt'],
                                         capture_output=True, timeout=30)
            if checked.returncode == 0 and len(checked.stdout) <= self.MAX_BYTES:
                receipt = json.loads(checked.stdout)
                if (receipt['semantics'] == 'ink-reference-call-v1'
                        and receipt['function'] == name
                        and receipt['input_core_sha256'] == receipt['selected_core_sha256']):
                    result = literal(function['result'], receipt['value'], self.program)
        except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired):
            pass
        # This cache saves authoring work only. It never supplies a proof or a
        # runtime retained result; every candidate still needs complete replay.
        self.cache[key] = result
        return result
