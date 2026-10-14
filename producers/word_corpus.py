"""Seeded small Ink programs for offline compiler comparison and discovery.

Generation does not look at LLVM output or proof results. Programs and seeds are
saved before discovery so unsupported cases and failed proofs remain observable.
"""
import random


def generate(seed=0, count=32, depth=4):
    if not 1 <= count <= 256 or not 1 <= depth <= 6:
        raise ValueError('word corpus bounds: 1..256 programs, depth 1..6')
    rng = random.Random(seed)
    functions = []
    for i in range(count):
        kind = 'u32' if i % 2 == 0 else 'u64'
        width = 32 if kind == 'u32' else 64
        atoms = ['x', 'y', '0', '1', '3', '7', '255', str((1 << width)-1)]
        def expression(level):
            if level == 0 or rng.randrange(4) == 0:
                return rng.choice(atoms)
            operation = rng.choice(['+', '-', '*', '&', '|', '^', 'word_not', 'shift'])
            left = expression(level-1)
            if operation == 'word_not':
                return f'word_not({left})'
            if operation == 'shift':
                return f"{rng.choice(['wrapping_shl','wrapping_shr'])}({left},{rng.choice([0,1,width-1,width,width+1])})"
            right = left if rng.randrange(5) == 0 else expression(level-1)
            return f'({left} {operation} {right})'
        body = expression(depth)
        name = f'generated_{i:03d}'
        functions.append(dict(name=name, kind=kind, expression=body))
    source = 'module generated_word_corpus;\n' + '\n'.join(
        f"fn {f['name']}(x:{f['kind']},y:{f['kind']})->{f['kind']}{{return {f['expression']};}}"
        for f in functions) + '\n'
    return source, dict(seed=seed,count=count,depth=depth,functions=functions)
