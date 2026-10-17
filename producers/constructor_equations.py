"""Untrusted constructor/Boolean-step authoring; the kernel computes conclusions.

Exact selector steps retain their fixed datatype meaning and lexical scopes.
No cached producer result supplies equality authority.
"""
from producers.equational import fresh_alpha
from producers.point_delta import free_variables, sub


class ConstructorEquations:
    def __init__(self, chunks):
        self.chunks = chunks

    def beta(self, term, env):
        self.chunks.tick()
        term = fresh_alpha(term, {name: name for name in env})
        node = term['Match']; constructor = node['scrutinee']['Construct']
        datatype, index = constructor['datatype'], constructor['constructor']
        fields = self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors'][index]['fields']
        branch = node['branches'][index]
        if len(fields) != len(constructor['arguments']) or len(fields) != len(branch['bindings']):
            raise ValueError('constructor equation arity')
        body = fresh_alpha(sub(branch['body'], dict(zip(branch['bindings'], constructor['arguments']))),
                           {name: name for name in env})
        return body, {'Step': term}

    def factor(self, proof, env):
        """Replace exact beta steps only in scopes whose variables are typed.

        Constructor/induction branches introduce other locals. Their enclosing
        author retains those proofs rather than guessing their environments.
        Conclusions are computed by the kernel from the supplied redex.
        """
        self.chunks.tick()
        if 'Convert' in proof:
            equation = proof['Convert']; left = equation['from']
            if 'If' in left and 'Bool' in left['If']['condition']:
                if not free_variables([left, equation['to']]) <= env.keys():
                    return proof
                names = {name: name for name in env}
                term = fresh_alpha(left, names)
                node = term['If']
                body = fresh_alpha(node['on_true' if node['condition']['Bool'] else 'on_false'], names)
                target = fresh_alpha(equation['to'], names)
                return {'Step': term} if body == target else proof
            if 'Match' not in left or 'Construct' not in left['Match']['scrutinee']:
                return proof
            if not free_variables([left, equation['to']]) <= env.keys():
                return proof
            body, witness = self.beta(left, env)
            target = fresh_alpha(equation['to'], {name: name for name in env})
            return witness if body == target else proof
        if 'Trans' in proof:
            old = proof['Trans']; children = [self.factor(child, env) for child in old]
            return proof if all(a is b for a, b in zip(old, children)) else {'Trans': children}
        if 'Sym' in proof:
            child = self.factor(proof['Sym'], env)
            return proof if child is proof['Sym'] else {'Sym': child}
        if 'Substitute' in proof:
            node = proof['Substitute']; child = self.factor(node['equality'], env)
            return proof if child is node['equality'] else {'Substitute': dict(node, equality=child)}
        if 'Call' in proof or 'Construct' in proof:
            kind = 'Call' if 'Call' in proof else 'Construct'; node = proof[kind]
            children = [self.factor(child, env) for child in node['arguments']]
            return proof if all(a is b for a, b in zip(node['arguments'], children)) else {kind: dict(node, arguments=children)}
        if 'Binary' in proof:
            node = proof['Binary']; first = self.factor(node['left'], env); second = self.factor(node['right'], env)
            return proof if first is node['left'] and second is node['right'] else {'Binary': dict(node, left=first, right=second)}
        return proof
