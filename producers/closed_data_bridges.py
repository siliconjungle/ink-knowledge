"""Untrusted, factored equality proposals for transparent closed data.

Fingerprints only find candidates. Every bridge is an ordinary closed theorem
over the exact source definitions, checked again with the complete selection.
"""
import json

from ink_knowledge import identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH, call, convert, trans, var
from producers.point_delta import binding_names, free_variables, lift, normal


class ClosedDataBridges:
    MAX_WORK = 100_000
    MAX_FUNCTIONS = 256

    def __init__(self, objects):
        self.objects = dict(objects)
        objects = self.objects
        self.aliases = {}
        self.lemmas = set()
        self.work = 0
        candidates = {}
        for name, obj in list(objects.items()):
            function = obj['payload'].get('declaration', {}).get('Function')
            if (function and not function['params'] and function['recursive'] is None
                    and isinstance(function['result'], dict) and 'Data' in function['result']):
                candidates[name] = function
        self.opaque = set(candidates)
        if len(candidates) > self.MAX_FUNCTIONS:
            return
        pending = {}
        for name, function in candidates.items():
            references = self.literal_calls(function['body'])
            if references is not None and references <= self.opaque:
                pending[name] = (function, references)
        done, representatives = set(), {}
        while pending:
            ready = sorted(name for name, (_, refs) in pending.items() if refs <= done)
            if not ready:
                break  # Nonliteral dependencies/cycles are not opportunities.
            for name in ready:
                function, _ = pending.pop(name)
                body, steps = self.rewrite(function['body'])
                normalized = normal(body, objects, opaque=self.opaque)
                proof = trans(convert(call(name, []), function['body']), *steps,
                              convert(body, normalized))
                key = json.dumps([function['result'], normalized], sort_keys=True, separators=(',', ':'))
                if key in representatives:
                    target, target_proof = representatives[key]
                    bridge = trans(proof, {'Sym': target_proof})
                    declaration = {'Theorem': dict(params=[], conditions=[],
                        **{'from': call(name, []), 'to': call(target, [])}, proof=bridge)}
                    deps = self.references(declaration)
                    obj = entry('theorem', MATH, {'declaration': declaration}, deps)
                    theorem = identity(obj)
                    objects[theorem] = obj
                    self.aliases[name] = (target, theorem)
                    self.lemmas.add(theorem)
                else:
                    representatives[key] = (name, proof)
                done.add(name)

    def tick(self):
        self.work += 1
        if self.work > self.MAX_WORK:
            raise ValueError('closed data bridge work budget')

    def literal_calls(self, term):
        """Accept only explicit constructor/primitive syntax with no binders."""
        pending = [term]
        calls = set()
        while pending:
            self.tick()
            term = pending.pop()
            if not isinstance(term, dict) or len(term) != 1:
                return None
            if 'U64' in term or 'Bool' in term:
                continue
            if 'Construct' in term:
                pending.extend(term['Construct']['arguments'])
            elif 'Binary' in term:
                pending.extend([term['Binary']['left'], term['Binary']['right']])
            elif 'Call' in term and not term['Call']['arguments']:
                calls.add(term['Call']['function'])
            else:
                return None
        return calls

    def references(self, value):
        pending, found = [value], set()
        while pending:
            self.tick()
            item = pending.pop()
            if isinstance(item, dict):
                for key in ['Data', 'datatype', 'function', 'theorem']:
                    name = item.get(key)
                    if isinstance(name, str) and name in self.objects:
                        found.add(name)
                pending.extend(item.values())
            elif isinstance(item, list):
                pending.extend(item)
        return found

    def rewrite(self, term, avoid=()):
        """Return a term plus checked-congruence proposals from its old form."""
        if not self.aliases:
            return term, []
        aliases = sorted(self.references(term) & self.aliases.keys())
        if not aliases:
            return term, []
        occupied = free_variables(term) | binding_names(term) | set(avoid)
        serial = 0
        while 'closed_data_hole_'+str(serial) in occupied:
            serial += 1
        hole = 'closed_data_hole_'+str(serial)
        steps = []
        for name in aliases:
            self.tick()
            target, theorem = self.aliases[name]
            source, selected = call(name, []), call(target, [])
            context = self.replace(term, source, var(hole))
            if context == term:
                continue
            steps.append(lift({'Use':dict(theorem=theorem,arguments=[],premises=[])}, context, hole))
            term = self.replace(term, source, selected)
        return term, steps

    def replace(self, term, source, selected):
        self.tick()
        if term == source:
            return selected
        if isinstance(term, dict):
            return {key:self.replace(value,source,selected) for key,value in term.items()}
        if isinstance(term, list):
            return [self.replace(value,source,selected) for value in term]
        return term
