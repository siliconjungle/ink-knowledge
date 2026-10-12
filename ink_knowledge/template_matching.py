"""Bounded structural discovery for parametric database templates.

Index only operation heads, never theorem names or program identities. Every
candidate still goes through full type inference and binder-aware matching,
then independent kernel replay. Immutable subject terms are borrowed here.
"""
from .pattern_index import shape

class TemplateSites:
    def __init__(self,subject,node_limit=200_000,attempt_limit=200_000):
        from ink_planner.semantic_search import positions
        self.sites=[];self.by_head={};self.limit=attempt_limit;self.attempts=0
        for name,body in subject['functions'].items():
            for path,target in positions(body):
                if len(self.sites)>=node_limit:raise ValueError('template subject node budget')
                site=(name,path,target);self.sites.append(site)
                self.by_head.setdefault(shape(target),[]).append(site)
    def matches(self,pattern,params,type_parameters):
        from .law_templates import infer
        head=shape(pattern,params)
        for name,path,target in self.sites if head=='*'else self.by_head.get(head,()):
            self.attempts+=1
            if self.attempts>self.limit:raise ValueError('template inference budget')
            bindings={}
            if infer(pattern,target,params,type_parameters,bindings)and set(bindings)==set(type_parameters):
                yield name,path,target,bindings
