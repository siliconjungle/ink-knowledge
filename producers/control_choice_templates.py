"""Reusable lazy-choice simplifications authored from development control flow.

Only ordinary concrete Cases/Normalize proofs grant authority. Templates and
names propose matches; neither compilation budgets nor timing are proof facts.
"""
from ink_knowledge import entry,identity,semantic_entry,Store
from ink_knowledge.law_templates import SEMANTICS,substitute_types
from producers.semantic_laws import value,var,op,law


def templates():
    carrier=value({'Named':'$A'});boolean=value('Bool')
    a,b,e=[var(carrier,n) for n in ('a','b','e')];c,d=[var(boolean,n) for n in ('c','d')]
    choose=lambda p,x,y:op(carrier,'call:choose',p,x,y)
    cases=lambda p,body='Normalize':{'Cases':dict(condition=p,on_false=body,on_true=body)}
    rows=[('repeated-left',{'a':carrier,'b':carrier,'e':carrier,'c':boolean},choose(c,choose(c,a,b),e),choose(c,a,e),cases(c)),
          ('repeated-right',{'a':carrier,'b':carrier,'e':carrier,'c':boolean},choose(c,a,choose(c,b,e)),choose(c,a,e),cases(c)),
          ('same-branches',{'a':carrier,'c':boolean},choose(c,a,a),a,cases(c)),
          ('shared-inner-choice',{'a':carrier,'b':carrier,'e':carrier,'c':boolean,'d':boolean},choose(c,choose(d,a,b),choose(d,a,e)),choose(d,a,choose(c,b,e)),cases(c,cases(d)))]
    return [dict(name=n,object=entry('definition',SEMANTICS,dict(type_parameters=['A'],law=law(params,src,dst,proof),dependencies={}))) for n,params,src,dst,proof in rows]


def concrete():
    return [(row['name']+'/'+str(t),semantic_entry(substitute_types(row['object']['payload']['law'],{'A':t})))
            for row in templates() for t in ['U32','I32','F32','Bool','String',{'List':'U32'}]]


def publish(root):
    rows=templates();instances=concrete()
    objects=[r['object'] for r in rows]+[o for _,o in instances]
    names={'real-software-control/'+r['name']:identity(r['object']) for r in rows}
    names.update({'real-software-control/instance/'+n:identity(o) for n,o in instances})
    return Store(root).extend(objects,names)
