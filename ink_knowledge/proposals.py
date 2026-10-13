"""Installed database producer discovery. This module grants no proof authority."""
import hashlib,importlib,json,re
from importlib.resources import files
from pathlib import Path
from .store import semantic_entry,identity

SEMANTICS='ink-semantic-producers-v1'
MODULE=re.compile(r'producers(?:\.[a-z][a-z0-9_]*)+')

def modules(store=None):
    catalog=json.loads(files('ink_knowledge').joinpath('producer-catalog.json').read_text())
    if set(catalog)!={'schema','modules'} or catalog['schema']!=1:raise ValueError('producer catalog schema')
    names=list(catalog['modules']);publications=[]
    if store is not None:
        after=None
        while True:
            page=store.query(kind='definition',semantics=SEMANTICS,after=after,limit=64)
            for ident in page:
                payload=store.object(ident)['payload']
                if set(payload)!={'module'}:raise ValueError('published semantic producer fields')
                names.append(payload['module']);publications.append(ident)
            if len(page)<64:break
            after=page[-1]
            if len(names)>64:raise ValueError('producer catalog limit')
    if len(names)>64 or any(not isinstance(n,str) or not MODULE.fullmatch(n) for n in names):raise ValueError('producer catalog limit or module')
    return list(dict.fromkeys(names)),publications

def retarget(value,renamed):
    """Follow identities that changed when an earlier row was context-bound.

    A producer may emit a supporting law and later rows that `Use` it by its
    unbound identity. Binding a definition context changes that identity, so
    dependency lists and proof references are rewritten to the bound entry.
    Unknown identities are left alone; the kernel still checks every closure.
    """
    if not renamed:return value
    if isinstance(value,dict):
        out={}
        for k,v in value.items():
            if k=='law' and isinstance(v,str):out[k]=renamed.get(v,v)
            elif k=='dependencies' and isinstance(v,list):out[k]=sorted({renamed.get(d,d) if isinstance(d,str) else d for d in v})
            else:out[k]=retarget(v,renamed)
        return out
    if isinstance(value,list):return [retarget(v,renamed) for v in value]
    return value

def generate(subject,core,store=None,compiler=None):
    names,publications=modules(store)
    objects={};receipts=[]
    for name in names:
        module=importlib.import_module(name)
        rows=module.specialize(subject,core)
        if len(rows)>256:raise ValueError('producer candidate limit')
        renamed={}
        for label,proposal in rows:
            from producers.definition_context28 import bind,calls
            names={f['name']for f in core['program']['functions']}
            original=identity(semantic_entry(proposal))
            proposal=retarget(proposal,renamed)
            if 'definition_context' not in proposal and (calls(proposal,names) or nominal_types(proposal)):
                proposal=bind(proposal,core,subject)
            obj=semantic_entry(proposal);ident=identity(obj);objects[ident]=obj
            if ident!=original:renamed[original]=ident
        receipts.append(dict(module=name,source_sha256=hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest(),candidates=len(rows),publication_ids=publications,retargeted=len(renamed)))
    if store is not None:
        from .law_templates import generate as instantiate
        extra,templates=instantiate(store,subject,core);objects.update(extra);receipts.extend(templates)
        # Structure laws reach a program only through concrete instances whose
        # assumptions the compiler has checked for this module.
        from .structure_instances import generate as structures
        extra,receipt=structures(store,subject,core,compiler);objects.update(extra);receipts.append(receipt)
    return objects,receipts

def nominal_types(value):
    """Named carrier sorts need their explicit portable declaration context."""
    if isinstance(value,dict):
        return 'Named' in value or any(nominal_types(v) for v in value.values())
    return isinstance(value,list) and any(nominal_types(v) for v in value)
