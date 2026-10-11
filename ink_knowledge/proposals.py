"""Installed database producer discovery. This module grants no proof authority."""
import hashlib,importlib,json
from importlib.resources import files
from pathlib import Path
from .store import semantic_entry,identity

def generate(subject,core):
    catalog=json.loads(files('ink_knowledge').joinpath('producer-catalog.json').read_text())
    if catalog.get('schema')!=1 or len(catalog.get('modules',[]))>64:raise ValueError('producer catalog limit')
    objects={};receipts=[]
    for name in catalog['modules']:
        module=importlib.import_module(name)
        rows=module.specialize(subject,core)
        if len(rows)>256:raise ValueError('producer candidate limit')
        for label,proposal in rows:
            from producers.definition_context28 import bind,calls
            names={f['name']for f in core['program']['functions']}
            if 'definition_context' not in proposal and (calls(proposal,names) or nominal_types(proposal)):
                proposal=bind(proposal,core,subject)
            obj=semantic_entry(proposal);objects[identity(obj)]=obj
        receipts.append(dict(module=name,source_sha256=hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest(),candidates=len(rows)))
    return objects,receipts

def nominal_types(value):
    """Named carrier sorts need their explicit portable declaration context."""
    if isinstance(value,dict):
        return 'Named' in value or any(nominal_types(v) for v in value.values())
    return isinstance(value,list) and any(nominal_types(v) for v in value)
