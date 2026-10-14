"""Materialise only requested proof closures, never unused discovery catalogues."""
from pathlib import Path
from .store import Store,identity,MAX_VIEW_ENTRIES,MAX_VIEW_BYTES,canonical
class ProposalViews:
    def __init__(self,source,objects,directory):
        self.source,self.objects,self.directory=source,objects,Path(directory)
        self.views={};self.bytes=0
        # One stable membership tree supports incremental kernel admissions.
        # This is an ephemeral partial transport, not a durable object store.
        # Unused discovery bodies are never copied or treated as admitted laws.
        # Reused laws need membership in this transport snapshot as well as
        # their bytes. A closure may mix newly authored and published objects.
        identities=set(objects);pending=[dep for obj in objects.values()for dep in obj['dependencies']]
        while pending:
            ident=pending.pop()
            if ident in identities:continue
            obj=self.source.object(ident);identities.add(ident);pending.extend(obj['dependencies'])
        self.transport=Store._publish_ids(self.directory,identities,{},64)
        self.members=self.transport.members()
    def update(self,extra):
        """Extend proposal transport; every new closure still needs kernel admission."""
        changed=False
        for ident,obj in extra.items():
            if identity(obj)!=ident:raise ValueError('proposal object content mismatch')
            if ident not in self.objects:self.objects[ident]=obj;changed=True
        if changed:
            self.transport=Store._publish_ids(self.directory,self.objects.keys(),{},64)
            self.members=self.transport.members()
            self.views.clear();self.bytes=0
    def bundle(self,roots):
        roots=tuple(sorted(set(roots)))
        if roots in self.views:return self.views[roots]
        objects={};active=set();size=0
        def visit(ident,depth):
            nonlocal size
            if ident in objects:return
            if ident in active or depth>64 or len(objects)+len(active)>=MAX_VIEW_ENTRIES:raise ValueError('proposal dependency closure budget/cycle')
            active.add(ident)
            obj=self.objects.get(ident)
            if obj is None:obj=self.source.object(ident)
            if identity(obj)!=ident:raise ValueError('proposal object content mismatch')
            size+=len(canonical(obj))
            if size>MAX_VIEW_BYTES:raise ValueError('proposal dependency byte budget')
            for dep in obj['dependencies']:visit(dep,depth+1)
            active.remove(ident);objects[ident]=obj
        for ident in roots:visit(ident,0)
        view=dict(schema=1,snapshot=self.transport.snapshot,roots=list(roots),objects=dict(sorted(objects.items())),membership={ident:self.members[ident]for ident in sorted(objects)})
        # Bounded hint cache. Eviction changes acquisition cost, not admission.
        if len(self.views)>=64:self.views.clear();self.bytes=0
        n=len(canonical(view))
        if self.bytes+n<=MAX_VIEW_BYTES:self.views[roots]=view;self.bytes+=n
        return view
