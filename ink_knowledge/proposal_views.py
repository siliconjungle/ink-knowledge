"""Materialise only requested proof closures, never unused discovery catalogues."""
from pathlib import Path
import hashlib
from .store import Store,identity,MAX_VIEW_ENTRIES,MAX_VIEW_BYTES,MAX_ENTRY_BYTES,canonical,_publication_lock
class ProposalViews:
    def __init__(self,source,objects,directory):
        self.source,self.objects,self.directory=source,objects,Path(directory)
        self.views={};self.bytes=0
        # One stable membership tree supports incremental kernel admissions.
        # This is an ephemeral partial transport, not a durable object store.
        # Unused discovery bodies are never copied or treated as admitted laws.
        # Reused laws need membership in this transport snapshot as well as
        # their bytes. A closure may mix newly authored and published objects.
        self._refresh_transport()
    def _refresh_transport(self):
        identities=set(self.objects);pending=[dep for obj in self.objects.values()for dep in obj['dependencies']]
        while pending:
            ident=pending.pop()
            if ident in identities:continue
            obj=self.source.object(ident);identities.add(ident);pending.extend(obj['dependencies'])
        with _publication_lock(self.directory):
            # Keep ordinary discovery cheap. Compact membership is built lazily
            # only when a requested packet approaches existing transport limits.
            self.transport=Store._publish_ids(self.directory,identities,{},64)
        self.members=self.transport.members()
        self.identities=identities
        self.compact=None
    def update(self,extra):
        """Extend proposal transport; every new closure still needs kernel admission."""
        changed=False
        for ident,obj in extra.items():
            if identity(obj)!=ident:raise ValueError('proposal object content mismatch')
            if ident not in self.objects:self.objects[ident]=obj;changed=True
        if changed:
            # The new membership tree must include the transitive external
            # dependencies of both previous and newly discovered proposals.
            self._refresh_transport()
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
            # Objects sit two levels below a view root. Preserve that canonical
            # depth budget while hashing and sizing the exact inner bytes once.
            encoded=canonical([[obj]])
            body=memoryview(encoded)[2:-2]
            if hashlib.sha256(body).hexdigest()!=ident:raise ValueError('proposal object content mismatch')
            size+=len(body)
            body.release()
            del encoded
            if size>MAX_VIEW_BYTES:raise ValueError('proposal dependency byte budget')
            for dep in obj['dependencies']:visit(dep,depth+1)
            active.remove(ident);objects[ident]=obj
        for ident in roots:visit(ident,0)
        view=dict(schema=1,snapshot=self.transport.snapshot,roots=list(roots),objects=dict(sorted(objects.items())),membership={ident:self.members[ident]for ident in sorted(objects)})
        # Bounded hint cache. Eviction changes acquisition cost, not admission.
        if len(self.views)>=64:self.views.clear();self.bytes=0
        def view_bytes(packet):
            # Replacing each object by null preserves every outer key, comma
            # and wrapper. Its already authenticated encoding supplies the rest.
            metadata=dict(packet,objects=dict.fromkeys(objects))
            return size+len(canonical(metadata))-4*len(objects)
        n=view_bytes(view)
        if n>=MAX_ENTRY_BYTES*15//16:
            if self.compact is None:
                with _publication_lock(self.directory/'compact'):
                    self.compact=Store._publish_ids(self.directory/'compact',self.identities,{},2)
            members=self.compact.members()
            alternative=dict(view,snapshot=self.compact.snapshot,membership={i:members[i]for i in sorted(objects)})
            compact_bytes=view_bytes(alternative)
            if compact_bytes<n:view,n=alternative,compact_bytes
        if self.bytes+n<=MAX_VIEW_BYTES:self.views[roots]=view;self.bytes+=n
        return view
