"""Bounded structural discovery; full inference and kernel replay remain authoritative."""
from .pattern_index import shape
from .store import canonical

def constraints(term,params=(),depth=0,path=()):
    """Necessary structural, concrete-sort and leaf constraints for Miller matching.

    Applied holes can absorb arbitrary subtrees, so traversal stops at them.
    Paths are relative to one site; constraints never mix different sites.
    """
    from .higher_patterns import applied_hole
    if depth>4 or applied_hole(term,params):return {}
    head=shape(term,params)
    if head=='*':return {}
    result={(path,'head'):head}
    def generic(v):
        if isinstance(v,dict):
            return any(k=='Named'and isinstance(x,str)and x.startswith('$')or generic(x)for k,x in v.items())
        return isinstance(v,list)and any(generic(x)for x in v)
    if not generic(term['sort']):result[path,'sort']=canonical(term['sort'])
    node=term['node']
    if isinstance(node,dict)and 'Op'in node:
        for n,child in enumerate(node['Op'][1]):result.update(constraints(child,params,depth+1,path+(n,)))
    elif isinstance(node,dict)and 'Lambda'in node:
        result.update(constraints(node['Lambda'],params,depth+1,path+(0,)))
    else:
        from ink_planner.semantic_search import children
        if not children(term):result[path,'leaf']=canonical(node)
    return result

class TemplateSites:
    def __init__(self,subject,node_limit=200_000,attempt_limit=200_000,token_limit=2_000_000):
        from ink_planner.semantic_search import positions
        self.sites=[];self.by_head={};self.limit=attempt_limit;self.attempts=0
        self.postings={};self.token_count=0;self.token_limit=token_limit
        self.originals={};self.head_reductions=0;self.head_reduction_declines=0
        reduction_budget=[node_limit]
        for name,body in subject['functions'].items():
            for path,target in positions(body):
                if len(self.sites)>=node_limit:raise ValueError('template subject node budget')
                at=len(self.sites);self.sites.append((name,path,target))
                self.by_head.setdefault(shape(target),[]).append(at)
        # Preserve the complete original index and its ordering before adding
        # optional search aliases. Exhaustion cannot discard literal sites.
        originals=len(self.sites)
        for at in range(originals):
            name,path,target=self.sites[at];node=target['node']
            if not isinstance(node,dict)or node.get('Op',[None])[0]!='apply':continue
            if len(self.sites)>=node_limit or reduction_budget[0]<=0:
                self.head_reduction_declines+=1;continue
            from .head_beta import reduce,contexts
            try:
                normal=reduce(target,reduction_budget)
                if normal is not target:
                    self.head_reductions+=1
                    for _,inner in contexts(normal,reduction_budget):
                        if len(self.sites)>=node_limit:raise ValueError('template alias budget')
                        alias=len(self.sites);self.sites.append((name,path,inner));self.originals[alias]=target
                        self.by_head.setdefault(shape(inner),[]).append(alias)
            except (ValueError,RecursionError):
                self.head_reduction_declines+=1;continue

    def matching_sites(self,pattern,params):
        from .higher_patterns import applied_hole
        head='*' if applied_hole(pattern,params)else shape(pattern,params)
        if head=='*':return range(len(self.sites))
        if head not in self.by_head:return ()
        # Small buckets are cheaper to match directly than to index. This is
        # a scheduling choice: it retains every candidate and the same checks.
        if len(self.by_head[head])<32:return self.by_head[head]
        if head not in self.postings:
            index={}
            for at in self.by_head[head]:
                for (path,kind),token in constraints(self.sites[at][2]).items():
                    self.token_count+=1
                    if self.token_count>self.token_limit:raise ValueError('template structural token budget')
                    index.setdefault((path,kind,token),set()).add(at)
            self.postings[head]=index
        index=self.postings[head]
        required=[index.get((path,kind,token),set())for (path,kind),token in constraints(pattern,params).items()]
        required.sort(key=len)
        if not required:return self.by_head[head]
        found=required[0].copy()
        for posting in required[1:]:
            found.intersection_update(posting)
            if not found:break
        return sorted(found)
    def matches(self,pattern,params,type_parameters):
        from .law_templates import infer
        seen=set()
        for at in self.matching_sites(pattern,params):
            name,path,target=self.sites[at]
            self.attempts+=1
            if self.attempts>self.limit:raise ValueError('template inference budget')
            bindings={}
            if infer(pattern,target,params,type_parameters,bindings)and set(bindings)==set(type_parameters):
                # Several inner views may instantiate the same law for one
                # original endpoint. The adapter deterministically lifts its
                # first match; do not consume proposal slots with duplicates.
                key=(name,tuple(path),canonical(bindings))
                if key in seen:continue
                seen.add(key)
                yield name,path,self.originals.get(at,target),bindings
