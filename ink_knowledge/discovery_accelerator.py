"""Disposable exact-result accelerators; no membership/proof authority.

Bloom negatives avoid discovery work. Learned positions are only hints: a local
search result is checked against global sorted neighbors and falls back to bisect.
Thus even a stale/inaccurate model cannot return an incorrect lower bound.
"""
import bisect
import hashlib
import json
from pathlib import Path


class Bloom:
    def __init__(self, keys, bits_per_key=12):
        if not 2<=bits_per_key<=64:raise ValueError('Bloom size')
        self.bits=max(64,len(keys)*bits_per_key);self.words=bytearray((self.bits+7)//8)
        for key in keys:
            for bit in self.positions(key):self.words[bit//8]|=1<<(bit%8)
    def positions(self,key):
        digest=hashlib.blake2b(str(key).encode(),digest_size=16).digest()
        a=int.from_bytes(digest[:8],'little');b=int.from_bytes(digest[8:],'little')|1
        return [(a+i*b)%self.bits for i in range(7)]
    def maybe(self,key):return all(self.words[b//8]&(1<<(b%8)) for b in self.positions(key))


class LearnedIndex:
    def __init__(self, keys, block_size=128):
        if not 2<=block_size<=4096:raise ValueError('learned block size')
        if any(type(x) is not int for x in keys) or list(keys)!=sorted(keys):raise ValueError('sorted integer keys required')
        self.keys=tuple(keys);self.segments=[];self.ends=[];self.fallbacks=0
        for start in range(0,len(keys),block_size):
            end=min(len(keys),start+block_size)-1;lo,hi=keys[start],keys[end]
            predict=lambda x:start+(x-lo)*(end-start)//max(1,hi-lo)
            error=max(abs(predict(keys[i])-i) for i in range(start,end+1))
            self.segments.append((start,end,lo,hi,error));self.ends.append(hi)
    def lower_bound(self,key):
        if type(key) is not int:raise ValueError('integer query')
        if not self.keys:return 0
        try:
            segment=min(bisect.bisect_left(self.ends,key),len(self.segments)-1)
            start,end,lo,hi,error=self.segments[segment]
            predicted=start+(key-lo)*(end-start)//max(1,hi-lo)
            left=max(0,min(len(self.keys),predicted-error-2));right=max(left,min(len(self.keys),predicted+error+3))
            position=bisect.bisect_left(self.keys,key,left,right)
            if (position==0 or self.keys[position-1]<key) and (position==len(self.keys) or self.keys[position]>=key):return position
        except (ArithmeticError,IndexError,TypeError,ValueError):pass
        self.fallbacks+=1;return bisect.bisect_left(self.keys,key)


class DiscoveryAccelerator:
    def __init__(self, store, block_size=128):
        self.snapshot=store.snapshot_id;self.rows=[];buckets={}
        # Exact pinned bytes supply this in-memory derived index. Every object
        # still authenticates independently on retrieval and proof export.
        for ident in sorted(store.members()):
            obj=store.object(ident);iface=obj['interface'];tokens=[]
            for name,value in [('kind',obj['kind']),('semantics',obj['semantics']),('result',iface['result'])]:tokens.append((name,json.dumps(value,sort_keys=True,separators=(',',':'))))
            for name,values in [('operation',iface['operations']),('effect',iface['effects']),('parameter_type',iface['parameters'].values()),('condition',iface['conditions'])]:
                tokens.extend((name,json.dumps(value,sort_keys=True,separators=(',',':'))) for value in values)
            self.rows.append(ident)
            for token in set(tokens):buckets.setdefault(token,[]).append(ident)
        self._buckets={k:tuple(v) for k,v in buckets.items()};self._bloom=Bloom(list(buckets))
        self.ids=tuple(self.rows);self._positions=LearnedIndex([int(i,16) for i in self.ids],block_size)
    def query(self, *, after=None, limit=1024, **filters):
        if type(limit) is not int or not 0<=limit<=1024:raise ValueError('discovery query limit')
        allowed={'kind','semantics','operation','result','effect','parameter_type','condition'}
        if set(filters)-allowed:raise ValueError('discovery query fields')
        if after is not None:
            from .store import hash_id
            hash_id(after)
        if limit==0:return []
        candidates=None
        for name,value in filters.items():
            if value is None:continue
            token=(name,json.dumps(value,sort_keys=True,separators=(',',':')))
            if not self._bloom.maybe(token):return []
            values=self._buckets.get(token,())
            candidates=set(values) if candidates is None else candidates.intersection(values)
            if not candidates:return []
        if candidates is None:
            start=0 if after is None else self._positions.lower_bound(int(after,16)+1)
            return list(self.ids[start:start+limit])
        return [i for i in sorted(candidates) if after is None or i>after][:limit]


def enable(store, block_size=128):
    accelerator=DiscoveryAccelerator(store,block_size)
    store._discovery_accelerator=accelerator
    return accelerator
