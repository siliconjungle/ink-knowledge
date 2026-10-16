"""Untrusted known-bit and unsigned-range analysis for offline law discovery.

Facts are suggestions, never core assumptions. Every generated replacement must
still carry an independently checked equality proof. Unknown operations lose
information; wrapping arithmetic never inherits LLVM's nowrap assumptions.
"""
from dataclasses import dataclass
from .semantic_laws import value, word, term, op


_WORD_ROUNDTRIPS = {
    'call:word_narrow_u64_to_u32': ('call:word_widen_u32_to_u64', 'U32', (1 << 32) - 1),
    'call:word_widen_u32_to_u64': ('call:word_narrow_u64_to_u32', 'U64', (1 << 32) - 1),
}


@dataclass(frozen=True)
class Facts:
    width: int
    zero: int = 0
    one: int = 0
    minimum: int = 0
    maximum: int | None = None
    excludes: int | None = None

    def __post_init__(self):
        if self.width not in (1, 32, 64):
            raise ValueError('Unsupported word fact width')
        mask = (1 << self.width) - 1
        maximum = mask if self.maximum is None else self.maximum
        if self.width not in (1, 32, 64) or (self.zero | self.one) & ~mask or self.zero & self.one:
            raise ValueError('Inconsistent word facts')
        lo, hi = max(self.minimum, self.one), min(maximum, mask ^ self.zero)
        excluded = self.excludes
        if excluded is not None and (type(excluded) is not int or not 0 <= excluded <= mask):
            raise ValueError('Excluded point outside word domain')
        # An excluded endpoint is expressible by the interval itself. Keep at
        # most one interior hole; losing another hole is conservative.
        if excluded == lo:lo += 1
        if excluded == hi:hi -= 1
        if not 0 <= lo <= hi <= mask:
            raise ValueError('Inconsistent unsigned range')
        # Every value in an unsigned interval shares the prefix above the
        # highest differing endpoint bit. This does not assume no overflow.
        prefix = mask ^ ((1 << (lo ^ hi).bit_length()) - 1)
        zero, one = self.zero | (prefix & ~lo), self.one | (prefix & lo)
        if zero & one:
            raise ValueError('Conflicting interval and known bits')
        object.__setattr__(self, 'zero', zero)
        object.__setattr__(self, 'one', one)
        object.__setattr__(self, 'minimum', lo)
        object.__setattr__(self, 'maximum', hi)
        # Retain an endpoint exclusion after tightening its range too: its
        # exact image remains useful through a wrapping bijection.
        object.__setattr__(self, 'excludes', excluded)

    @property
    def constant(self):
        return self.minimum if self.minimum == self.maximum else None


def constant(width, n):
    mask=(1<<width)-1;n &= mask
    return Facts(width, mask ^ n, n, n, n)


def trailing_ones(bits, width):
    return min(width, ((bits ^ (bits + 1)).bit_length() - 1))


def add_bits(a, b, carry_in=0):
    """Independent bit possibilities lose correlations conservatively."""
    zeros = ones = 0
    carry = {carry_in}
    for i in range(a.width):
        bit = 1 << i
        left = {1} if a.one & bit else {0} if a.zero & bit else {0, 1}
        right = {1} if b.one & bit else {0} if b.zero & bit else {0, 1}
        sums = {x + y + c for x in left for y in right for c in carry}
        digits, carry = {n & 1 for n in sums}, {n >> 1 for n in sums}
        if digits == {0}: zeros |= bit
        if digits == {1}: ones |= bit
    return zeros, ones


def refine(scope, condition, truth, budget=32, *, relational=True):
    """Untrusted branch-local constraints. No bindings or caller contracts cross here.

    Intersections describe simultaneous constraints; branch joins below instead
    union their possible values. Contradictory constraints are discarded rather
    than used to invent a value for an unreachable branch.
    """
    result = list(scope)
    remaining = budget
    def constrain(subject, fact):
        for index, (prior, old) in enumerate(result):
            if prior == subject:
                try:
                    hole = fact.excludes if fact.excludes is not None else old.excludes
                    result[index] = (subject, Facts(fact.width, old.zero | fact.zero,
                        old.one | fact.one, max(old.minimum, fact.minimum),
                        min(old.maximum, fact.maximum), hole))
                except ValueError:
                    pass
                return
        if len(result) < 64:
            result.append((subject, fact))
    def visit(t, answer):
        nonlocal remaining
        remaining -= 1
        if remaining < 0:
            return
        if t.get('sort') != value('Bool'):
            return
        constrain(t, constant(1, int(answer)))
        node = t['node']
        if 'Op' not in node:
            return
        name, args = node['Op']
        if name == 'unary:!' and len(args) == 1:
            visit(args[0], not answer)
        elif len(args) == 2 and ((name == 'binary:&&' and answer) or
                                 (name == 'binary:||' and not answer)):
            visit(args[0], answer); visit(args[1], answer)
        elif name in ('binary:==', 'binary:!=', 'binary:<', 'binary:<=', 'binary:>', 'binary:>=') and len(args) == 2:
            left, right = args
            if left['sort'] != right['sort']:
                return
            relation = name[7:]
            if 'Word' in left['node'] and 'Word' not in right['node']:
                left, right = right, left
                relation = {'<':'>', '<=':'>=', '>':'<', '>=':'<=', '==':'==', '!=':'!='}[relation]
            kind = left['sort'].get('Value')
            if kind not in ('U32', 'U64'):
                return
            width = 32 if kind == 'U32' else 64
            mask = (1 << width) - 1
            if not answer:
                relation = {'<':'>=', '<=':'>', '>':'<=', '>=':'<', '==':'!=', '!=':'=='}[relation]
            # Relational narrowing uses already established ranges, never the
            # assumption that wrapping expressions are monotone in their inputs.
            # Refining the expression's result is valid even if it is x + 1.
            if 'Word' not in right['node']:
                if not relational:return
                try:
                    a = analyse(left, max_nodes=512, _scope=tuple(result), _relational=False)
                    b = analyse(right, max_nodes=512, _scope=tuple(result), _relational=False)
                except ValueError:
                    return
                if relation in ('>','>='):
                    left,right,a,b = right,left,b,a
                    relation = '<' if relation == '>' else '<='
                if relation in ('<','<='):
                    strict = int(relation == '<')
                    if b.maximum >= strict:
                        constrain(left, Facts(width, maximum=b.maximum-strict))
                    if a.minimum + strict <= mask:
                        constrain(right, Facts(width, minimum=a.minimum+strict))
                elif relation == '==':
                    constrain(left, b);constrain(right, a)
                elif b.constant is not None:
                    constrain(left, Facts(width, excludes=b.constant))
                elif a.constant is not None:
                    constrain(right, Facts(width, excludes=a.constant))
                return
            n = right['node']['Word']
            if type(n) is not int or not 0 <= n <= mask:return
            lo, hi = 0, mask
            if relation == '==':lo = hi = n
            elif relation == '<':hi = n - 1
            elif relation == '<=':hi = n
            elif relation == '>':lo = n + 1
            elif relation == '>=':lo = n
            elif n == 0:
                constrain(left, Facts(width, excludes=0));return
            elif n == mask:
                constrain(left, Facts(width, excludes=mask));return
            else:
                constrain(left, Facts(width, excludes=n));return
            if 0 <= lo <= hi <= mask:
                constrain(left, Facts(width, minimum=lo, maximum=hi))
    # A second bounded pass lets x < y consume a later y <= 255 conjunct.
    # This is a discovery budget, not a fixed-point or completeness claim.
    visit(condition, truth)
    visit(condition, truth)
    return result


class _FactMemo:
    """Bounded records borrowed only during one synchronous discovery query.

    Strong references keep identity keys valid. Limits bound extra entries and
    scoped references; the conservative byte charge is not an RSS promise and
    excludes the input graph already held by the caller. No facts survive the
    query or an outward generator yield.
    """
    def __init__(self, *, max_entries=2048, max_cells=16384, max_charge=1048576):
        self.entries = {}
        self.cells = self.charge = 0
        self.max_entries = max_entries
        self.max_cells = max_cells
        self.max_charge = max_charge

    def clear(self):
        self.entries.clear()
        self.cells = self.charge = 0

    def put(self, key, facts, cost, height, node, scope):
        cells, charge = 1 + len(scope), 512 + 512 * len(scope)
        if (len(self.entries) >= self.max_entries or
                self.cells + cells > self.max_cells or
                self.charge + charge > self.max_charge):
            return
        self.entries[key] = (facts, cost, height, node, tuple(scope))
        self.cells += cells
        self.charge += charge


def analyse(source, max_nodes=4096, *, _scope=(), _memo=None, _relational=True):
    remaining = max_nodes
    peaks = []

    def cached(t, depth=0, scope=_scope):
        nonlocal remaining
        # Leaf facts are cheaper to calculate than to retain. Oversized caller
        # scopes also use ordinary bounded traversal without adding cache keys.
        if 'Op' not in t.get('node', {}) or len(scope) > 64:
            if peaks:
                peaks[-1] = max(peaks[-1], depth)
            return uncached(t, depth, scope)
        key = (id(t), _relational, tuple((id(subject), fact) for subject, fact in scope))
        found = _memo.entries.get(key)
        if found is not None:
            facts, cost, height, held_node, held_scope = found
            remaining -= cost
            if remaining < 0 or depth + height > 64:
                raise ValueError('Word fact analysis budget')
            if peaks:
                peaks[-1] = max(peaks[-1], depth + height)
            return facts
        before = remaining
        peaks.append(depth)
        try:
            facts = uncached(t, depth, scope)
        finally:
            peak = peaks.pop()
        if peaks:
            peaks[-1] = max(peaks[-1], peak)
        _memo.put(key, facts, before - remaining, peak - depth, t, scope)
        return facts

    def uncached(t, depth=0, scope=_scope):
        nonlocal remaining
        remaining-=1
        if remaining<0 or depth>64:
            raise ValueError('Word fact analysis budget')
        sort=t.get('sort',{});kind=sort.get('Value') if isinstance(sort,dict) else None
        if not isinstance(kind,str) or kind not in ('Bool','U32','U64'):
            raise ValueError('Word fact analysis supports unsigned words and Bool')
        width={'Bool':1,'U32':32,'U64':64}[kind];mask=(1<<width)-1
        node=t['node']
        for subject, fact in reversed(scope):
            if subject == t:
                return fact
        if 'Word' in node:return constant(width,node['Word'])
        if 'Bool' in node:return constant(1,int(node['Bool']))
        if 'Op' not in node:return Facts(width)
        name,args=node['Op']
        # Unsupported calls can contain other carriers or binders. Their values
        # remain unconstrained; neither contracts nor metadata become facts.
        names={'call:word_and','call:word_or','call:word_xor','call:word_not',
               'binary:+','binary:-','binary:*','binary:==','binary:!=','binary:<',
               'binary:<=','binary:>','binary:>=','call:choose','call:wrapping_shl',
               'call:wrapping_shr','call:word_widen_u32_to_u64','call:word_narrow_u64_to_u32',
               'binary:&&','binary:||','unary:!'}
        if name not in names:return Facts(width)
        if name=='call:choose' and len(args)==3:
            cond=visit(args[0],depth+1,scope)
            if cond.constant is not None:
                return visit(args[1 if cond.constant else 2],depth+1,scope)
            a=visit(args[1],depth+1,refine(scope,args[0],True,relational=_relational))
            b=visit(args[2],depth+1,refine(scope,args[0],False,relational=_relational))
            holes = [hole for hole in (a.excludes,b.excludes) if hole is not None]
            excludes = next((hole for hole in holes if all(
                hole < f.minimum or hole > f.maximum or hole == f.excludes
                or hole & f.zero or hole & f.one != f.one for f in (a,b))), None)
            return Facts(width,a.zero&b.zero,a.one&b.one,min(a.minimum,b.minimum),max(a.maximum,b.maximum),excludes)
        facts=[visit(a,depth+1,scope) for a in args]
        if len(facts)==1:
            a=facts[0]
            if name in ('call:word_not','unary:!'):return Facts(width,a.one,a.zero,mask-a.maximum,mask-a.minimum,None if a.excludes is None else mask^a.excludes)
            if name=='call:word_widen_u32_to_u64':return Facts(64,a.zero|(((1<<32)-1)<<32),a.one,a.minimum,a.maximum,a.excludes)
            if name=='call:word_narrow_u64_to_u32':
                return Facts(32,a.zero&mask,a.one&mask,a.minimum if a.maximum<=mask else 0,a.maximum if a.maximum<=mask else mask,a.excludes if a.maximum<=mask else None)
            return Facts(width)
        if len(facts)!=2:return Facts(width)
        a,b=facts
        same = args[0] == args[1]
        if same and name in ('binary:-','call:word_xor'):return constant(width,0)
        if same and name in ('binary:==','binary:!=','binary:<','binary:<=','binary:>','binary:>='):
            return constant(1,int(name in ('binary:==','binary:<=','binary:>=')))
        if name in ('call:word_and','binary:&&'):return Facts(width,a.zero|b.zero,a.one&b.one,0,min(a.maximum,b.maximum))
        if name in ('call:word_or','binary:||'):return Facts(width,a.zero&b.zero,a.one|b.one,max(a.minimum,b.minimum),mask)
        # Addition/subtraction and XOR with a constant are bijections modulo
        # 2^width. Their excluded-point transport remains valid across overflow.
        def excluded_image(operation):
            if b.constant is not None and a.excludes is not None:return operation(a.excludes,b.constant)&mask
            if a.constant is not None and b.excludes is not None:return operation(a.constant,b.excludes)&mask
            return None
        if name=='call:word_xor':return Facts(width,(a.zero&b.zero)|(a.one&b.one),(a.zero&b.one)|(a.one&b.zero),excludes=excluded_image(lambda x,y:x^y))
        if name in ('call:wrapping_shl','call:wrapping_shr'):
            # Ink masks oversized counts. Enumerate the at most 64 feasible
            # residues, including values LLVM would otherwise call poison.
            counts = ([b.constant % width] if b.constant is not None else
                      [n for n in range(width) if not n & b.zero and n & (b.one & (width-1)) == b.one & (width-1)])
            possibilities=[]
            for count in counts:
                if name.endswith('shl'):
                    possibilities.append(Facts(width,((a.zero<<count)|((1<<count)-1))&mask,(a.one<<count)&mask))
                else:
                    possibilities.append(Facts(width,(a.zero>>count)|(mask^(mask>>count)),a.one>>count,a.minimum>>count,a.maximum>>count))
            zeros=ones=mask
            for possibility in possibilities:
                zeros &= possibility.zero; ones &= possibility.one
            return Facts(width,zeros,ones,min(p.minimum for p in possibilities),max(p.maximum for p in possibilities))
        if name=='binary:+':
            zeros,ones=((((a.zero<<1)|1)&mask,(a.one<<1)&mask) if same else add_bits(a,b))
            lo,hi=a.minimum+b.minimum,a.maximum+b.maximum
            return Facts(width,zeros,ones,lo if hi<=mask else 0,hi if hi<=mask else mask,excluded_image(lambda x,y:x+y))
        if name=='binary:-':
            zeros,ones=add_bits(a,Facts(width,b.one,b.zero),1)
            nowrap=a.minimum>=b.maximum
            return Facts(width,zeros,ones,a.minimum-b.maximum if nowrap else 0,a.maximum-b.minimum if nowrap else mask,excluded_image(lambda x,y:x-y))
        if name=='binary:*':
            za,zb=trailing_ones(a.zero,width),trailing_ones(b.zero,width)
            ka,kb=trailing_ones(a.zero|a.one,width),trailing_ones(b.zero|b.one,width)
            suffix=(1<<min(width,ka+zb,kb+za))-1
            product=a.one*b.one
            zeros,ones=(~product)&suffix,product&suffix
            if same:
                # Squaring a deterministic word has stronger low-bit facts
                # than multiplying two independently unknown words.
                if 2*za+1<width:zeros|=1<<(2*za+1)
                if za<width and a.one&(1<<za) and 2*za+2<width:zeros|=1<<(2*za+2)
            hi=a.maximum*b.maximum
            return Facts(width,zeros,ones,a.minimum*b.minimum if hi<=mask else 0,hi if hi<=mask else mask)
        if name in ('binary:==','binary:!=','binary:<','binary:<=','binary:>','binary:>='):
            answer=None
            if name in ('binary:==','binary:!='):
                if a.constant is not None and b.constant is not None:answer=a.constant==b.constant
                elif a.maximum<b.minimum or b.maximum<a.minimum or (a.zero&b.one)|(a.one&b.zero):answer=False
                elif (a.constant is not None and a.constant==b.excludes) or (b.constant is not None and b.constant==a.excludes):answer=False
                if answer is not None and name=='binary:!=':answer=not answer
            else:
                if name in ('binary:>','binary:>='):a,b=b,a
                strict=name in ('binary:<','binary:>')
                if a.maximum<b.minimum or (not strict and a.maximum==b.minimum):answer=True
                elif a.minimum>b.maximum or (strict and a.minimum==b.maximum):answer=False
            if answer is not None:return constant(1,int(answer))
        return Facts(width)
    visit = uncached if _memo is None else cached
    return visit(source)


def _candidates(source, *, _scope=(), _depth=0, _memo=None, _facts=None):
    """Propose total whole-expression simplifications, with no proof authority."""
    facts=analyse(source,_scope=_scope,_memo=_memo) if _facts is None else _facts
    kind=source['sort']['Value']
    if facts.constant is not None:
        candidate=(term(value('Bool'),{'Bool':bool(facts.constant)}) if kind=='Bool'
                   else word(kind,facts.constant))
        if candidate!=source:yield 'constant-from-bits-or-range',candidate
    node=source['node']
    if 'Op' not in node:return
    name,args=node['Op']
    if name=='call:choose' and len(args)==3:
        condition=analyse(args[0],_scope=_scope,_memo=_memo).constant
        if condition is not None:yield 'known-condition',args[1 if condition else 2]
        elif _depth < 8:
            branches = list(args)
            for index in (1,2):
                scoped=refine(_scope,args[0],index==1)
                replacement=next(_candidates(args[index],_scope=scoped,_depth=_depth+1,_memo=_memo),None)
                if replacement is not None:branches[index]=replacement[1]
            if branches != args:
                replacement=(branches[1] if branches[1]==branches[2]
                             else op(source['sort'],'call:choose',*branches))
                yield 'branch-scoped-facts',replacement
    if name in ('binary:+','call:word_xor') and len(args)==2 and kind!='Bool':
        a,b=(analyse(t,_scope=_scope,_memo=_memo) for t in args);mask=(1<<facts.width)-1
        if (mask^a.zero)&(mask^b.zero)==0:
            yield 'disjoint-fields',op(source['sort'],'call:word_or',*args)
    # Representation equality alone is insufficient: a lossy round trip is
    # an identity only when this branch's complete input range fits. These are
    # proposal-side fixed word conversions, never type/check-elision authority.
    if name in _WORD_ROUNDTRIPS and len(args)==1:
        inverse, original_kind, maximum = _WORD_ROUNDTRIPS[name]
        inner = args[0]['node'].get('Op')
        if inner is not None and inner[0]==inverse and len(inner[1])==1:
            original = inner[1][0]
            if original['sort']==value(original_kind):
                original_facts = analyse(original,_scope=_scope,_memo=_memo)
                if original_facts.maximum <= maximum:
                    yield 'lossless-word-roundtrip',original
    if name=='call:word_and' and len(args)==2:
        for i in (0,1):
            literal=args[i]['node'].get('Word')
            if literal is not None:
                other=analyse(args[1-i],_scope=_scope,_memo=_memo);mask=(1<<facts.width)-1
                if (mask^literal)&(mask^other.zero)==0:
                    yield 'redundant-mask',args[1-i]


def candidates(source, *, _scope=(), _depth=0):
    """Stream proposals without retaining reusable facts across caller control."""
    yield from _candidates(source, _scope=_scope, _depth=_depth)


def analyse_candidates(source):
    """Return facts and all proposals from one bounded synchronous query.

    The source must remain unchanged during this call. All reuse remains local;
    every returned proposal still needs an independent equality proof.
    """
    memo = _FactMemo()
    try:
        facts = analyse(source, _memo=memo)
        return facts, list(_candidates(source, _memo=memo, _facts=facts))
    finally:
        memo.clear()
