"""Untrusted ordered sequence trees, independent of a source action or row shape.

Leaves retain every row in order, including duplicate keys. Cached bounds permit
pruning without assuming that the input is sorted. AVL concatenation and rotations
are ordinary first-order definitions. A definition is not replacement authority:
the accompanying universal equations must be checked before representation use.
"""
from producers.action_replacement import var, call, cons
from producers.point_delta import binary, choice, match

U = lambda n: {'U64': n}
D = lambda i: {'Data': i}


def define(table, row_sort, option, add, contribution=None):
    tree = add({'Datatype': {'constructors': [
        {'name': 'Empty', 'fields': []},
        {'name': 'Leaf', 'fields': ['U64', row_sort]},
        {'name': 'Branch', 'fields': ['SelfType', 'SelfType', 'U64', 'U64', 'U64', 'U64']},
    ]}})
    T, L = D(tree), D(table)
    t, left, right, key, value = map(var, ['tree', 'left', 'right', 'key', 'value'])
    names = ['left', 'right', 'minimum', 'maximum', 'height', 'measure']
    empty = cons(tree, 0, [])
    leaf = lambda k, v: cons(tree, 1, [k, v])
    branch = lambda l, r, lo, hi, h, s: cons(tree, 2, [l, r, lo, hi, h, s])
    ids = {'datatype': tree}

    def fn(name, params, result, body, recursive=None):
        identity = add({'Function': dict(params=params, result=result, body=body, recursive=recursive)})
        ids[name] = identity
        return lambda *xs: call(identity, list(xs))

    minimum = fn('minimum', [['tree', T]], 'U64', match(t, [([], U(2**64-1)), (['key', 'value'], key), (names, var('minimum'))]))
    maximum = fn('maximum', [['tree', T]], 'U64', match(t, [([], U(0)), (['key', 'value'], key), (names, var('maximum'))]))
    height = fn('height', [['tree', T]], 'U64', match(t, [([], U(0)), (['key', 'value'], U(1)), (names, var('height'))]))
    measure = fn('measure', [['tree', T]], 'U64', match(t, [([], U(0)), (['key', 'value'], call(contribution, [value]) if contribution else U(1)), (names, var('measure'))]))
    lo = choice(binary('<', minimum(left), minimum(right)), minimum(left), minimum(right))
    hi = choice(binary('>', maximum(left), maximum(right)), maximum(left), maximum(right))
    h = binary('+', choice(binary('>', height(left), height(right)), height(left), height(right)), U(1))
    node0 = branch(left, right, lo, hi, h, binary('+', measure(left), measure(right)))
    node = fn('node', [['left', T], ['right', T]], T,
              match(left, [([], right), (['lk', 'lv'], match(right, [([], left), (['rk', 'rv'], node0), (['rl','rr','rlo','rhi','rh','rs'], node0)])),
                           (['ll','lr','llo','lhi','lh','ls'], match(right, [([], left), (['rk', 'rv'], node0), (['rl','rr','rlo','rhi','rh','rs'], node0)]))]))

    # Single/double rotations only rearrange leaves; no key sorting or deduplication.
    ll, lr, rl, rr = map(var, ['ll', 'lr', 'rl', 'rr'])
    left_rotation = choice(binary('>=', height(ll), height(lr)), node(ll, node(lr, right)),
                          match(lr, [([], node(left, right)), (['mk','mv'], node(left, right)),
                                     (['ml','mr','mlo','mhi','mh','ms'], node(node(ll,var('ml')),node(var('mr'),right)))]))
    right_rotation = choice(binary('>=', height(rr), height(rl)), node(node(left, rl), rr),
                           match(rl, [([], node(left, right)), (['mk','mv'], node(left, right)),
                                      (['ml','mr','mlo','mhi','mh','ms'], node(node(left,var('ml')),node(var('mr'),rr)))]))
    balance = fn('balance', [['left', T], ['right', T]], T,
                 choice(binary('>', height(left), binary('+', height(right), U(1))),
                        match(left, [([], node(left,right)), (['lk','lv'], node(left,right)),
                                     (['ll','lr','llo','lhi','lh','ls'], left_rotation)]),
                        choice(binary('>', height(right), binary('+', height(left), U(1))),
                               match(right, [([], node(left,right)), (['rk','rv'], node(left,right)),
                                             (['rl','rr','rlo','rhi','rh','rs'], right_rotation)]), node(left,right))))
    # Separate structural recursions avoid mutual recursion or an unchecked
    # numerical termination argument. join_right precedes join_left in the DAG.
    join_right = fn('join_right', [['left', T], ['right', T]], T,
                    match(right, [([], left), (['rk','rv'], node(left,right)),
                                  (['rl','rr','rlo','rhi','rh','rs'],
                                   choice(binary('>', height(right), binary('+',height(left),U(1))),
                                          balance({'SelfCall':[left,rl]},rr),node(left,right)))]), 1)
    join = fn('join', [['left', T], ['right', T]], T,
              match(left, [([], right), (['lk','lv'], join_right(left,right)),
                           (['ll','lr','llo','lhi','lh','ls'],
                            choice(binary('>',height(left),binary('+',height(right),U(1))),
                                   balance(ll,{'SelfCall':[lr,right]}),join_right(left,right)))]), 0)
    outside = lambda x: binary('||',binary('<',key,minimum(x)),binary('>',key,maximum(x)))
    none, some = cons(option,0,[]), lambda v:cons(option,1,[v])
    get_left = {'SelfCall':[left,key]}
    fn('get', [['tree',T],['key','U64']], D(option), match(t,[([],none),(['head','row'],choice(binary('==',key,var('head')),some(var('row')),none)),
        (names,choice(outside(t),none,match(get_left,[([],{'SelfCall':[right,key]}),(['found'],some(var('found')))])))]),0)
    fn('insert', [['tree',T],['key','U64'],['value',row_sort]], T, match(t,[([],leaf(key,value)),(['head','row'],choice(binary('<',key,var('head')),node(leaf(key,value),t),node(t,leaf(key,value)))),
        (names,choice(binary('<',key,maximum(left)),balance({'SelfCall':[left,key,value]},right),balance(left,{'SelfCall':[right,key,value]})))]),0)
    fn('replace', [['tree',T],['key','U64'],['value',row_sort]], T, match(t,[([],empty),(['head','row'],leaf(var('head'),choice(binary('==',key,var('head')),value,var('row')))),
        (names,choice(outside(t),t,node({'SelfCall':[left,key,value]},{'SelfCall':[right,key,value]})))]),0)
    fn('remove', [['tree',T],['key','U64']], T, match(t,[([],empty),(['head','row'],choice(binary('==',key,var('head')),empty,t)),
        (names,choice(outside(t),t,join({'SelfCall':[left,key]},{'SelfCall':[right,key]})))]),0)
    nil = cons(table,0,[])
    append = fn('append', [['rows',L],['rest',L]], L,match(var('rows'),[([],var('rest')),(['head','row','tail'],cons(table,1,[var('head'),var('row'),{'SelfCall':[var('tail'),var('rest')]}]))]),0)
    fn('decode', [['tree',T]], L,match(t,[([],nil),(['head','row'],cons(table,1,[var('head'),var('row'),nil])),(names,append({'SelfCall':[left]},{'SelfCall':[right]}))]),0)
    fn('encode', [['rows',L]], T,match(var('rows'),[([],empty),(['head','row','tail'],join(leaf(var('head'),var('row')),{'SelfCall':[var('tail')]}))]),0)
    fn('decorate', [['tree',T]], T,match(t,[([],empty),(['head','row'],t),(names,node({'SelfCall':[left]},{'SelfCall':[right]}))]),0)
    fn('copy_shape', [['tree',T]], T,match(t,[([],empty),(['head','row'],leaf(var('head'),var('row'))),
        (names,branch(left,right,var('minimum'),var('maximum'),var('height'),var('measure')))]))
    # Independent invariant components keep each mathematical obligation small.
    # Height guides balancing but is not a premise of source equivalence.
    validations=[]
    for label,field,expected in [('minimum',var('minimum'),lo),('maximum',var('maximum'),hi),('measure',var('measure'),binary('+',measure(left),measure(right)))]:
        body=binary('&&',{'SelfCall':[left]},binary('&&',{'SelfCall':[right]},binary('==',field,expected)))
        validate=fn(label+'_valid',[['tree',T]],'Bool',match(t,[([],{'Bool':True}),(['head','row'],{'Bool':True}),(names,body)]),0)
        validations.append(validate(t))
    valid=validations[-1]
    for item in reversed(validations[:-1]):valid=binary('&&',item,valid)
    fn('valid',[['tree',T]],'Bool',valid)
    fn('find',[['tree',T],['key','U64']],D(option),match(t,[([],none),(['head','row'],choice(binary('==',key,var('head')),some(var('row')),none)),(names,match({'SelfCall':[left,key]},[([],{'SelfCall':[right,key]}),(['found'],some(var('found')))]))]),0)
    fn('contains',[['tree',T],['key','U64']],'Bool',match(t,[([],{'Bool':False}),(['head','row'],binary('==',key,var('head'))),(names,binary('||',{'SelfCall':[left,key]},{'SelfCall':[right,key]}))]),0)
    fn('rows_get',[['rows',L],['key','U64']],D(option),match(var('rows'),[([],none),(['head','row','tail'],choice(binary('==',key,var('head')),some(var('row')),{'SelfCall':[var('tail'),key]}))]),0)
    rw,tail,head,row=map(var,['rows','tail','head','row'])
    for op in ['insert','replace','remove']:
        args=[['rows',L],['key','U64']]+([]if op=='remove'else[['value',row_sort]])
        rec={'SelfCall':[tail,key]+([]if op=='remove'else[value])}
        construct=lambda k,v,t:cons(table,1,[k,v,t])
        if op=='insert':body=choice(binary('<',key,head),construct(key,value,rw),construct(head,row,rec));base=construct(key,value,nil)
        elif op=='replace':body=construct(head,choice(binary('==',key,head),value,row),rec);base=nil
        else:body=choice(binary('==',key,head),rec,construct(head,row,rec));base=nil
        fn('rows_'+op,args,L,match(rw,[([],base),(['head','row','tail'],body)]),0)
    fn('has_key',[['rows',L],['key','U64']],'Bool',match(rw,[([],{'Bool':False}),(['head','row','tail'],binary('||',binary('==',key,head),{'SelfCall':[tail,key]}))]),0)
    fn('has_greater',[['rows',L],['key','U64']],'Bool',match(rw,[([],{'Bool':False}),(['head','row','tail'],binary('||',binary('<',key,head),{'SelfCall':[tail,key]}))]),0)
    return ids
