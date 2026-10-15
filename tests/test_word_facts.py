"""Check conservative bit/range inference independently, including overflow."""
import random
import unittest
from producers.semantic_laws import value,var,word,op
from producers.word_facts import analyse,candidates


def evaluate(t,values):
    kind=t['sort']['Value'];width={'U32':32,'U64':64,'Bool':1}[kind];mask=(1<<width)-1
    n=t['node']
    if 'Word' in n:return n['Word']&mask
    if 'Bool' in n:return int(n['Bool'])
    if 'Free' in n:return values[n['Free']]&mask
    name,args=n['Op'];a=[evaluate(t,values) for t in args]
    operations={'call:word_and':lambda:a[0]&a[1],'call:word_or':lambda:a[0]|a[1],
                'call:word_xor':lambda:a[0]^a[1],'call:word_not':lambda:~a[0],
                'binary:+':lambda:a[0]+a[1],'binary:-':lambda:a[0]-a[1],
                'binary:*':lambda:a[0]*a[1],
                'call:wrapping_shl':lambda:a[0]<<(a[1]%width),
                'call:wrapping_shr':lambda:a[0]>>(a[1]%width),
                'call:rotate_left':lambda:(a[0]<<(a[1]%width))|(a[0]>>((-a[1])%width)),
                'call:rotate_right':lambda:(a[0]>>(a[1]%width))|(a[0]<<((-a[1])%width)),
                'binary:<':lambda:a[0]<a[1],'binary:>=':lambda:a[0]>=a[1],
                'binary:<=':lambda:a[0]<=a[1],'binary:>':lambda:a[0]>a[1],
                'binary:==':lambda:a[0]==a[1],'binary:!=':lambda:a[0]!=a[1],
                'binary:&&':lambda:bool(a[0]) and bool(a[1]),
                'binary:||':lambda:bool(a[0]) or bool(a[1]),'unary:!':lambda:not a[0],
                'call:choose':lambda:a[1] if a[0] else a[2],
                'call:word_widen_u32_to_u64':lambda:a[0],
                'call:word_narrow_u64_to_u32':lambda:a[0]}
    return int(operations[name]())&mask


class WordFacts(unittest.TestCase):
    def test_generated_circuits_never_claim_bits_or_bounds_contradicted_by_values(self):
        rng=random.Random(831731)
        for kind,width in [('U32',32),('U64',64)]:
            s=value(kind);mask=(1<<width)-1;x=var(s,'x');y=var(s,'y')
            atoms=[x,y,*[word(kind,n) for n in (0,1,7,255,mask,1<<(width-1))]]
            pool=list(atoms)
            for _ in range(120):
                name=rng.choice(['call:word_and','call:word_or','call:word_xor','binary:+','binary:-','binary:*'])
                left=rng.choice(pool[-24:]);right=rng.choice(atoms)
                source=op(s,name,left,right);pool.append(source)
            pool += [op(s,name,x,word('U32',n)) for name in ('call:wrapping_shl','call:wrapping_shr')
                     for n in (0,1,31,32,63,64,65,4294967295)]
            inputs=[{'x':a,'y':b} for a in (0,1,mask,mask-1,1<<(width-1)) for b in (0,1,mask)]
            inputs += [dict(x=rng.getrandbits(width),y=rng.getrandbits(width)) for _ in range(80)]
            for source in pool:
                facts=analyse(source)
                alternatives=list(candidates(source))
                for inputs_ in inputs:
                    actual=evaluate(source,inputs_)
                    self.assertEqual(actual&facts.zero,0)
                    self.assertEqual(actual&facts.one,facts.one)
                    self.assertLessEqual(facts.minimum,actual)
                    self.assertGreaterEqual(facts.maximum,actual)
                    for _,replacement in alternatives:self.assertEqual(actual,evaluate(replacement,inputs_))

    def test_branch_local_bounds_simplify_without_leaking_to_other_branches(self):
        from producers.semantic_laws import term
        boolean=value('Bool')
        for kind,width in [('U32',32),('U64',64)]:
            sort=value(kind);x=var(sort,'x');mask=(1<<width)-1
            low=op(boolean,'binary:<',x,word(kind,256))
            masked=op(sort,'call:word_and',x,word(kind,255))
            source=op(sort,'call:choose',low,masked,x)
            self.assertIn(('branch-scoped-facts',x),list(candidates(source)))
            # Opposite branch has no upper bound. Dropping its mask is wrong.
            opposite=op(sort,'call:choose',low,x,masked)
            self.assertNotIn(('branch-scoped-facts',x),list(candidates(opposite)))
            # Nested scopes intersect; an unknown outer condition joins values.
            hi=op(boolean,'binary:>=',x,word(kind,16))
            nested=op(sort,'call:choose',hi,
                      op(sort,'call:choose',low,masked,x),x)
            for _,replacement in candidates(nested):
                for n in [0,15,16,255,256,mask]:
                    self.assertEqual(evaluate(nested,dict(x=n)),evaluate(replacement,dict(x=n)))
            # True conjunction and false disjunction carry both constraints.
            for guard,branch in [(op(boolean,'binary:&&',low,hi),1),
                                 (op(boolean,'binary:||',op(boolean,'unary:!',low),
                                     op(boolean,'unary:!',hi)),2)]:
                arms=[x,x];arms[branch-1]=masked
                guarded=op(sort,'call:choose',guard,*arms)
                self.assertIn(('branch-scoped-facts',x),list(candidates(guarded)))
            # True disjunction does not imply either bound separately.
            loose=op(sort,'call:choose',op(boolean,'binary:||',low,hi),masked,x)
            self.assertNotIn(('branch-scoped-facts',x),list(candidates(loose)))
            # Range information must not turn wrapping arithmetic into nowrap.
            room=op(boolean,'binary:>=',x,word(kind,mask-1))
            increment=op(sort,'binary:+',x,word(kind,1))
            wrapped=op(sort,'call:choose',room,increment,word(kind,0))
            facts=analyse(wrapped)
            for n in [0,mask-2,mask-1,mask]:
                actual=evaluate(wrapped,dict(x=n))
                self.assertLessEqual(facts.minimum,actual);self.assertGreaterEqual(facts.maximum,actual)

    def test_all_comparison_directions_boundaries_and_composite_subjects(self):
        boolean=value('Bool')
        rng=random.Random(618024)
        for kind,width in [('U32',32),('U64',64)]:
            sort=value(kind);x=var(sort,'x');mask=(1<<width)-1
            inputs=list(range(260))+[mask,mask-1,mask-255]+[rng.getrandbits(width) for _ in range(40)]
            for subject in [x,op(sort,'binary:+',x,word(kind,1))]:
                masked=op(sort,'call:word_and',subject,word(kind,255))
                for name in ['<','<=','>','>=','==','!=']:
                    for bound in [0,1,255,256,mask]:
                        for reverse in [False,True]:
                            args=[subject,word(kind,bound)]
                            if reverse:args.reverse()
                            guard=op(boolean,'binary:'+name,*args)
                            for arms in [(masked,subject),(subject,masked)]:
                                source=op(sort,'call:choose',guard,*arms)
                                facts=analyse(source);alternatives=list(candidates(source))
                                for n in inputs:
                                    actual=evaluate(source,dict(x=n))
                                    self.assertEqual(actual&facts.zero,0)
                                    self.assertEqual(actual&facts.one,facts.one)
                                    self.assertLessEqual(facts.minimum,actual)
                                    self.assertGreaterEqual(facts.maximum,actual)
                                    for _,replacement in alternatives:
                                        self.assertEqual(actual,evaluate(replacement,dict(x=n)))

    def test_wrapping_addition_does_not_invent_monotonicity(self):
        s=value('U32');x=var(s,'x');inc=op(s,'binary:+',x,word('U32',1))
        facts=analyse(inc)
        self.assertEqual((facts.minimum,facts.maximum),(0,4294967295))
        comparison=op(value('Bool'),'binary:>',inc,x)
        self.assertIsNone(analyse(comparison).constant)

    def test_masked_fields_and_redundant_masks_are_proposed(self):
        s=value('U32');x=var(s,'x');y=var(s,'y')
        a=op(s,'call:word_and',x,word('U32',255))
        b=op(s,'call:word_and',y,word('U32',65280))
        self.assertEqual(next(candidates(op(s,'binary:+',a,b)))[0],'disjoint-fields')
        self.assertIn(('redundant-mask',a),list(candidates(op(s,'call:word_and',a,word('U32',65535)))))
        bounded=op(value('Bool'),'binary:<',a,word('U32',256))
        self.assertEqual(analyse(bounded).constant,1)

    def test_correlated_arithmetic_and_known_product_suffixes(self):
        for kind,width in [('U32',32),('U64',64)]:
            s=value(kind);x=var(s,'x');y=var(s,'y')
            self.assertEqual(analyse(op(s,'binary:+',x,x)).zero&1,1)
            self.assertEqual(analyse(op(s,'binary:-',x,x)).constant,0)
            self.assertEqual(analyse(op(s,'binary:*',x,x)).zero&2,2)
            odd=op(s,'call:word_or',x,word(kind,1))
            square=analyse(op(s,'binary:*',odd,odd))
            self.assertEqual(square.zero&6,6);self.assertEqual(square.one&7,1)
            left=op(s,'call:word_or',op(s,'call:word_and',x,word(kind,((1<<width)-1)^15)),word(kind,12))
            right=op(s,'call:word_or',op(s,'call:word_and',y,word(kind,((1<<width)-1)^7)),word(kind,6))
            product=analyse(op(s,'binary:*',left,right))
            self.assertEqual(product.zero&31,(~72)&31)
            self.assertEqual(product.one&31,72&31)
            difference=analyse(op(s,'binary:-',left,right))
            self.assertEqual(difference.one&7,6)
            self.assertEqual(difference.zero&7,1)
            for name,answer in [('binary:==',1),('binary:!=',0),('binary:<',0),('binary:<=',1)]:
                self.assertEqual(analyse(op(value('Bool'),name,x,x)).constant,answer)

    def test_variable_shift_residues_preserve_wrapping_semantics(self):
        rng=random.Random(412)
        for kind,width in [('U32',32),('U64',64)]:
            s=value(kind);x=var(s,'x');k=var(value('U32'),'k');mask=(1<<width)-1
            count=op(value('U32'),'call:word_or',op(value('U32'),'call:word_and',k,word('U32',3)),word('U32',4))
            shifted=op(s,'call:wrapping_shl',x,count)
            self.assertEqual(analyse(shifted).zero&15,15)
            # A high set bit does not establish a positive effective count.
            wrapped=op(s,'call:wrapping_shl',x,op(value('U32'),'call:word_or',k,word('U32',width)))
            self.assertEqual(analyse(wrapped).zero,0)
            for direction in ['call:wrapping_shl','call:wrapping_shr']:
                for count_expr in [count,k,op(value('U32'),'call:word_or',k,word('U32',width))]:
                    source=op(s,direction,op(s,'call:word_and',x,word(kind,255)),count_expr)
                    facts=analyse(source)
                    for count_value in [0,1,31,32,63,64,65,4294967295]+[rng.getrandbits(32) for _ in range(100)]:
                        actual=evaluate(source,dict(x=rng.getrandbits(width),k=count_value))
                        self.assertEqual(actual&facts.zero,0)
                        self.assertEqual(actual&facts.one,facts.one)
                        self.assertLessEqual(facts.minimum,actual);self.assertGreaterEqual(facts.maximum,actual)

    def test_known_condition_proposal_retains_selected_expression(self):
        s=value('U32');x=var(s,'x');y=var(s,'y')
        condition=op(value('Bool'),'binary:==',x,x)
        source=op(s,'call:choose',condition,x,y)
        self.assertIn(('known-condition',x),list(candidates(source)))


if __name__=='__main__':unittest.main()
