"""A proposal filter must preserve exhaustive matching, including lexical holes."""
import unittest
from ink_knowledge.pattern_index import TermIndex
from ink_planner.semantic_search import match
from producers.semantic_laws import arrow,bound,lam,op,term,value,var,word


class TermHeadDispatch(unittest.TestCase):
    def test_exact_matching_bindings_order_duplicates_and_captures_are_preserved(self):
        u32=value('U32');u64=value('U64');f32=value('F32');boolean=value('Bool')
        x=var(u32,'x');a=var(u32,'renamed');b=var(u32,'different');function=arrow(u32,u32)
        repeated=op(u32,'binary:+',x,x)
        callback=lam(u32,op(u32,'apply',var(function,'f'),bound(u32,0)))
        capture=lam(u32,op(u32,'apply',lam(u32,bound(u32,1)),bound(u32,0)))
        ordinary=lam(u32,op(u32,'apply',var(function,'renamed_function'),bound(u32,0)))
        same=op(u32,'binary:+',a,a)
        sites=[a,b,word('U32',0),word('U64',0),word('F32',0x80000000),
               term(boolean,{'Bool':True}),term(boolean,{'Bool':False}),
               same,op(u32,'binary:+',a,b),same,op(u32,'binary:*',a,a),
               op(u64,'binary:+',var(u64,'renamed'),word('U64',0)),
               ordinary,capture,term(value({'List':'U32'}),'Nil'),
               var(function,'renamed_function'),bound(u32,0)]
        patterns=[(x,{'x':u32}),(a,{}),(word('U32',0),{}),
                  (var(u64,'x'),{'x':u64}),(var(f32,'x'),{'x':f32}),
                  (term(boolean,{'Bool':False}),{}),
                  (repeated,{'x':u32}),(callback,{'f':function}),
                  (term(value({'List':'U32'}),'Nil'),{}),
                  (var(function,'f'),{'f':function}),(bound(u32,0),{})]
        index=TermIndex(iter(sites))
        def matches(pattern,params,terms):
            result=[]
            for t in terms:
                bindings={}
                if match(pattern,t,params,bindings):result.append((id(t),bindings))
            return result
        for pattern,params in patterns:
            self.assertEqual(matches(pattern,params,index.candidates(pattern,params)),
                             matches(pattern,params,sites))
        self.assertEqual(len(matches(repeated,{'x':u32},sites)),2)
        self.assertEqual(len(matches(callback,{'f':function},sites)),1)
        self.assertEqual(list(TermIndex([]).candidates(x,{'x':u32})),[])
        self.assertEqual(list(index.candidates(word('U32',99))),[sites[2]])

    def test_same_operator_with_different_structure_still_requires_exact_match(self):
        u32=value('U32');x=var(u32,'x');pattern=op(u32,'binary:+',x,x)
        target=op(u32,'binary:+',word('U32',1),word('U32',2))
        candidates=list(TermIndex([target]).candidates(pattern,{'x':u32}))
        self.assertEqual(candidates,[target])
        self.assertFalse(match(pattern,target,{'x':u32},{}))
