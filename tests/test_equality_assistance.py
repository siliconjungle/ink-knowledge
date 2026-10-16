"""Assisted search cannot turn a conjectured scalar equality into a premise."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.equality_assistance import prove_with_equalities
from producers.semantic_laws import value, var
from tests.test_v8_integer_laws import compiler, run, SOURCE, DATA
from producers.frozen_laws import read,closure


class EqualityAssistance(unittest.TestCase):
 def check(self, core, directory, law):
  obj=semantic_entry(law);entries=[semantic_entry(w)for _,w in closure(DATA,[('candidate',law)])];store=Store.publish(directory,entries);path=directory/'view.json'
  path.write_bytes(canonical(store.bundle([identity(obj)])))
  return run(compiler(),'knowledge-check',core,path,ok=False)

 def test_ordered_facts_retain_and_discharge_original_conditions(self):
  x,y=[var(value('U64'),n)for n in ['x','y']]
  equation={'from':x,'to':y};goal=dict(params={'x':value('U64'),'y':value('U64')},conditions=[equation],**equation)
  facts=[dict(equation,proof={'Hypothesis':0}),dict(**{'from':y,'to':x},proof={'Sym':{'Hypothesis':1}})]
  original=copy.deepcopy((goal,facts));requests=[]
  def author(request):requests.append(request);return {'Hypothesis':1}
  law=prove_with_equalities(goal,facts,author)
  self.assertEqual((goal,facts),original);self.assertEqual(len(requests[0]['conditions']),3)
  self.assertEqual(law['conditions'],goal['conditions'])
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
   self.assertEqual(self.check(d/'core.json',d/'positive',law).returncode,0)
   bad=copy.deepcopy(law);bad['conditions']=[]
   self.assertNotEqual(self.check(d/'core.json',d/'escaped',bad).returncode,0)

 def test_unproved_or_wrong_equalities_cannot_authorize_frozen_remainders(self):
  rows={r['name']:r['law']for r in read(DATA)}
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
   for name in ['u64_rem_or_self','u64_rem_or_zero_numerator']:
    law=rows[name];self.assertEqual(len(law['dependencies']),1)
    self.assertEqual(self.check(d/'core.json',d/(name+'-positive'),law).returncode,0)
    for mode in ['unproved','wrong-endpoint','missing-fact','wrong-body']:
     bad=copy.deepcopy(law);node=bad['proof']['AssertEquality']
     if mode=='unproved':node['premise']='Normalize'
     elif mode=='wrong-endpoint':node['equality']['to']={'sort':value('U64'),'node':{'Word':17}}
     elif mode=='missing-fact':bad['proof']=node['body']
     else:node['body']['BitVector']['hypotheses']=[1]
     result=self.check(d/'core.json',d/(name+'-'+mode),bad)
     self.assertNotEqual(result.returncode,0,(name,mode,result.stderr))

 def test_bounded_exact_scalar_assistance(self):
  x=var(value('U64'),'x');goal=dict(params={'x':value('U64')},conditions=[],**{'from':x,'to':x})
  fact=dict(**{'from':x,'to':x},proof='Normalize')
  for facts in [[],[fact]*17]:
   with self.assertRaises(ValueError):prove_with_equalities(goal,facts,lambda g:'Normalize')
  bad=copy.deepcopy(fact);bad['to']=var(value('U32'),'x')
  with self.assertRaises(ValueError):prove_with_equalities(goal,[bad],lambda g:'Normalize')
  for carrier in ['F32','F64']:
   bad=copy.deepcopy(fact);bad['from']['sort']=bad['to']['sort']=value(carrier)
   with self.assertRaises(ValueError):prove_with_equalities(goal,[bad],lambda g:'Normalize')


if __name__=='__main__':unittest.main()
