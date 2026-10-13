"""Genuine ordinary laws: distribute new operations over a known pure choice.

No sampled float identities, reassociation, reciprocal multiplication or
approximation-to-exact replacements. The same Cases proof works for any typed
primitive signature; each instance remains independently checked.
"""
from ink_knowledge import Store,identity,semantic_entry
from producers.semantic_laws import value,var,op,law

SIGNATURES=[
('sqrt',['F32'],'F32'),('f32_div',['F32','F32'],'F32'),
('floor',['F32'],'F32'),('ceil',['F32'],'F32'),('trunc',['F32'],'F32'),('round_ties_even',['F32'],'F32'),
('is_nan',['F32'],'Bool'),('is_finite',['F32'],'Bool'),('f32_bits',['F32'],'U32'),('f32_from_bits',['U32'],'F32'),
('f32_from_u32',['U32'],'F32'),('f32_from_u64',['U64'],'F32'),('f32_from_i32',['I32'],'F32'),('f32_from_int',['Int'],'F32'),
('u32_from_f32',['F32'],{'Option':'U32'}),('u64_from_f32',['F32'],{'Option':'U64'}),('i32_from_f32',['F32'],{'Option':'I32'}),('int_from_f32',['F32'],{'Option':'Int'}),
('string_byte_len',['String'],'U32'),('string_byte_at',['String','U32'],{'Option':'U32'}),('string_slice',['String','U32','U32'],{'Option':'String'}),('string_concat',['String','String'],'String'),('string_find',['String','String','U32'],{'Option':'U32'}),
]+[(n,[t],'U32')for n in ['popcount','leading_zeros','trailing_zeros']for t in ['U32','U64','I32']]

def objects():
 rows=[]
 for n,inputs,result in SIGNATURES:
  for index in range(len(inputs)):
   c=var(value('Bool'),'c');params={'c':c['sort']};yes=[];no=[]
   for i,t in enumerate(inputs):
    a=var(value(t),'a'+str(i));params['a'+str(i)]=a['sort'];yes.append(a);no.append(a)
    if i==index:
     b=var(value(t),'b'+str(i));params['b'+str(i)]=b['sort'];no[-1]=b
   args=list(yes);args[index]=op(yes[index]['sort'],'call:choose',c,yes[index],no[index])
   from_=op(value(result),'call:'+n,*args);to=op(value(result),'call:choose',c,op(value(result),'call:'+n,*yes),op(value(result),'call:'+n,*no))
   proof={'Cases':dict(condition=c,on_false='Normalize',on_true='Normalize')}
   rows.append((n+'/'+str(inputs[0])+'/'+str(index),semantic_entry(law(params,from_,to,proof))))
 return rows

def publish(root):
 rows=objects();return Store(root).extend([o for _,o in rows],{'numeric-text/choice/'+n:identity(o)for n,o in rows})
