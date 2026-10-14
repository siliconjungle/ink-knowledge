"""Publish independently replayed search/index laws and an untrusted template."""
import argparse,copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,entry,identity
from ink_knowledge.law_templates import SEMANTICS as TEMPLATE

LIBRARIES=Path(__file__).resolve().parents[1]/'libraries'

def source_applicability(compiler,core,bundle,directory):
 d=Path(directory);subject=d/'applicability-subject.json';packet=d/'applicability.json'
 subprocess.run([str(compiler),'emit-semantic',str(core),'--core','-o',str(subject)],check=True,capture_output=True,text=True)
 sha=json.loads(subject.read_text())['input_core_sha256']
 packet.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=sha,knowledge=bundle,applications=[])))
 return subprocess.run([str(compiler),'check-selection',str(core),str(packet)],capture_output=True,text=True)

def publish(compiler,root):
 compiler=str(Path(compiler).resolve());objects={};names={}
 with tempfile.TemporaryDirectory(prefix='ink-sequence-search-') as temporary:
  d=Path(temporary)
  for stem in ['sequence-search','indexed-sequence','owned-index']:
   path=d/(stem+'.json')
   result=subprocess.run([compiler,'emit-laws',str(LIBRARIES/(stem+'-laws.ink')),'-o',str(path)],capture_output=True,text=True,check=True)
   bundle=json.loads(path.read_text());objects.update(bundle['objects'])
   names.update({'sequence-search/'+name:ident for name,ident in json.loads(result.stdout)['names'].items()})
   if stem=='indexed-sequence':
    # Bind the duplicate authoring definitions to the actual executable source.
    # A changed helper fails this check even when its stored proof still replays.
    source=d/'indexed.core.json'
    subprocess.run([compiler,'emit-core',str(LIBRARIES/'indexed-sequences.ink'),'-o',str(source)],check=True,capture_output=True,text=True)
    source_applicability(compiler,source,bundle,d).check_returncode()
  from producers.structure_laws import check
  check(compiler,objects,sorted(names.values()))
 general=objects[names['sequence-search/foldr_any']]['payload']
 law=copy.deepcopy(general)
 def rename(x):
  if isinstance(x,dict):
   if x=={'Named':'A'}:return {'Named':'$A'}
   return {k:rename(v) for k,v in x.items()}
  if isinstance(x,list):return [rename(v) for v in x]
  return x
 law=rename(law)
 for key in ['types','assumptions','definition_context']:law.pop(key,None)
 law['semantics']='ink-conditional-laws-v1'
 template=entry('definition',TEMPLATE,dict(type_parameters=['A'],law=law,dependencies={}))
 objects[identity(template)]=template;names['sequence-search/template/foldr_any']=identity(template)
 store=Store(root).extend(objects.values(),names)
 roots=sorted(set(names.values())-{identity(template)})
 (Path(root)/'store/sequence-search-view.json').write_bytes(canonical(store.bundle(roots))+b'\n')
 return dict(schema=1,status='checked',snapshot=store.snapshot_id,names=names,scope='Generic existence search and u32 indexed membership/filtering. Template proposals replay concrete ordinary proofs; no performance authority.')

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--compiler',required=True);p.add_argument('--root',required=True);a=p.parse_args()
 print(json.dumps(publish(a.compiler,a.root)))
