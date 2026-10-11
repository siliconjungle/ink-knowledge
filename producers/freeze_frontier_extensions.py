#!/usr/bin/env python3
"""Freeze reproducible checked-candidate inputs without treating archives as proofs."""
import argparse,gzip,hashlib,json,os,subprocess,sys
from pathlib import Path
KNOWLEDGE=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(KNOWLEDGE),str(KNOWLEDGE/'producers')]
from producers.representations import generate
from producers.representation_product import generate as product
from producers.representation_bridge import generate as bridge

def candidates(kind,model,path):
    if kind in ['grid','heap']:return [generate(model,path/'plain')['requests'][0],generate(model,path/'cached',cache_query='route'if kind=='grid'else'sorted',preserve_cache=True,delta_query=True)['requests'][1]]
    if kind=='mutations':return generate(model,path,column_mutations=True,packed_booleans=True)['requests']
    if kind=='fields':return generate(model,path,cache_query='cached',preserve_cache=True,delta_query=True)['requests']
    if kind=='ordered':return generate(model,path,ordered_queries=['active','all'],packed_booleans=True)['requests']
    if kind=='grouped':return generate(model,path,cache_query='groups',preserve_cache=True,aggregate_query=True)['requests']
    if kind=='fused':return generate(model,path,fused_queries=['groups'])['requests']
    if kind=='dense':return [generate(model,path/'plain',column_mutations=True)['requests'][0],generate(model,path/'dense',dense_slots=2)['requests'][0]]
    if kind=='index':return [generate(model,path/'plain',column_mutations=True)['requests'][0],generate(model,path/'indexed',indexed=True)['requests'][0]]
    if kind=='shared':
        components=[generate(model,path/name,cache_query=name,preserve_cache=True,delta_query=True)['requests'][1]for name in ['zero','one']]
        return [product(model,components,path/'plain',{'one':1}),product(model,components,path/'shared',{'one':1},True)]
    raise ValueError(kind)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--output-root',type=Path,default=KNOWLEDGE/'research/frontier-extensions-current');p.add_argument('--case',action='append',choices=['mutations','fields','shared','ordered','grouped','fused','index','dense','grid','heap']);a=p.parse_args()
    compiler=Path(os.environ['INK_COMPILER']);workspace=a.workspace.resolve()
    sources={'grid':workspace/'examples/frontier-algorithm-cache.ink','heap':workspace/'examples/frontier-heap-cache.ink','mutations':workspace/'examples/frontier-packed-flags.ink','fields':workspace/'examples/frontier-field-sensitive.ink','shared':KNOWLEDGE/'research/product-caches/source.ink','ordered':workspace/'examples/frontier-ordered-results.ink','grouped':workspace/'examples/frontier-grouped-results.ink','fused':workspace/'examples/frontier-grouped-results.ink','index':KNOWLEDGE/'research/product-caches/source.ink','dense':KNOWLEDGE/'research/product-caches/source.ink'}
    for kind in a.case or sources:
        directory=a.output_root/kind;directory.mkdir(parents=True,exist_ok=True)
        work=KNOWLEDGE/'build/frontier-freeze'/kind;work.mkdir(parents=True,exist_ok=True)
        (directory/'source.ink').write_bytes(sources[kind].read_bytes())
        subprocess.run([compiler,'emit-action-model',directory/'source.ink','-o',work/'model.json'],check=True,capture_output=True)
        model=json.loads((work/'model.json').read_text());requests=candidates(kind,model,work/'database')
        frozen={'model.json':json.dumps(model,separators=(',',':')).encode()}
        for i,request in enumerate(requests):
            raw=json.dumps(request,separators=(',',':')).encode();(work/(str(i)+'.json')).write_bytes(raw)
            subprocess.run([compiler,'check-representation',directory/'source.ink',work/(str(i)+'.json')],check=True,capture_output=True)
            frozen[str(i)+'.json']=raw
        for label,before,after in [('forward',0,1),('reverse',1,0)]:
            migration=bridge(requests[before],requests[after],work/(label+'-store'),True);raw=json.dumps(migration,separators=(',',':')).encode();(work/(label+'.json')).write_bytes(raw)
            subprocess.run([compiler,'check-migration',directory/'source.ink',work/(str(before)+'.json'),work/(str(after)+'.json'),work/(label+'.json')],check=True,capture_output=True)
            frozen[label+'.json']=raw
        for name,raw in frozen.items():(directory/(name+'.gz')).write_bytes(gzip.compress(raw,mtime=0))
        manifest=dict(schema=1,case=kind,source_sha256=hashlib.sha256((directory/'source.ink').read_bytes()).hexdigest(),source_identity=model['source'],representations=[r['representation']for r in requests],files={name:hashlib.sha256(raw).hexdigest()for name,raw in frozen.items()},compression='gzip, mtime zero; hashes bind decompressed exact bytes',scope='Every archived request and both migration directions were checked. Archive identities establish integrity only; replay must run the existing checker.')
        (directory/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(kind,'frozen and checked',flush=True)
if __name__=='__main__':main()
