"""Publish exact error-budget and finite-probability laws after kernel replay."""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from ink_knowledge import Store, canonical


def publish(compiler, root):
    compiler = str(Path(compiler).resolve())
    libraries = Path(__file__).resolve().parents[1] / 'libraries'
    with tempfile.TemporaryDirectory(prefix='ink-approximation-laws-') as temporary:
        output = Path(temporary) / 'laws.json'
        run = subprocess.run([compiler, 'emit-laws', str(libraries / 'approximation-laws.ink'),
                              '--proofs', str(libraries / 'approximation-laws.proofs.json'),
                              '-o', str(output)], capture_output=True, text=True, timeout=120)
        if run.returncode:
            raise ValueError('approximation law admission failed: ' + run.stderr)
        bundle = json.loads(output.read_bytes())
        names = {'approximation/' + name: ident for name, ident in json.loads(run.stdout)['names'].items()}
    from producers.contract_algebra import templates
    generated,mapping=templates(bundle['objects'])
    names.update({'templates/'+name:mapping[ident]for name,ident in list(names.items())if ident in mapping})
    objects = {**bundle['objects'],**generated}.values()
    store = Store(root).extend(objects, names) if Store.is_published(root) else Store.publish(root, objects, names)
    store.refresh_index()
    report = dict(schema=1, snapshot=store.snapshot_id, laws=len(bundle['roots']), templates=len(generated), names=names)
    (Path(root) / 'store/approximation-view.json').write_bytes(canonical(store.bundle(bundle['roots'])) + b'\n')
    (Path(root) / 'store/approximation-publication.json').write_bytes(canonical(report) + b'\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', required=True)
    parser.add_argument('--output-store', required=True)
    args = parser.parse_args()
    print(json.dumps(publish(args.compiler, args.output_store)))
