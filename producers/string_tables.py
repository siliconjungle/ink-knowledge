"""Propose source String-key table storage; admission is not profitability.

The backend owns the fixed null-prototype storage contract. This producer chooses
sites and preserves existing physical choices; it recognises no application.
"""
import json
import tempfile
from pathlib import Path
from producers.physical_capabilities import base, invoke, write


def candidates(context, groupings=('individual', 'all')):
    if context.get('representation') or context.get('emit_target') != 'javascript':
        yield dict(status='declined', label='string-tables', reason='requires source JavaScript storage')
        return
    roots = sorted(s['name'] for s in context['core']['program']['states']
                   if isinstance(s['ty'], dict) and s['ty'].get('Table', [None])[0] == 'String')
    if not roots:
        return
    with tempfile.TemporaryDirectory(prefix='ink-string-tables-') as temporary:
        directory = Path(temporary)
        source = write(directory / 'core.json', context['core'])
        physical = context.get('physical')
        if physical is None:
            subjects = directory / 'subjects.json'
            invoke(context['compiler'], 'emit-bounds-obligations', source, '--core', '-o', subjects)
            physical = base(json.loads(subjects.read_bytes())['source'])
        existing = set(physical.get('dictionary_tables', []))
        groups = [('root/' + name, [name]) for name in roots] if 'individual' in groupings else []
        if 'all' in groupings:
            groups.append(('all', roots))
        for label, additions in groups:
            selected = existing | set(additions)
            if selected == existing:
                continue
            plan = json.loads(json.dumps(physical))
            plan['dictionary_tables'] = sorted(selected)
            invoke(context['compiler'], 'check-physical-plan', source, write(directory / 'physical.json', plan), '--core')
            yield dict(status='proposal', label='string-tables/' + label, step=dict(kind='physical', package=plan))
