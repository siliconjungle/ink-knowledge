"""Replay generic branch proofs and normal producer composition."""
import copy
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from ink_knowledge import Store, canonical, entry, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.recipes import execute, load
from producers.guarded_choices import choice_rule, guard_entry, guarded_rows, list_guard, propose
from producers.semantic_laws import law, value, var

ROOT = Path(__file__).resolve().parents[2]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT / 'target/debug/ink')).resolve()


class GuardedChoices(unittest.TestCase):
    def compiler(self, *args, success=True):
        result = subprocess.run([str(COMPILER), *map(str, args)], capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout[-1000:] + result.stderr[-3000:])
        return result

    def context(self, directory, source):
        path = directory / 'source.ink'
        path.write_text(source)
        self.compiler('emit-core', path, '-o', directory / 'core.json')
        core = json.loads((directory / 'core.json').read_bytes())
        source_id = json.loads(self.compiler('check-core', directory / 'core.json').stdout)['core_sha256']
        store = Store.publish(directory / 'knowledge', [])
        return store, dict(core=core, source=source_id, compiler=str(COMPILER), knowledge_root=str(store.root),
                          knowledge_snapshot=store.snapshot_id, check_timeout=120)

    def check(self, d, context, row, name, success=True):
        package = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=context['source'], steps=row['steps'])
        path = d / (name + '.json')
        path.write_bytes(canonical(package))
        self.compiler('check-plan', d / 'core.json', path, '--core', '--target', 'javascript', success=success)
        if success:
            self.compiler('emit-plan', d / 'core.json', path, '--core', '--target', 'javascript', '-o', d / (name + '.mjs'))

    def node(self, d, text):
        (d / 'check.mjs').write_text(text)
        result = subprocess.run(['node', str(d / 'check.mjs')], capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_registry_composes_source_extension_and_all_cutoffs(self):
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            store, context = self.context(d, '''module wide;
fn run(xs:List<u64>)->List<u64>{return foldl(xs,[],fn(item,out)=>
 choose(foldl(out,false,fn(key,seen)=>seen||key==item),out,out.concat([item])));}
''')
            registry, _ = load(store=store)
            for cutoff in (8, 128, 2048):
                recipe = next(r for r in registry['recipes'] if r['id'] == f'guarded-whole-call-{cutoff}')
                rows = list(execute(recipe, context))
                proposals = [r for r in rows if r['status'] == 'proposal']
                self.assertEqual(len(proposals), 1, rows)
                row = proposals[0]
                self.assertEqual([s['kind'] for s in row['steps']], ['extension', 'rewrite'])
                self.check(d, context, row, f'guarded-{cutoff}')
            self.node(d, '''import assert from 'node:assert/strict';
for(const cutoff of [8,128,2048]){
 const m=await import(`./guarded-${cutoff}.mjs`);
 for(const n of [0,1,cutoff-1,cutoff,cutoff+1])for(const reverse of [false,true]){
  const xs=Array.from({length:n},(_,i)=>[0n,1n,18446744073709551615n,9007199254740993n][i%4]);
  if(reverse)xs.reverse();const before=xs.slice();
  assert.deepEqual(m.call('run',[xs]),[...new Set(xs)]);assert.deepEqual(xs,before);
 }
}''')
            self.assertEqual(Store(store.root).snapshot_id, context['knowledge_snapshot'])

    def test_unrelated_list_law_and_changed_fallback_rejected(self):
        # No membership, map, buffer, source extension or word key is involved.
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            store, context = self.context(d, 'module simple; fn run(xs:List<Bool>)->List<Bool>{return xs.concat([]);}')
            self.compiler('emit-semantic', d / 'core.json', '--core', '-o', d / 'semantic.json')
            body = json.loads((d / 'semantic.json').read_bytes())['functions']['run']
            sort = value({'List': 'Bool'})
            obj = semantic_entry(law({'xs': sort}, body, var(sort, 'xs'),
                {'Induction': dict(variable='xs', names=['head', 'tail'], base='Normalize', step='Normalize')}))
            ident = identity(obj)
            packet = dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=context['source'],
                knowledge=ProposalViews(store, {ident: obj}, d / 'original').bundle([ident]),
                applications=[dict(function='run', path=[], law=ident, arguments={'xs': var(sort, 'xs')}, premises=[])])
            original = dict(status='proposal', label='append-empty', steps=[dict(kind='rewrite', package=packet)])
            rows = list(guarded_rows(original, store, d / 'guarded', 8))
            self.assertEqual(len(rows), 1)
            single = dict(status='proposal', label=original['label'], step=original['steps'][0])
            self.assertEqual(list(guarded_rows(single, store, d / 'single', 8)), rows)
            self.check(d, context, rows[0], 'guarded')
            bad_rule = copy.deepcopy(choice_rule())
            bad_rule['payload']['conditions'] = []
            bad_rule['interface']['conditions'] = []
            # A valid content hash and membership witness cannot substitute for
            # the missing equality premise in this database-authored theorem.
            bad_store = store.extend([bad_rule])
            loaded = choice_rule(bad_store, identity(bad_rule))
            bad_rows = list(guarded_rows(original, bad_store, d / 'false-rule', 8, loaded))
            self.check(d, context, bad_rows[0], 'false-rule', success=False)
            self.node(d, '''import assert from 'node:assert/strict';import * as m from './guarded.mjs';
for(const n of [0,1,7,8,9]){const xs=Array.from({length:n},(_,i)=>!!(i%2));
 const before=xs.slice();assert.deepEqual(m.call('run',[xs]),xs);assert.deepEqual(xs,before);}''')
            bad = copy.deepcopy(rows[0])
            p = bad['steps'][-1]['package']
            objects = dict(p['knowledge']['objects'])
            old = objects[p['applications'][0]['law']]
            authored = dict(schema=1, semantics=old['semantics'], dependencies=old['dependencies'], **copy.deepcopy(old['payload']))
            authored['to']['node']['Op'][1][2] = dict(sort=sort, node='Nil')
            changed = semantic_entry(authored)
            new = identity(changed)
            p['knowledge'] = ProposalViews(store, {**objects, new: changed}, d / 'bad').bundle([new])
            p['applications'][0]['law'] = new
            self.check(d, context, bad, 'bad', success=False)
            # Guarding an already guarded source is bounded out, regardless of names.
            guarded_law = old['payload']
            self.assertNotEqual(guarded_law['from'], guarded_law['to'])
            next_obj = semantic_entry(law({'xs': sort}, guarded_law['to'], var(sort, 'xs')))
            next_id = identity(next_obj)
            p['knowledge'] = ProposalViews(store, {next_id: next_obj}, d / 'nested').bundle([next_id])
            p['applications'][0]['law'] = next_id
            self.assertEqual(list(guarded_rows(bad, store, d / 'nested-output', 128)), [])

    def test_undischarged_laws_and_invalid_budgets_decline(self):
        sort = value({'List': 'Bool'})
        xs = var(sort, 'xs')
        condition = list_guard('xs', sort, 8)
        for field in ('types', 'assumptions'):
            obj = semantic_entry(law({'xs': sort}, xs, xs))
            # The helper must reject these before handing anything to the checker.
            obj['payload'][field] = ['unresolved']
            with self.assertRaisesRegex(ValueError, 'instantiate'):
                guard_entry(identity(obj), obj, condition)
        for cutoff in (True, 0, -1, 1_000_000_001, 1.5):
            with self.assertRaises(ValueError):
                list_guard('xs', sort, cutoff)
        with self.assertRaises(ValueError):
            list_guard('xs', value('U32'), 8)
        with self.assertRaisesRegex(ValueError, 'recursive'):
            list(propose({'_guarded_choice_active': True}, ['anything'], 8))

    def test_conditional_rewrite_keeps_its_premise_obligation(self):
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            store, context = self.context(d, 'module conditional; fn run(xs:List<Bool>)->List<Bool>{return xs;}')
            sort = value({'List': 'Bool'})
            xs, ys = var(sort, 'xs'), var(sort, 'ys')
            condition = {'from': xs, 'to': ys}
            obj = semantic_entry(law({'xs': sort, 'ys': sort}, xs, ys, {'Hypothesis': 0}, conditions=[condition]))
            ident = identity(obj)
            packet = dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=context['source'],
                knowledge=ProposalViews(store, {ident: obj}, d / 'original').bundle([ident]),
                applications=[dict(function='run', path=[], law=ident, arguments={'xs': xs, 'ys': xs}, premises=['Normalize'])])
            original = dict(status='proposal', label='conditional-equality', step=dict(kind='rewrite', package=packet))
            rows = list(guarded_rows(original, store, d / 'guarded', 8))
            self.assertEqual(len(rows), 2)
            for i, row in enumerate(rows):
                p = row['steps'][-1]['package']
                a = p['applications'][0]
                self.assertEqual(p['knowledge']['objects'][a['law']]['payload']['conditions'], [condition])
                self.assertEqual(a['premises'], ['Normalize'])
                self.check(d, context, row, 'conditional-' + str(i))
                # The fallback is safe, but cannot justify the selected branch
                # when the required input equality has not been established.
                bad = copy.deepcopy(row)
                bad['steps'][-1]['package']['applications'][0]['arguments']['ys'] = dict(sort=sort, node='Nil')
                self.check(d, context, bad, 'false-premise-' + str(i), success=False)

    def test_base_recipe_comes_from_the_pinned_snapshot(self):
        with tempfile.TemporaryDirectory() as temporary:
            registry, _ = load()
            base = copy.deepcopy(next(r for r in registry['recipes'] if r['id'] == 'indexed-ordered-dedup'))
            base['parameters']['limit'] = 0
            store = Store.publish(temporary, [entry('definition', 'ink-planning-recipes-v1', dict(recipe=base))])
            context = dict(knowledge_root=temporary, knowledge_snapshot=store.snapshot_id, core={})
            # The resource default would access core.program; this snapshot's
            # override declines before doing that, and must be honoured.
            self.assertEqual(list(propose(context, [base['id']], 8)), [])
            recursive = dict(base, id='recursive-alias', module='producers.guarded_choices')
            newer = store.extend([entry('definition', 'ink-planning-recipes-v1', dict(recipe=recursive))])
            with self.assertRaises(KeyError):
                list(propose(context, ['recursive-alias'], 8))
            context['knowledge_snapshot'] = newer.snapshot_id
            with self.assertRaisesRegex(ValueError, 'recursive'):
                list(propose(context, ['recursive-alias'], 8))


if __name__ == '__main__':
    unittest.main()
