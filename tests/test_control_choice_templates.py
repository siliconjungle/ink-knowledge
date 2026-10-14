import unittest
from producers.control_choice_templates import templates,concrete
from ink_knowledge import identity
class ControlChoices(unittest.TestCase):
    def test_templates_preserve_lazy_value_order_without_source_or_target_tags(self):
        rows=templates();self.assertEqual(len(rows),4)
        self.assertEqual(len({identity(r['object']) for r in rows}),4)
        for row in rows:
            p=row['object']['payload'];self.assertEqual(p['type_parameters'],['A'])
            self.assertEqual(p['dependencies'],{});self.assertEqual(p['law']['conditions'],[])
            self.assertEqual(set(p['law']['proof']),{'Cases'})
            self.assertNotIn('definition_context',p['law'])
        self.assertEqual(len(concrete()),24)
        self.assertEqual(len({identity(o) for _,o in concrete()}),24)


class CheckedControlChoices(unittest.TestCase):
    def test_concrete_templates_replay_and_false_rehashed_conclusion_is_rejected(self):
        import copy,json,os,subprocess,tempfile
        from pathlib import Path
        from ink_knowledge import Store,canonical,semantic_entry
        from producers.semantic_laws import value
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory(prefix='ink-choice-proof-test-')as temporary:
            d=Path(temporary);source=d/'source.ink';core=d/'core.json'
            source.write_text('module Choices;fn pick(flag:Bool,x:u32,y:u32)->u32{return choose(flag,x,y);}')
            run=subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],capture_output=True,text=True,timeout=60)
            self.assertEqual(run.returncode,0,run.stderr)
            def check(objects,name):
                store=Store.publish(d/name,objects);view=d/(name+'.json')
                view.write_bytes(canonical(store.bundle([identity(obj)for obj in objects])))
                return subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=60)
            objects=[obj for _,obj in concrete()]
            run=check(objects,'valid');self.assertEqual(run.returncode,0,run.stderr)
            self.assertEqual(len(json.loads(run.stdout)['entries']),24)
            original=next(obj for name,obj in concrete()if name=='same-branches/Bool')
            false=copy.deepcopy(original['payload'])
            false['to']={'sort':value('Bool'),'node':{'Bool':False}}
            # Rebuild both typed interface and identity so rejection tests the
            # false equation, rather than stale metadata or a malformed entry.
            false=semantic_entry(dict(false,semantics=original['semantics'],dependencies={}))
            run=check([false],'false');self.assertNotEqual(run.returncode,0)
            self.assertIn('semantic normal forms differ',run.stderr)
