"""Regression cases for the disposable pattern index's public query boundary."""
import sqlite3
from contextlib import closing
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from ink_knowledge.pattern_index import Reader, candidates


class PatternReaderBoundary(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.index=self.root/'index.sqlite'
        self.store=SimpleNamespace(root=self.root,snapshot_id='snapshot')
        with closing(sqlite3.connect(self.index)) as db, db:
            db.executescript('CREATE TABLE pattern_roots(entry_id TEXT,sort TEXT,head TEXT);'
                'CREATE TABLE pattern_targets(entry_id TEXT,sort TEXT,head TEXT);'
                'CREATE TABLE snapshots(id TEXT);CREATE TABLE members(entry_id TEXT,snapshot_id TEXT);')
            db.execute('INSERT INTO snapshots VALUES(?)',(self.store.snapshot_id,))
            ids=[f'{n:064x}'for n in range(1050)]
            db.executemany('INSERT INTO pattern_roots VALUES(?,?,?)',[(i,'{"Value":"U32"}','Op:binary:+')for i in ids])
            db.executemany('INSERT INTO members VALUES(?,?)',[(i,self.store.snapshot_id)for i in ids])
        self.sort={'Value':'U32'};self.head='Op:binary:+'

    def test_both_indexed_apis_enforce_the_store_page_budget(self):
        with Reader(self.store)as reader:
            calls=[lambda **kw:candidates(self.store,self.sort,self.head,**kw),
                   lambda **kw:reader.candidates(self.sort,self.head,**kw)]
            for call in calls:
                for limit in [-1,1025,1.5,'1',None]:
                    with self.subTest(limit=limit),self.assertRaisesRegex(ValueError,'query limit'):
                        call(limit=limit)
                for limit in [0,1,1024]:self.assertEqual(len(call(limit=limit)),limit)
                page=call(limit=1024);tail=call(limit=1024,after=page[-1])
                self.assertEqual(len(tail),26);self.assertFalse(set(page)&set(tail))

    def test_entry_failure_closes_the_actual_connection(self):
        self.index.write_bytes(b'not a sqlite database')
        opened=[];connect=sqlite3.connect
        def record(*args,**kwargs):
            db=connect(*args,**kwargs);opened.append(db);return db
        with patch('ink_knowledge.pattern_index.sqlite3.connect',side_effect=record):
            with self.assertRaises(sqlite3.DatabaseError):
                Reader(self.store).__enter__()
        self.assertEqual(len(opened),1)
        with self.assertRaises(sqlite3.ProgrammingError):opened[0].execute('SELECT 1')

    def test_exit_clears_closed_handle_and_allows_fresh_entry(self):
        reader=Reader(self.store)
        with reader:
            first=reader.db;self.assertEqual(len(reader.candidates(self.sort,self.head,limit=1)),1)
        self.assertIsNone(reader.db)
        with self.assertRaises(sqlite3.ProgrammingError):first.execute('SELECT 1')
        with self.assertRaisesRegex(RuntimeError,'fixture'):
            with reader:
                second=reader.db;self.assertIsNot(second,first)
                raise RuntimeError('fixture')
        self.assertIsNone(reader.db)
        with self.assertRaises(sqlite3.ProgrammingError):second.execute('SELECT 1')

    def test_invalid_limit_is_rejected_before_fallback_or_connect(self):
        self.index.unlink()
        self.store.query=lambda **kwargs:self.fail('invalid page reached fallback')
        with patch('ink_knowledge.pattern_index.sqlite3.connect',side_effect=AssertionError('unexpected connect')):
            with self.assertRaisesRegex(ValueError,'query limit'):candidates(self.store,self.sort,self.head,limit=-1)
            with Reader(self.store)as reader:
                with self.assertRaisesRegex(ValueError,'query limit'):reader.candidates(self.sort,self.head,limit=-1)


if __name__=='__main__':unittest.main()
