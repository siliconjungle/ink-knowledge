# Source-bound cache maintenance

The same unchanged `app.ink` underlies three requests: `direct.json` stores its
two tables; `refresh.json` caches `zero` but refreshes it after every change;
`preserve.json` retains the cached value after aborts or host failures and carries
the cached reply through successful writes to `Z`. Writes to `Rows` still refresh
it. Ordinary queries retain physical state in both cached candidates.

The producer is `producers/representations.py --cache-query zero --preserve-cache`.
`producers/cache_maintenance.py` conservatively examines the query's table-root
variables and the committed post-state of each action branch. This proposes work
skipping; it grants no authority. Existing `Induction`, `BoolSplit`, `Substitute`
and definitional equality prove the complete equation on all branches and every
logical state, version and argument. Every source action still needs observation
and preservation proofs. No source syntax, core kernel, runtime or native backend
change is required. The candidate composes with checked whole-action replacements.

The authoring example supports constructor/If observation cases, bounded to 256
nodes. Unsupported authoring cases fail rather than publishing an unchecked
candidate. Admission remains the general representation contract; another
producer can supply different algorithms and proofs. This work skips unnecessary
refresh, but does not implement key-level delta maintenance or a durable database
log. Native full-state transport remains linear in table size.

Requests carry canonical objects and authenticated membership from their pinned
snapshots.
Current catalogue details are recorded below; previous snapshots and requests remain
replayable. SQLite is a disposable discovery index. Correctness is independent
of measured profitability; retain `refresh.json` for target/workload comparisons.
The distribution's `reports/cache-maintenance-performance` archives measurements.

From ink-lang:

```sh
ink check-representation knowledge/research/cache-maintenance/app.ink \
  knowledge/research/cache-maintenance/preserve.json
ink check-migration knowledge/research/cache-maintenance/app.ink \
  knowledge/research/cache-maintenance/direct.json \
  knowledge/research/cache-maintenance/preserve.json \
  knowledge/research/cache-maintenance/migration.json
ink execute-representation knowledge/research/cache-maintenance/app.ink \
  knowledge/research/cache-maintenance/preserve.json \
  knowledge/research/cache-maintenance/calls.json
```

`migration.json` converts the direct representation to the preserved cache at a
transaction boundary. Portable logical snapshots allow restore in either cached
candidate and generic migration between them. Calls cover inserts, cache reads,
an unrelated committed write, rollback after staged deletion/emission, and a
successful deletion that must invalidate the cache. Compiler tests also compare
reference, native fused and native three-call execution, exhausted versions,
exact replies/events/snapshots and a well-hashed false unchanged-root proof.

The intermediate carrier contains only the cached reply and the complete source
observation. Source post-state already supplies the logical roots for rebuilding
the physical tuple, including rollback and host-failure paths. Carrying the whole
previous physical state duplicated roots across native transport without changing
meaning; `whole-state.json` and `whole-state-migration.json` retain that checked
experiment for replay and cost comparison. The producer now emits the compact
carrier with `--preserve-cache`. The earlier candidate's core proofs remain valid;
its whole-state transport cost makes it unsuitable for automatic selection.

`composed.json` combines compact cache retention with the canonical complete-action
removal-idempotence law. It has its own `composed-direct.json` and
`composed-migration.json` endpoints. The original source still removes twice;
the selected database function removes once, with universal equality to the
complete original action, including rollback and events. The compact candidate
alone showed no consistent total-call gain; composition reduced 48-row aborted
native erase latency by about 5.7% in the distribution's small-fixture report.
Selection remains explicit because other actions/executors did not consistently
benefit. Correctness proof bytes do not include these measurements as premises.

The current store contains 822 entries under snapshot
`787ae018df2a0de6d4eec1d46c7f9d1acd14157792e5a74637f06998785fc0f2`. Earlier fixture snapshots and requests remain immutable and
replayable. `refresh.json` supplies the comparison candidate in both experiments.
