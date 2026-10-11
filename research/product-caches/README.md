# Composition of independent maintained caches

Two independently admitted dynamic point caches serve `zero` and `one` on the
same source state. `producers/representation_product.py` composes their complete
physical states and universal relations. Every change executes both components;
each source action publishes exactly one chosen complete observation. The cache
for `one` supplies that query, and the first component supplies other actions.

Ordinary initialization, snapshot, observation and preservation proofs are
factored into checked lemmas. Structural projections have literal nonrecursive
bodies in the existing structural declaration form. Keeping symbolic projections
opaque bounds proof normalization; there is no new kernel reduction or admission
rule. Components need the exact common source closure and action interface. The
existing eight-relation and other checker resource limits remain in force.

`producers/representation_bridge.py --via-logical` now handles arbitrary target
relations by transporting the source snapshot equality and invoking each target
initialization proof. Frozen `forward.json` and `backward.json` bridge the first
component and the product. Migration still validates exact logical state,
portable snapshots, versions and pending events at transaction boundaries.

The product duplicates transition computation and can duplicate persistent roots.
It is a correctness and composition candidate, with no profitability claim or
automatic default selection. A later candidate can fuse shared dependencies
through further ordinary equations. Do not treat product composition itself as
common-subexpression elimination or field-sensitive invalidation.

`tests/test_product_caches.py` reproduces the frozen bytes. The root integration
test checks both migration directions, future updates and rollback, repeated
restoration, all standalone transports and a reauthenticated candidate missing
the second relation premise. Admission rejects that altered mathematics.
