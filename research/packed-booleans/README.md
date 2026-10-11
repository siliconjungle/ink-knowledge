# Proved Boolean packing

`producers/representations.py --packed-booleans` combines a record's Boolean
fields into a single `u64` word column. Existing total word addition of disjoint
bit contributions and masking describe encode/decode. The producer requests
ordinary bit-vector certificates for every restored flag; Ink reconstructs and
checks those obligations inside the row/table round-trip proof. No packing rule
or storage-policy whitelist is added to the core.

The source fixture combines three Boolean flags, a full-width `u64`, signed keys
and row-valued events. All flag combinations, rollback and signed-key boundaries
are covered by compiled parity. The negative test changes a decoder bit, rehashes
the affected closure and republishes its Merkle membership. Mathematical checking
rejects the false round trip.

Packing describes the stored word exactly; columns still use inductive lists.
This is not native array storage, general word narrowing or a measured speedup.
The candidate does not become a default. `tests/test_column_layouts.py` reproduces
both frozen tuple layouts.
