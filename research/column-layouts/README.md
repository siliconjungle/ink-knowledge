# Ordinary column representation

`producers/representations.py --columnar` places table keys and one-constructor
record fields in separate inductive lists. Other values use a single value
column. Encode/decode round trips are proved by ordinary table induction and
record reconstruction. Empty, unordered and duplicate logical rows participate
in those proofs; equal-length columns follow from the representation relation.
Both tuple orders have initialization, snapshot and every-action obligations.

The generated transition decodes and reencodes complete source actions, except
that unchanged queries retain the physical roots. This is a checked representation
candidate, not a claim of efficient column updates, native typed arrays or SIMD.
Costs must be measured before selection. Source values and column payloads retain
their exact existing scalar meanings; numerical narrowing is not implicit.

The root parity test checks records, filtered keeps, overflow, failure, events,
restoration, a checked baseline-to-column migration and all standalone transports.
`tests/test_column_layouts.py` reproduces the frozen requests.
