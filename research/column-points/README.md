# Direct column point reads

`representations.py --column-points` supplies direct point search over the ordinary
key/field columns. An induction over all logical rows proves equivalence to the
source table get, including empty, duplicate and unordered rows. Per-action
observation, relation preservation, round trip and migration remain obligations
of the existing general checker. There is no sortedness premise or new kernel
rule. The authoring recogniser changes no executable authority.

Standalone query erasure removes the unused private logical-state component;
point reads then return their record without reconstructing the entire table.
Reference evaluation and mutations can still decode logical rows. Keys and row
values retain exact current source semantics. Producer support is a direct get
whose key captures no other logical root, and unsupported query shapes keep the
baseline computation. Combining packed Boolean fields is supported separately.

Reproduce from `model.json` with `--column-points`. Python regressions compare
complete requests and reauthenticate a false comparison before demanding
mathematical rejection. Forward/reverse checked migration to ordinary columns, complete native/JS/actual
Wasm parity and the residual
call graph are exercised in `tests/representation_parity.rs`.
