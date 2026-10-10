# Parametric table-removal law

The four entries define an abstract row sort, a u64-keyed row list, removal of
all matching keys, and remove idempotence. The theorem is proved once by
induction and explicit Boolean-condition substitution. The closed application
uses `Instance` to interpret the row sort and match the exact source-bound table
and removal definitions. It carries no assumption and does no per-program
induction.

Canonical roles are stable across all supported row sorts. Reproduce the library
with `python3 producers/action_laws.py /tmp/action-laws --compiler /path/to/ink`.
The shared store imports these mathematical entries through `build_store.py`.
The source-bound transition projection separately establishes application
correspondence for its documented subset. Ordered unique table inhabitants are
the reference/native domain; the stronger deletion law holds over every list.
Native code, toolchains and the Rust projection remain trusted. This is not
whole-language or physical-representation refinement.
