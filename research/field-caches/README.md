# Exact mapped point caches

`source.ink` reads one field of a record through the existing Option mapper.
`mapped.json` retains only the projected Option in its cache. Ordinary Option
induction and conditional congruence lift the point-update equations without a
new proof rule or trusted dependency declaration. Same-key insertion still uses
exact refresh; replacement extracts the field from the new row. All inductive
table inputs are covered, including unsorted/duplicate rows.

`direct.json`, `mapped.json` and `migration.json` are source-bound candidates and
an exact checked bridge. `model.json` is their fixed source correspondence input.
The source exercises unrelated keys and unread fields, captured query arguments,
abort, record-valued events, absent reads and wrapping word values. CPU and actual
Rust/C Wasm histories are checked by `mapped_point_caches_preserve_record_fields_and_complete_histories`.

Reproduction and an authenticated wrong-field control are in
`tests/test_field_caches.py`. The producer rejects mappers that capture extra
state. This is not general dependency fusion or evidence of profitability; no
candidate becomes a default merely by passing admission.
