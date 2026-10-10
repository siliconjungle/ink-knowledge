# Effect-prefix composition

Eleven checked definitions/theorems describe the fixed finite prefix algebra:
outer value/exit shapes, write/event flags, sequencing, Boolean prefix combination,
associativity, empty-prefix identity and abrupt suffix suppression. They use
Ink's unchanged general first-order equality kernel. No rule or resource limit
was added. `producers/effect_composition_proofs.py` regenerates the research
objects; `producers/build_store.py` imports individual canonical entries.

The source compiler binds the definitions to `effects::Path::follow` through
`effect_model::BoundEffects`. The immutable binding records an actual checked
effect artifact identity. This is composition algebra, not a proof that abstract
source analysis is sound, that actions denote a complete transition function, or
that native rollback/storage is refined. It enables no stateful replacement or
journal shortcut and makes no performance claim.
