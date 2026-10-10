# Change boundary laws

Six definitions/theorems describe the existing total commit decision: domain
errors roll back before considering exhaustion; successful changes advance one
version or exhaust at the maximum word. The guarded commit theorem has an
explicit non-exhaustion premise. `producers/transaction_boundary_proofs.py`
reproduces the objects; canonical entries are the production storage interface.

The language's `transaction_model::BoundChange` checks these exact definitions
against its shared executable boundary primitives. Names and hashes alone do
not bind meanings. This is only the boundary decision: neither an action-body
proof nor physical rollback, event payload, snapshot or native-code refinement.
It enables no optimisation and has no timing claim.
