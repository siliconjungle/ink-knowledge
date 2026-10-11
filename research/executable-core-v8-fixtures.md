# Replayed representation request identities

The executable-core V8 revision changes the complete module identity. Twenty
older source-bound request envelopes in source-representations, compact-queries,
cache-maintenance, point-delta and filtered-aggregate now name that identity.

Before proposing each envelope, the maintenance pass emitted the current action
model and required an identical source-definition index and byte-for-byte identical
canonical projected definitions. It then ran the independent compiler's complete
`check-representation` admission. The mathematical objects, representation IDs,
snapshot pins and membership witnesses are unchanged. This is safe proof replay
under a newly checked source binding, not permission to ignore a version change.
Changed projected definitions require new proof authoring instead.

The associated migration bundles retain the same endpoints and equations and are
replayed with `check-migration` against both current source-bound endpoints.
