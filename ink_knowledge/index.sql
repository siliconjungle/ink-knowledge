-- Disposable discovery/cache schema v2. Rebuilt from canonical Git objects.
-- Proof authority stays in the semantic core, including for cached witnesses.
PRAGMA foreign_keys = ON;

CREATE TABLE snapshots (
    id TEXT PRIMARY KEY,
    root TEXT NOT NULL,
    touched INTEGER NOT NULL DEFAULT 0
) STRICT;

CREATE TABLE entries (
    id TEXT PRIMARY KEY,
    kind TEXT NOT NULL CHECK (kind IN (
        'definition', 'theorem', 'rewrite', 'implementation',
        'representation', 'maintenance', 'bridge'
    )),
    semantics TEXT NOT NULL,
    result TEXT NOT NULL CHECK (json_valid(result)),
    parameters TEXT NOT NULL CHECK (json_valid(parameters)),
    conditions TEXT NOT NULL CHECK (json_valid(conditions))
) STRICT;
CREATE INDEX entry_lookup ON entries (semantics, kind, result);
CREATE INDEX entry_kind_lookup ON entries (kind, id);

CREATE TABLE witnesses (
    id TEXT PRIMARY KEY,
    witness TEXT NOT NULL CHECK(json_valid(witness))
) STRICT;

CREATE TABLE members (
    snapshot_id TEXT REFERENCES snapshots (id),
    entry_id TEXT REFERENCES entries (id),
    witness_id TEXT NOT NULL REFERENCES witnesses(id),
    PRIMARY KEY (snapshot_id, entry_id)
) STRICT;

CREATE INDEX membership_witness_lookup ON members(witness_id);
CREATE INDEX membership_entry_lookup ON members(entry_id,snapshot_id);

CREATE TABLE dependencies (
    entry_id TEXT REFERENCES entries (id),
    dependency_id TEXT REFERENCES entries (id) DEFERRABLE INITIALLY DEFERRED,
    PRIMARY KEY (entry_id, dependency_id)
) STRICT;
-- Deferred parent insertion checks need the reverse edge too. Without this
-- index each newly inserted proof may scan the complete dependency relation.
CREATE INDEX dependency_parent_lookup ON dependencies(dependency_id,entry_id);

CREATE TABLE types (
    entry_id TEXT REFERENCES entries (id),
    role TEXT CHECK (role IN ('parameter', 'result')),
    name TEXT,
    type TEXT NOT NULL CHECK (json_valid(type)),
    PRIMARY KEY (entry_id, role, name)
) STRICT;
CREATE INDEX types_lookup ON types (type, role, entry_id);

CREATE TABLE operations (
    entry_id TEXT REFERENCES entries (id),
    operation TEXT,
    PRIMARY KEY (entry_id, operation)
) STRICT;
CREATE INDEX operations_lookup ON operations (operation, entry_id);

CREATE TABLE effects (
    entry_id TEXT REFERENCES entries (id),
    effect TEXT,
    PRIMARY KEY (entry_id, effect)
) STRICT;
CREATE INDEX effects_lookup ON effects (effect, entry_id);

CREATE TABLE applicability (
    entry_id TEXT REFERENCES entries (id),
    position INTEGER CHECK (position >= 0),
    condition TEXT NOT NULL CHECK (json_valid(condition)),
    PRIMARY KEY (entry_id, position)
) STRICT;
CREATE INDEX applicability_lookup ON applicability (condition, entry_id);

CREATE TABLE names (
    name TEXT PRIMARY KEY,
    entry_id TEXT NOT NULL REFERENCES entries (id)
) STRICT;

-- Observation references are intentionally independent of the selected snapshot.
-- Costs never establish a proof premise or change mathematical membership.
CREATE TABLE observations (
    id TEXT PRIMARY KEY,
    program_id TEXT NOT NULL,
    plan_id TEXT NOT NULL,
    target TEXT NOT NULL CHECK (json_valid(target)),
    workload TEXT NOT NULL CHECK (json_valid(workload)),
    metrics TEXT NOT NULL CHECK (json_valid(metrics))
) STRICT;
CREATE INDEX observation_lookup ON observations (program_id, plan_id, target, workload, id);

-- Typed pattern heads are disposable discovery metadata, never proof authority.
CREATE TABLE pattern_roots (
    entry_id TEXT PRIMARY KEY REFERENCES entries(id),
    sort TEXT NOT NULL CHECK(json_valid(sort)),
    head TEXT NOT NULL
) STRICT;
CREATE INDEX pattern_root_lookup ON pattern_roots(sort,head,entry_id);
CREATE TABLE pattern_targets (
    entry_id TEXT REFERENCES entries(id),
    sort TEXT NOT NULL CHECK(json_valid(sort)),
    head TEXT NOT NULL,
    PRIMARY KEY(entry_id,sort,head)
) STRICT;

-- Disposable template index projection; canonical bytes remain authoritative.
CREATE TABLE IF NOT EXISTS template_heads(
 entry_id TEXT PRIMARY KEY REFERENCES entries(id), head TEXT NOT NULL) STRICT;
CREATE INDEX IF NOT EXISTS template_head_lookup ON template_heads(head,entry_id);
CREATE TABLE IF NOT EXISTS template_tokens(
 entry_id TEXT REFERENCES entries(id), path TEXT NOT NULL, token TEXT NOT NULL,
 PRIMARY KEY(entry_id,path)) STRICT;
CREATE INDEX IF NOT EXISTS template_token_lookup ON template_tokens(path,token,entry_id);

-- Disposable family evidence projection; canonical bytes remain authoritative.
CREATE TABLE IF NOT EXISTS observation_entries(
 observation_id TEXT REFERENCES observations(id), entry_id TEXT NOT NULL,
 PRIMARY KEY(observation_id,entry_id)) STRICT;
CREATE INDEX IF NOT EXISTS observation_entry_lookup ON observation_entries(entry_id,observation_id);
CREATE TABLE IF NOT EXISTS observation_attribution(id TEXT PRIMARY KEY REFERENCES observations(id)) STRICT;
