# Ink knowledge

The independently versioned proof catalogue and untrusted proof producers for
[Ink](https://github.com/siliconjungle/ink-lang). The compiler and its general
checking rules live in `ink-lang`; this repository supplies mathematical
definitions, theorems, proof certificates and candidate implementations.

The JSON format is the current storage backend. A future database or index must
preserve the checked object identities and explicitly pinned dependencies.
Changing storage does not change what is trusted.

## Use

```sh
git clone https://github.com/siliconjungle/ink-knowledge.git
python3 ink-knowledge/tools/catalogue.py list
/path/to/ink verify-library ink-knowledge/source-search-layout/lock.json
/path/to/ink build program.ink --implementation ink-knowledge/filtered/proposal.json -o program.o
```

With a compiler supporting `ink-executable-core-v1`, pin both the executable
program and the exact proof-library lock before admission:

```sh
python3 ink-knowledge/tools/replacement_package.py \
  ink-knowledge/filtered/kernels.lang ink-knowledge/filtered/proposal.json \
  --compiler /path/to/ink --output-dir /tmp/ink-replacement
/path/to/ink build /tmp/ink-replacement/core.json --core \
  --replacement /tmp/ink-replacement/replacement.json -o program.o
```

The producer requires an empty output directory, copies immutable proof bytes,
and asks the unchanged compiler to check the result. It is untrusted tooling.
The current observation domain is pure total-value equality; this envelope
does not authorise stateful migration, event changes or allocation-failure claims.

`ink-lang` pins a commit of this repository as its `knowledge` submodule for
integration tests and reproducible experiments. An installed compiler accepts
explicit external package paths and does not fetch the latest catalogue.

## Discovery and checking

`catalogue.json` lists the primary proof-library locks, their byte identities,
semantics versions and checking commands. It is generated discovery metadata,
not a proof or a complete list of every candidate or legacy certificate.

```sh
python3 tools/catalogue.py check
python3 tools/catalogue.py verify --compiler /path/to/ink
python3 tools/catalogue.py rebuild
```

The checker reloads and validates selected proof objects, including dependency
closure and content hashes. A valid lock hash alone does not establish theorem
validity or correspondence to native code. Changing a lock requires regenerating
the index and explicitly updating consumers' pinned revision.

## Produce proofs

Python 3 is needed for producers; the bitvector-based producers additionally
need `python-sat`. Production tools are outside the trusted compiler.

```sh
python3 tools/boolean_proofs.py boolean-rules.json /tmp/boolean-package
INK_COMPILER=/path/to/ink INK_CORE_ROOT=/path/to/ink-lang \
  python3 tools/search_layout_proofs.py /tmp/search-package \
  --sorted source-sorted-layout --source /path/to/ink-lang/examples/source-row-undo.ink
```

Use explicit `--compiler`, `--maintenance` and other input arguments to reproduce
historical experiments. `INK_COMPILER` overrides default compiler locations;
`INK_CORE_ROOT` locates source examples and preserved compiler artifacts. When
checked out as Ink's submodule, the core root is detected automatically.

`proofs/` contains separately authored Lean research. Lean proofs are not
automatically imported as Ink optimisation authority. Ink currently has its own
restricted Rust checker; neither that implementation nor native lowering has
an end-to-end formal correctness proof.

The catalogue history was extracted from `ink-lang` through commit `c1b4035`.
Original object bytes and package files are preserved. Proof producers were
moved from that compiler revision with path configuration changes.

## Bounded rewrite search

```sh
python3 tools/rewrite_search.py rewrite-search/kernels.ink \
  --rules bitvector/rewrite-index.json --compiler /path/to/ink \
  --output-dir /tmp/ink-search --budget 10000
```

The rule index is untrusted discovery/selection data. The producer reads theorem
endpoints from the pinned library and constructs complete congruence/induction
proofs; the compiler checks them independently. No SAT solver is needed when
reusing these existing certificates. Search handles scalars and single mapped
sums. `--fuse-mapped-sum` adds a fold candidate with an explicit induction proof.
Unsupported structures, insufficient budget and square factoring retain the
original implementation. A node-count estimate chooses smaller expressions;
it is not a performance measurement. `rewrite-search/` is a reproducible example
with lexical shadowing and a deliberately unproved factoring case.

## Extension contract

New knowledge must use the fixed checking rules. Packages cannot install an
axiom, trust flag or new kernel rule. See [the compiler boundary](https://github.com/siliconjungle/ink-lang/blob/main/docs/small-core-and-knowledge.md).

The production package interface will add typed applicability conditions,
representation relations, initialisation/migration candidates and separate
target-specific cost evidence. Those interfaces are planned, not implemented
by this repository split. Existing mathematical layout proofs do not yet
authorise native stateful representation replacement.
