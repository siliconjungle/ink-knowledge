# Persistent first-order machines

Six independently checked packages: original/alternative row, ledger and counter
representations. `tools/machine_candidates.py` builds them from ordinary library
functions and general proof terms. `ink emit-machine LOCK MACHINE -o SOURCE.rs`
checks actual initialisation, state relations, future-operation preservation,
reply/query agreement and logical snapshots before emitting a private-state API.

The counter specifies wrapping counts, abort priority, commit exhaustion and
ordered committed events. Rows/ledger reuse the existing column mathematics.
These packages are total-value sequential models; they do not certify actual Ink
source actions, physical flat storage, host allocation failures, durable recovery,
concurrency or speed. The emitted boxed Rust protocol/codecs and Rust/LLVM are trusted.
