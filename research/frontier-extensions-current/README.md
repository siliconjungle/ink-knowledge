# Current checked incremental state representations

These packets were regenerated against the integrated executable core and producers. Each manifest binds its exact source, model, representation requests and migration proofs. Every representation and both migration directions were checked locally.

The original `../frontier-extensions` packets remain historical evidence for their recorded compiler revision. Candidate scopes and limitations are documented in that archive’s README.

Reproduce from the distribution root:

```sh
INK_COMPILER="$PWD/target/debug/ink" python3 knowledge/producers/freeze_frontier_extensions.py --workspace "$PWD" --output-root knowledge/research/frontier-extensions-current
```
