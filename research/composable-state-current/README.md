# Current composed-state admission

These fixtures and twenty published choices are independently checked against the integrated compiler source identities. Historical packets and their original measurements remain under `../composable-state` and keep their recorded source/compiler bindings.

From the distribution root, run `bench/composable-state/prepare-fixtures.py`, `publish-current.py`, then `replay-admissions.py`, each with `--compiler target/debug/ink`. The replay additionally takes `--mathematics-source source-group examples/grouped-state.ink`. Proof authoring uses `python-sat==1.9.dev5`; the general kernel checks the proposed certificates.

Admissions cover exact observations, state relations and migration preservation. Profitability, codecs, native emission and host behavior remain separate obligations.
