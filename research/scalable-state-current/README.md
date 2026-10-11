# Current scalable-state proof packets

Bulk maintenance and membership-cache requests were regenerated and checked against the integrated core. Source bytes match the historical fixtures. Original packets in `../bulk-maintenance` and `../membership-cache` remain historical evidence for their recorded compiler revision.

Reproduce and check exact request bytes from the distribution root:

```sh
python3 tools/reproduce_scalable_knowledge.py --candidate-root knowledge/research/scalable-state-current
```
