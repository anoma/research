# Recursive proofs

This repository contains some files for playing with two different
proof schemes called IPA (inner product argument) and PB
(pairing-based).

This is still a work in progress.

We compare the cost of the PB scheme using different curves,
corresponding to the case of recursive proofs (where a cycle of curves
is needed):
```python3
sage bench_pb.py
```

We also provide some code for playing with the IPA commitment scheme:
```python3
sage bench_ipa.py
```
