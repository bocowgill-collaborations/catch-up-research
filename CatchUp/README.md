# Lean library

The parent directory is a Lake package pinned to **Lean 4.27.0** and Mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`. Start with the [results guide](../results/) or [module index](../results/modules.md).

From the repository root, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 computation/check_semantics.py
python3 scripts/check_collection.py
lake env lean --run computation/CheckEarlier.lean
```

The default build imports all 110 mathematics modules. The binary machine lives in a [separate package](../cryptid/) with its original Lean version; do not combine the two packages' import paths or compiled files.

`Reference.lean` retains the reference game definitions and adds the strategy/reduction API from the existing research. The upstream unfinished conjecture is omitted. See [provenance and fidelity checks](../verification/).
