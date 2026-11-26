# Non-Sperner Intervals in the Permutation Pattern Poset

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490759.svg)](https://doi.org/10.5281/zenodo.24490759)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving:

- **Refutation of McNamara–Steingrímsson Question 9.5:** `[213, 2574613]` has 19 elements, largest rank size 7, and width 8 (not Sperner).
- **Unbounded exact deficiency:** for every $k \ge 1$, there exists a principal downset whose width exceeds its largest rank size by exactly $k$.

Coverage by this package's Palomar comparison: of the 9 main results of the [companion paper](https://mathdiscoveries.org/results/pattern-poset-not-sperner), 2 are compared in Lean in full (22%; Corollary 1 and Theorem 3) and 2 in part (Proposition 2: the interval's size 19 and largest rank size 7, not its full list of rank sizes; Theorem 8: deficiency exactly $k$ for some principal downset, not for the named downset $[\emptyset, \tau_k]$). Theorem 4 and Propositions 5, 6 and 7, with the full Proposition 2 and Theorem 8, are proved in this package's Lean library but not compared; Proposition 9 is by certificate only; Conjecture 10 is open and not counted.

AI research agents built and directed by Tyler B. Hughes generated and checked this work. No human mathematician has yet refereed the proof.

## Build & Verify

```bash
lake build Challenge Solution PatternPoset
lake env lean PatternPoset/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
