# Non-Sperner Intervals in the Permutation Pattern Poset

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490759.svg)](https://doi.org/10.5281/zenodo.24490759)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving:

- **Refutation of McNamara–Steingrímsson Question 9.5:** `[213, 2574613]` has 19 elements, largest rank size 7, and width 8 (not Sperner).
- **Unbounded exact deficiency:** for every $k \ge 1$, there exists a principal downset whose width exceeds its largest rank size by exactly $k$.

## Build & Verify

```bash
lake build Challenge Solution PatternPoset
lake env lean PatternPoset/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
