module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Hom.Basic

/-!
# Palomar Challenge: Non-Sperner Intervals and Unbounded Deficiency in the Permutation Pattern Poset

Refutes McNamara and Steingrímsson's Question 9.5 (2015) by exhibiting a
length-7 closed interval `[σ, τ]` in the permutation pattern poset with 19
elements, largest rank size 7, and width 8 (hence not Sperner), and proves
that for every `k ≥ 1` there is a principal downset `[∅, τ]` whose width
exceeds its largest rank size by exactly `k`.
-/

@[expose] public section

namespace PatternPosetChallenge

structure Perm where
  len : ℕ
  perm : Equiv.Perm (Fin len)

def Contains (σ τ : Perm) : Prop :=
  ∃ f : Fin σ.len ↪o Fin τ.len,
    ∀ i j : Fin σ.len, σ.perm i < σ.perm j ↔ τ.perm (f i) < τ.perm (f j)

def IsAntichain (A : Finset Perm) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, Contains x y → x = y

def RankLevel (S : Finset Perm) (r : ℕ) : Finset Perm :=
  S.filter (fun π => π.len = r)

def largestRank (S : Finset Perm) : ℕ :=
  (S.image Perm.len).sup (fun r => (RankLevel S r).card)

noncomputable def width (S : Finset Perm) : ℕ :=
  letI := Classical.decPred IsAntichain
  (S.powerset.filter IsAntichain).sup Finset.card

def IsSperner (S : Finset Perm) : Prop :=
  width S = largestRank S

/-- Refutation of McNamara–Steingrímsson Question 9.5: there exists a closed
interval `[σ, τ]` in the permutation pattern poset with 19 elements, largest
rank size 7, and width 8 (not Sperner). -/
theorem mcnamara_steingrimsson_Q9_5_false :
    ∃ σ τ : Perm, Contains σ τ ∧
      ∃ I : Finset Perm,
        (∀ π : Perm, π ∈ I ↔ Contains σ π ∧ Contains π τ) ∧
        I.card = 19 ∧ largestRank I = 7 ∧ width I = 8 ∧ ¬ IsSperner I := by
  sorry

/-- For every `k ≥ 1`, there exists a permutation `τ` whose principal downset
`[∅, τ]` has width exceeding its largest rank size by exactly `k`. -/
theorem downset_exact_deficiency (k : ℕ) (hk : 1 ≤ k) :
    ∃ τ : Perm, ∃ D : Finset Perm,
      (∀ π : Perm, π ∈ D ↔ Contains π τ) ∧
      width D = largestRank D + k ∧ ¬ IsSperner D := by
  sorry

end PatternPosetChallenge
