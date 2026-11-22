module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Hom.Basic

/-!
# Palomar Challenge: Non-Sperner Intervals and Unbounded Deficiency in the Permutation Pattern Poset

Refutes McNamara and Steingrímsson's Question 9.5 (2015) by proving that the
explicit closed interval `[213, 2574613]` (`[perm213, perm2574613]`) in the
permutation pattern poset has 19 elements, largest rank size 7, and width 8
(hence is not Sperner), and proves that for every `k ≥ 1` there is a principal
downset `[∅, τ]` whose width exceeds its largest rank size by exactly `k`.
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

/-- The length-3 permutation `213` (0-indexed: `0 ↦ 1, 1 ↦ 0, 2 ↦ 2`). -/
def perm213 : Perm :=
  ⟨3,
    ⟨fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 2,
     fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 2,
     fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl,
     fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl⟩⟩

/-- The length-7 permutation `2574613`
(0-indexed: `0 ↦ 1, 1 ↦ 4, 2 ↦ 6, 3 ↦ 3, 4 ↦ 5, 5 ↦ 0, 6 ↦ 2`). -/
def perm2574613 : Perm :=
  ⟨7,
    ⟨fun
      | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => 6 | ⟨3, _⟩ => 3
      | ⟨4, _⟩ => 5 | ⟨5, _⟩ => 0 | ⟨6, _⟩ => 2,
     fun
      | ⟨0, _⟩ => 5 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 6 | ⟨3, _⟩ => 3
      | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 4 | ⟨6, _⟩ => 2,
     fun
      | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
      | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl,
     fun
      | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
      | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl⟩⟩

/-- Refutation of McNamara–Steingrímsson Question 9.5: the explicit closed
interval `[213, 2574613]` in the permutation pattern poset has 19 elements,
largest rank size 7, and width 8 (hence is not Sperner). -/
theorem mcnamara_steingrimsson_Q9_5_false :
    Contains perm213 perm2574613 ∧
      ∃ I : Finset Perm,
        (∀ π : Perm, π ∈ I ↔ Contains perm213 π ∧ Contains π perm2574613) ∧
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
