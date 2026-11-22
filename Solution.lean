module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Hom.Basic
public import PatternPoset

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

private def toPP (π : Perm) : PatternPoset.Perm := ⟨π.len, π.perm⟩
private def fromPP (π : PatternPoset.Perm) : Perm := ⟨π.len, π.perm⟩

private def permEquiv : PatternPoset.Perm ≃ Perm where
  toFun := fromPP
  invFun := toPP
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

private theorem contains_iff (σ τ : PatternPoset.Perm) :
    Contains (fromPP σ) (fromPP τ) ↔ σ ≤ τ := by
  exact PatternPoset.le_iff_contains.symm

private theorem isAntichain_map (A : Finset PatternPoset.Perm) :
    IsAntichain (A.map permEquiv.toEmbedding) ↔ PatternPoset.IsAntichain A := by
  constructor
  · intro h x hx y hy hxy
    have h1 := h (fromPP x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      (fromPP y) (Finset.mem_map.mpr ⟨y, hy, rfl⟩) ((contains_iff x y).mpr hxy)
    exact permEquiv.injective h1
  · intro h x hx y hy hxy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
    exact congrArg fromPP (h a ha b hb ((contains_iff a b).mp hxy))

private theorem rankLevel_map (S : Finset PatternPoset.Perm) (r : ℕ) :
    (RankLevel (S.map permEquiv.toEmbedding) r).card = (PatternPoset.RankLevel S r).card := by
  have h : RankLevel (S.map permEquiv.toEmbedding) r =
      (PatternPoset.RankLevel S r).map permEquiv.toEmbedding := by
    ext x
    simp only [RankLevel, PatternPoset.RankLevel, Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hr⟩
      exact ⟨a, ⟨ha, hr⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hr⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hr⟩
  rw [h, Finset.card_map]

private theorem largestRank_map (S : Finset PatternPoset.Perm) :
    largestRank (S.map permEquiv.toEmbedding) = PatternPoset.largestRank S := by
  unfold largestRank PatternPoset.largestRank
  have himg : (S.map permEquiv.toEmbedding).image Perm.len = S.image PatternPoset.Perm.len := by
    ext r
    simp only [Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨fromPP a, ⟨a, ha, rfl⟩, rfl⟩
  rw [himg]
  apply Finset.sup_congr rfl
  intro r _
  exact rankLevel_map S r

private theorem width_map (S : Finset PatternPoset.Perm) :
    width (S.map permEquiv.toEmbedding) = PatternPoset.width S := by
  classical
  apply Nat.le_antisymm
  · unfold width
    apply Finset.sup_le
    intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    let B : Finset PatternPoset.Perm := A.map permEquiv.symm.toEmbedding
    have hAB : B.map permEquiv.toEmbedding = A := by
      ext x
      simp [B]
    have hsub : B ⊆ S := by
      intro b hb
      rcases Finset.mem_map.mp hb with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp (hA.1 ha) with ⟨s, hs, hse⟩
      have : permEquiv.symm a = s := by rw [← hse]; exact permEquiv.symm_apply_apply s
      exact this ▸ hs
    have hanti : PatternPoset.IsAntichain B := (isAntichain_map B).mp (hAB.symm ▸ hA.2)
    have hcard : A.card = B.card := by rw [← hAB, Finset.card_map]
    rw [hcard]
    exact PatternPoset.card_le_width_of_antichain hsub hanti
  · apply PatternPoset.width_le_of_forall_antichain
    intro B hB hanti
    have hsub : B.map permEquiv.toEmbedding ⊆ S.map permEquiv.toEmbedding :=
      Finset.map_subset_map.mpr hB
    have hanti' : IsAntichain (B.map permEquiv.toEmbedding) := (isAntichain_map B).mpr hanti
    have hmem : B.map permEquiv.toEmbedding ∈
        (S.map permEquiv.toEmbedding).powerset.filter IsAntichain := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsub, hanti'⟩
    have hle := Finset.le_sup (f := Finset.card) hmem
    simpa [width, Finset.card_map] using hle

private theorem fromPP_sigma7_eq : fromPP PatternPoset.σ₇ = perm213 := by
  refine congrArg (Perm.mk 3) ?_
  ext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

private theorem fromPP_tau7_eq : fromPP PatternPoset.τ₇ = perm2574613 := by
  refine congrArg (Perm.mk 7) ?_
  ext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl

theorem mcnamara_steingrimsson_Q9_5_false :
    Contains perm213 perm2574613 ∧
      ∃ I : Finset Perm,
        (∀ π : Perm, π ∈ I ↔ Contains perm213 π ∧ Contains π perm2574613) ∧
        I.card = 19 ∧ largestRank I = 7 ∧ width I = 8 ∧ ¬ IsSperner I := by
  rw [← fromPP_sigma7_eq, ← fromPP_tau7_eq]
  refine ⟨(contains_iff _ _).mpr PatternPoset.sigma7_le_tau7,
    (PatternPoset.Interval PatternPoset.σ₇ PatternPoset.τ₇).map permEquiv.toEmbedding,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro π
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases PatternPoset.mem_interval_iff.mp ha with ⟨h1, h2⟩
      exact ⟨(contains_iff _ _).mpr h1, (contains_iff _ _).mpr h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨toPP π, PatternPoset.mem_interval_iff.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (contains_iff _ _).mp h1
      · exact (contains_iff _ _).mp h2
  · rw [Finset.card_map, PatternPoset.interval7_card]
  · rw [largestRank_map, PatternPoset.interval7_largestRank]
  · rw [width_map, PatternPoset.interval7_width]
  · intro hsp
    unfold IsSperner at hsp
    rw [width_map, largestRank_map, PatternPoset.interval7_width,
      PatternPoset.interval7_largestRank] at hsp
    omega

theorem downset_exact_deficiency (k : ℕ) (hk : 1 ≤ k) :
    ∃ τ : Perm, ∃ D : Finset Perm,
      (∀ π : Perm, π ∈ D ↔ Contains π τ) ∧
      width D = largestRank D + k ∧ ¬ IsSperner D := by
  refine ⟨fromPP (PatternPoset.tau k),
    (PatternPoset.Downset (PatternPoset.tau k)).map permEquiv.toEmbedding,
    ?_, ?_, ?_⟩
  · intro π
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (contains_iff _ _).mpr (PatternPoset.mem_downset_iff.mp ha)
    · intro h
      exact ⟨toPP π, PatternPoset.mem_downset_iff.mpr ((contains_iff _ _).mp h), rfl⟩
  · rw [width_map, largestRank_map, PatternPoset.family_exact_deficiency k hk]
  · intro hsp
    unfold IsSperner at hsp
    rw [width_map, largestRank_map, PatternPoset.family_exact_deficiency k hk] at hsp
    omega

end PatternPosetChallenge
