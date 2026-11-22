module

public import PatternPoset

/-!
# Axiom Verification Audit for `PatternPoset`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `PatternPoset`. A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Core permutation pattern poset definitions and structural lemmas (Defs.lean)
#print axioms PatternPoset.Perm.ext_val
#print axioms PatternPoset.strictMono_fin_eq_id
#print axioms PatternPoset.contains_len_le
#print axioms PatternPoset.contains_eq_of_len_eq
#print axioms PatternPoset.Perm.eq_of_lt_iff
#print axioms PatternPoset.le_iff_contains
#print axioms PatternPoset.le_len_le
#print axioms PatternPoset.eq_of_le_of_len_eq
#print axioms PatternPoset.rankLevel_isAntichain
#print axioms PatternPoset.rankLevel_card_le_largestRank
#print axioms PatternPoset.largestRank_le_iff
#print axioms PatternPoset.largestRank_eq_of_bounds
#print axioms PatternPoset.card_le_width_of_antichain
#print axioms PatternPoset.width_le_of_forall_antichain
#print axioms PatternPoset.largestRank_le_width
#print axioms PatternPoset.antichain_card_le_of_indexed_chain_cover
#print axioms PatternPoset.width_le_of_indexed_chain_cover
#print axioms PatternPoset.width_le_of_chain_cover
#print axioms PatternPoset.hasValley_mono
#print axioms PatternPoset.subseqPerm_le
#print axioms PatternPoset.eq_subseqPerm_of_le
#print axioms PatternPoset.mem_downset_iff
#print axioms PatternPoset.mem_interval_iff
#print axioms PatternPoset.Perm.toList_length
#print axioms PatternPoset.Perm.toList_injective
#print axioms PatternPoset.card_lt_perm_val
#print axioms PatternPoset.toList_eq_standardizeList_of_le

-- 3D box symmetric chain decomposition and slice formula (BoxChains.lean)
#print axioms PatternPoset.rectId_bounds
#print axioms PatternPoset.rectRecon_mem
#print axioms PatternPoset.rectId_rectRecon
#print axioms PatternPoset.rectRecon_rectId_rectPos
#print axioms PatternPoset.rectRecon_mono
#print axioms PatternPoset.mem_boxFinset
#print axioms PatternPoset.mem_boxSlice
#print axioms PatternPoset.boxId_bounds
#print axioms PatternPoset.boxRecon_mem_slice
#print axioms PatternPoset.boxRecon_boxId
#print axioms PatternPoset.box_chain_comparable
#print axioms PatternPoset.boxId_injOn_slice
#print axioms PatternPoset.boxId_image_eq_mid
#print axioms PatternPoset.boxId_image_card
#print axioms PatternPoset.boxSlice_card_le_mid
#print axioms PatternPoset.boxSlice_card_antitone
#print axioms PatternPoset.boxSlice_card
#print axioms PatternPoset.boxSlice_mid_card
#print axioms PatternPoset.boxId_image_card_eq

-- Seven-entry counterexample [213, 2574613] (SevenPoint.lean)
#print axioms PatternPoset.bitMask_encodeMask
#print axioms PatternPoset.toList_subseqPerm_eq_standardizeList
#print axioms PatternPoset.le_iff_exists_bitmask
#print axioms PatternPoset.has213List_of_sigma7_le
#print axioms PatternPoset.sigma7_le_tau7
#print axioms PatternPoset.interval7_eq
#print axioms PatternPoset.interval7_card
#print axioms PatternPoset.interval7_rank_sizes
#print axioms PatternPoset.interval7_largestRank
#print axioms PatternPoset.anti7_card
#print axioms PatternPoset.anti7_subset
#print axioms PatternPoset.anti7_isAntichain
#print axioms PatternPoset.chains7_isChain
#print axioms PatternPoset.chains7_covers
#print axioms PatternPoset.interval7_width
#print axioms PatternPoset.not_sperner_interval7
#print axioms PatternPoset.mcnamara_steingrimsson_Q9_5_false

-- Infinite family τ_k with exact Sperner deficiency k (Family.lean)
#print axioms PatternPoset.tau_len
#print axioms PatternPoset.tau_entry_zero
#print axioms PatternPoset.tau_entry_one
#print axioms PatternPoset.tau_tail_strictAnti
#print axioms PatternPoset.patP_zero_zero
#print axioms PatternPoset.patQ_zero
#print axioms PatternPoset.patP_hasValley
#print axioms PatternPoset.patQ_not_hasValley
#print axioms PatternPoset.patD_not_hasValley
#print axioms PatternPoset.patP_injective
#print axioms PatternPoset.patQ_injective
#print axioms PatternPoset.patD_injective
#print axioms PatternPoset.patP_ne_patQ
#print axioms PatternPoset.patP_ne_patD
#print axioms PatternPoset.patQ_ne_patD
#print axioms PatternPoset.patP_le_patP
#print axioms PatternPoset.patQ_le_patQ
#print axioms PatternPoset.patD_le_patD
#print axioms PatternPoset.patP_le_tau
#print axioms PatternPoset.patQ_le_tau_leaderA
#print axioms PatternPoset.patQ_le_tau_leaderB
#print axioms PatternPoset.patQ_le_tau
#print axioms PatternPoset.patD_le_tau
#print axioms PatternPoset.downset_tau_classify
#print axioms PatternPoset.familyAntichain_subset
#print axioms PatternPoset.familyAntichain_isAntichain
#print axioms PatternPoset.familyAntichain_card
#print axioms PatternPoset.familyChain_isChain
#print axioms PatternPoset.familyChain_covers
#print axioms PatternPoset.familyChainIndices_card
#print axioms PatternPoset.family_width
#print axioms PatternPoset.family_rankLevel_card_le
#print axioms PatternPoset.family_rankLevel_mid_card
#print axioms PatternPoset.family_largestRank
#print axioms PatternPoset.family_exact_deficiency
#print axioms PatternPoset.family_not_sperner
