/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Real.ConditionallyComplete
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Defining reals without the use of rationals

Showing that the reals are a Cauchy complete space.

* [Defining reals without the use of rationals][debruijn1976]

-/

namespace DigitExpansion.real

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

noncomputable
instance : UniformSpace (real Z b) :=
  .ofFun (fun x y ↦ |x - y|) (by simp) (by simp [abs_eq_abs]) (by simp [abs_sub_le])
    (fun ε εpos ↦ ⟨shift (shift ε), by simp [εpos],
     fun _ hx _ hy ↦ (add_lt_add hx hy).trans (shift_shift_add_shift_shift_lt_of_pos εpos)⟩)

instance [Nonempty Z] : NoMaxOrder (real Z b) where
  exists_gt x := by
    rcases lt_trichotomy x 0 with h|h|h
    · refine ⟨-(x + x), ?_⟩
      rw [lt_neg]
      refine (add_lt_add_left h x).trans ?_
      simp [h]
    · inhabit Z
      refine ⟨single default 1, ?_⟩
      simp only [h, ← positive_iff, val_single]
      refine single_positive_of_ne_zero _ (Ne.symm ?_)
      simp [hb.out]
    · refine ⟨x + x, ?_⟩
      simp [h]

theorem uniformity_basis_dist [Nonempty Z] :
    (uniformity (real Z b)).HasBasis (fun ε : real Z b => 0 < ε)
    fun ε => { p : (real Z b) × (real Z b) | |p.1 - p.2| < ε } := by
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

instance [Nonempty Z] : Filter.IsCountablyGenerated (uniformity (real Z b)) := by
  inhabit Z
  classical
  let g : ℕ → real Z b := fun n ↦ shift^[n] (single default 1)
  exact Filter.isCountablyGenerated_of_seq
    ⟨fun n ↦ { p : real Z b × real Z b | |p.1 - p.2| < g n },
    Filter.HasBasis.eq_iInf <| by
    refine ⟨fun s ↦ uniformity_basis_dist.mem_iff.trans ?_⟩
    have h1 : ((1 : Fin (b + 1)) : ℕ) = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt]
      simp [Nat.pos_of_ne_zero hb.out]
    have h01 : (1 : Fin (b + 1)) ≠ 0 := by
      rw [ne_comm, Fin.ne_iff_vne, h1]
      simp
    constructor
    · rintro ⟨f, posf, hf⟩
      suffices ∃ k, shift^[k] (single default 1) < f by
        obtain ⟨k, hk⟩ := this
        refine ⟨k, trivial, hf.trans' ?_⟩
        simp only [even_two, Even.mul_right, zero_lt_two, Nat.mul_div_right, ite_true,
          Set.le_eq_subset, Set.setOf_subset_setOf, Prod.forall]
        intros
        apply hk.trans'
        assumption
      obtain ⟨x, xpos, hx⟩ := (positive_iff.mpr posf).exists_least_pos
      have : single x 1 ≤ f := by
        rw [real.le_def]
        rcases eq_or_ne f (single x 1) with rfl|H
        · exact Or.inl rfl
        · refine Or.inr ⟨?_, x, fun y hy ↦ ?_⟩
          · rw [sub_ne_zero, ne_eq, ← Subtype.ext_iff]
            exact H
          · rw [DigitExpansion.sub_def, hx _ hy, val_single, single_apply_of_ne _ _ _ hy.ne',
                sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff]
            intros z _ hz'
            rcases eq_or_ne z x with rfl|hx
            · simp only [single_apply_self] at hz'
              replace hz' : f.val z ≤ 0 := by
                rw [Fin.lt_iff_val_lt_val, h1, Nat.lt_one_iff] at hz'
                exact hz'.le
              exact absurd hz' xpos.not_le
            · simp [single_apply_of_ne _ _ _ hx.symm] at hz'
      rcases lt_or_le x default with hd|hd
      · refine ⟨0, ?_⟩
        simp only [Function.iterate_zero, id_eq]
        exact this.trans_lt' (single_strict_anti_left_of_ne_zero h01 hd)
      · obtain ⟨k, rfl⟩ := exists_succ_iterate_of_le hd
        refine ⟨k + 1, ?_⟩
        simp only [Function.iterate_succ', Function.comp_apply]
        refine (shift_lt_iff.mpr ?_).trans_le ?_
        · clear xpos hx this hd posf hf f
          induction' k with k IH
          · simpa [← positive_iff] using single_positive_of_ne_zero _ h01
          · rwa [Function.iterate_succ', Function.comp_apply, shift_pos_iff]
        · convert this
          clear xpos hx this hd posf hf f
          induction' k with k IH
          · simp
          · simp only [Function.iterate_succ', Function.comp_apply, shift_single, IH]
    · rintro ⟨k, -, hk⟩
      refine ⟨g k, ?_, hk⟩
      simp only [g]
      clear hk
      induction' k with k IH
      · simpa [← positive_iff] using single_positive_of_ne_zero _ h01
      · rwa [Function.iterate_succ', Function.comp_apply, shift_pos_iff]⟩

noncomputable instance [Nonempty Z] : CompleteSpace (real Z b) := by
  inhabit Z; exact
  UniformSpace.complete_of_cauchySeq_tendsto <| fun a ha ↦
  ⟨⨆ n, sInf {a k | k ≥ n}, by
    intro s hs
    have := nhds_basis_uniformity uniformity_basis_dist (x := ⨆ n, sInf {a k | k ≥ n})
    obtain ⟨ε, εpos, hε⟩ := this.mem_iff.mp hs
    rw [uniformity_basis_dist.cauchySeq_iff] at ha
    obtain ⟨N, hN⟩ := ha (shift ε) (by simp [εpos])
    simp only [Filter.mem_map, Filter.mem_atTop_sets]
    refine ⟨N, fun n hn ↦ ?_⟩
    simp only [Set.mem_preimage]
    apply hε
    simp only [ge_iff_le, Set.mem_setOf_eq]
    have hbb : BddBelow {a k | k ≥ n} := by
      rw [bddBelow_def]
      refine ⟨a n - ε, ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      rw [sub_le_comm]
      specialize hN _ hn _ (hn.trans hm)
      simp only [Set.mem_setOf_eq, abs_lt] at hN
      exact (hN.right.trans (shift_lt_iff.mpr εpos)).le
    replace hbb : ∀ m, BddBelow {a k | k ≥ m} := by
      intro m
      rcases le_or_lt n m with hm|hm
      · refine hbb.mono ?_
        simp only [ge_iff_le, Set.setOf_subset_setOf, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        intro k hk
        exact ⟨k, hm.trans hk, rfl⟩
      · have : {a k | k ≥ m} = {a k | k ≥ n} ∪ {x | ∃ k, a k = x ∧ k < n ∧ k ≥ m} := by
          ext y
          simp only [ge_iff_le, Set.mem_setOf_eq, Set.mem_union]
          constructor
          · rintro ⟨k, hk, rfl⟩
            rcases le_or_lt n k with hkn|hkn
            · exact Or.inl ⟨_, hkn, rfl⟩
            · exact Or.inr ⟨_, rfl, hkn, hk⟩
          · rintro (⟨k, hk, rfl⟩|⟨k, rfl, _, hk⟩)
            · exact ⟨_, hk.trans' hm.le, rfl⟩
            · exact ⟨_, hk, rfl⟩
        rw [this]
        refine hbb.union (Set.Finite.bddBelow ?_)
        refine Set.Finite.ofFinset ((Finset.range (n - m)).image fun k ↦ a (k + m)) ?_
        intro y
        simp only [Finset.mem_image, Finset.mem_range, ge_iff_le, Set.mem_setOf_eq,
                   lt_tsub_iff_left, hm]
        constructor
        · rintro ⟨k, hk, rfl⟩
          refine ⟨k + m, rfl, ?_, le_add_self⟩
          rwa [add_comm]
        · rintro ⟨k, rfl, hkn, hk⟩
          refine ⟨k - m, ?_, ?_⟩
          · rwa [add_tsub_cancel_of_le hk]
          · rw [tsub_add_cancel_of_le hk]
    have : ∀ m ≥ n, sInf {a k | k ≥ n} ≤ a m := by
      intro m hm
      apply csInf_le
      · exact hbb _
      · exact ⟨m, hm, rfl⟩
    have hmono : ∀ n m : ℕ, m ≤ n → sInf {a k | k ≥ m} ≤ sInf {a k | k ≥ n} := by
      intros n m h
      apply csInf_le_csInf
      · exact hbb _
      · exact ⟨a n, _, le_rfl, rfl⟩
      · simp only [ge_iff_le, Set.setOf_subset_setOf, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
        intro k hk
        exact ⟨k, h.trans hk, rfl⟩
    rw [abs_lt, neg_lt_sub_iff_lt_add, sub_lt_comm]
    constructor
    · suffices ⨆ n, sInf {x | ∃ k, n ≤ k ∧ a k = x} ≤ shift ε + a n by
        refine this.trans_lt ?_
        simp [shift_lt_iff, εpos]
      apply ciSup_le
      intro m
      rcases le_or_lt m n with h|h
      · refine (hmono _ _ h).trans <| ((this n le_rfl).trans_lt ?_).le
        simp [εpos]
      · have : sInf {x | ∃ k, m ≤ k ∧ a k = x} ≤ a m := by
          apply csInf_le
          · exact hbb _
          · exact ⟨m, le_rfl, rfl⟩
        refine this.trans ?_
        rw [← sub_le_iff_le_add]
        refine (lt_of_abs_lt ?_).le
        simpa using hN _ (hn.trans h.le) _ hn
    · suffices a n - shift ε ≤ ⨆ n, sInf {x | ∃ k, n ≤ k ∧ a k = x} by
        refine this.trans_lt' ?_
        simp [shift_lt_iff, εpos]
      have : sInf {x | ∃ k ≥ n, a k = x} ≤ ⨆ n, sInf {x | ∃ k, n ≤ k ∧ a k = x} := by
        refine le_ciSup_of_le ?_ n le_rfl
        rw [bddAbove_def]
        refine ⟨a n + ε, ?_⟩
        simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        intro m
        rcases le_or_lt m n with h|h
        · refine (hmono _ _ h).trans <| ((this n le_rfl).trans_lt ?_).le
          simp [εpos]
        · have : sInf {x | ∃ k, m ≤ k ∧ a k = x} ≤ a m := by
            apply csInf_le
            · exact hbb _
            · exact ⟨m, le_rfl, rfl⟩
          refine this.trans ?_
          rw [← sub_le_iff_le_add']
          refine (lt_of_abs_lt ?_).le
          refine (shift_lt_iff.mpr εpos).trans' ?_
          simpa using hN _ (hn.trans h.le) _ hn
      refine this.trans' ?_
      apply le_csInf
      · exact ⟨a n, _, le_rfl, rfl⟩
      · simp only [ge_iff_le, Set.mem_setOf_eq, tsub_le_iff_right, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
        intro m hm
        rw [← sub_le_iff_le_add']
        refine (lt_of_abs_lt ?_).le
        simpa using hN _ hn _ (hn.trans hm)⟩

end DigitExpansion.real
