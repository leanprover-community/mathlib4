/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Ideal.Operations

#align_import ring_theory.coprime.ideal from "leanprover-community/mathlib"@"2bbc7e3884ba234309d2a43b19144105a753292e"

/-!
# An additional lemma about coprime ideals

This lemma generalises `exists_sum_eq_one_iff_pairwise_coprime` to the case of non-principal ideals.
It is on a separate file due to import requirements.
-/


namespace Ideal

variable {ι R : Type*} [CommSemiring R]

/-- A finite family of ideals is pairwise coprime (that is, any two of them generate the whole ring)
iff when taking all the possible intersections of all but one of these ideals, the resulting family
of ideals still generate the whole ring.

For example with three ideals : `I ⊔ J = I ⊔ K = J ⊔ K = ⊤ ↔ (I ⊓ J) ⊔ (I ⊓ K) ⊔ (J ⊓ K) = ⊤`.

When ideals are all of the form `I i = R ∙ s i`, this is equivalent to the
`exists_sum_eq_one_iff_pairwise_coprime` lemma.-/
theorem iSup_iInf_eq_top_iff_pairwise {t : Finset ι} (h : t.Nonempty) (I : ι → Ideal R) :
    (⨆ i ∈ t, ⨅ (j) (_ : j ∈ t) (_ : j ≠ i), I j) = ⊤ ↔
      (t : Set ι).Pairwise fun i j => I i ⊔ I j = ⊤ := by
  haveI : DecidableEq ι := Classical.decEq ι
  -- ⊢ ⨆ (i : ι) (_ : i ∈ t), ⨅ (j : ι) (_ : j ∈ t) (_ : j ≠ i), I j = ⊤ ↔ Set.Pair …
  rw [eq_top_iff_one, Submodule.mem_iSup_finset_iff_exists_sum]
  -- ⊢ (∃ μ, (Finset.sum t fun i => ↑(μ i)) = 1) ↔ Set.Pairwise ↑t fun i j => I i ⊔ …
  refine' h.cons_induction _ _ <;> clear t h
  -- ⊢ ∀ (a : ι), (∃ μ, (Finset.sum {a} fun i => ↑(μ i)) = 1) ↔ Set.Pairwise ↑{a} f …
                                   -- ⊢ ∀ (a : ι), (∃ μ, (Finset.sum {a} fun i => ↑(μ i)) = 1) ↔ Set.Pairwise ↑{a} f …
                                   -- ⊢ ∀ ⦃a : ι⦄ (s : Finset ι) (h : ¬a ∈ s), Finset.Nonempty s → ((∃ μ, (Finset.su …
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true_iff]
    -- ⊢ ∀ (a : ι), ∃ μ, ↑(μ a) = 1
    refine' fun a => ⟨fun i => if h : i = a then ⟨1, _⟩ else 0, _⟩
    -- ⊢ 1 ∈ ⨅ (j : ι) (_ : j ∈ {a}) (_ : j ≠ i), I j
    · simp [h]
      -- 🎉 no goals
    · simp only [dif_pos, dif_ctx_congr, Submodule.coe_mk, eq_self_iff_true]
      -- 🎉 no goals
  intro a t hat h ih
  -- ⊢ (∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1) ↔ Set.Pairwise …
  rw [Finset.coe_cons,
    Set.pairwise_insert_of_symmetric fun i j (h : I i ⊔ I j = ⊤) => sup_comm.trans h]
  constructor
  -- ⊢ (∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1) → (Set.Pairwis …
  · rintro ⟨μ, hμ⟩
    -- ⊢ (Set.Pairwise ↑t fun i j => I i ⊔ I j = ⊤) ∧ ∀ (b : ι), b ∈ ↑t → a ≠ b → I a …
    rw [Finset.sum_cons] at hμ
    -- ⊢ (Set.Pairwise ↑t fun i j => I i ⊔ I j = ⊤) ∧ ∀ (b : ι), b ∈ ↑t → a ≠ b → I a …
    -- Porting note: `refine` yields goals in a different order than in lean3.
    refine ⟨ih.mp ⟨Pi.single h.choose ⟨μ a, ?a1⟩ + fun i => ⟨μ i, ?a2⟩, ?a3⟩, fun b hb ab => ?a4⟩
    case a1 =>
      have := Submodule.coe_mem (μ a)
      rw [mem_iInf] at this ⊢
      --for some reason `simp only [mem_iInf]` times out
      intro i
      specialize this i
      rw [mem_iInf, mem_iInf] at this ⊢
      intro hi _
      apply this (Finset.subset_cons _ hi)
      rintro rfl
      exact hat hi
    case a2 =>
      have := Submodule.coe_mem (μ i)
      simp only [mem_iInf] at this ⊢
      intro j hj ij
      exact this _ (Finset.subset_cons _ hj) ij
    case a3 =>
      rw [← @if_pos _ _ h.choose_spec R (μ a) 0, ← Finset.sum_pi_single', ← Finset.sum_add_distrib]
        at hμ
      convert hμ
      rename_i i _
      rw [Pi.add_apply, Submodule.coe_add, Submodule.coe_mk]
      by_cases hi : i = h.choose
      · rw [hi, Pi.single_eq_same, Pi.single_eq_same, Submodule.coe_mk]
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Submodule.coe_zero]
    case a4 =>
      rw [eq_top_iff_one, Submodule.mem_sup]
      rw [add_comm] at hμ
      refine' ⟨_, _, _, _, hμ⟩
      · refine' sum_mem _ fun x hx => _
        have := Submodule.coe_mem (μ x)
        simp only [mem_iInf] at this
        apply this _ (Finset.mem_cons_self _ _)
        rintro rfl
        exact hat hx
      · have := Submodule.coe_mem (μ a)
        simp only [mem_iInf] at this
        exact this _ (Finset.subset_cons _ hb) ab.symm
  · rintro ⟨hs, Hb⟩
    -- ⊢ ∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    -- ⊢ ∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1
    have := sup_iInf_eq_top fun b hb => Hb b hb (ne_of_mem_of_not_mem hb hat).symm
    -- ⊢ ∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1
    rw [eq_top_iff_one, Submodule.mem_sup] at this
    -- ⊢ ∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1
    obtain ⟨u, hu, v, hv, huv⟩ := this
    -- ⊢ ∃ μ, (Finset.sum (Finset.cons a t hat) fun i => ↑(μ i)) = 1
    refine' ⟨fun i => if hi : i = a then ⟨v, _⟩ else ⟨u * μ i, _⟩, _⟩
    · simp only [mem_iInf] at hv ⊢
      -- ⊢ ∀ (i_1 : ι), i_1 ∈ Finset.cons a t hat → i_1 ≠ i → v ∈ I i_1
      intro j hj ij
      -- ⊢ v ∈ I j
      rw [Finset.mem_cons, ← hi] at hj
      -- ⊢ v ∈ I j
      exact hv _ (hj.resolve_left ij)
      -- 🎉 no goals
    · have := Submodule.coe_mem (μ i)
      -- ⊢ u * ↑(μ i) ∈ ⨅ (j : ι) (_ : j ∈ Finset.cons a t hat) (_ : j ≠ i), I j
      simp only [mem_iInf] at this ⊢
      -- ⊢ ∀ (i_1 : ι), i_1 ∈ Finset.cons a t hat → i_1 ≠ i → u * ↑(μ i) ∈ I i_1
      intro j hj ij
      -- ⊢ u * ↑(μ i) ∈ I j
      rcases Finset.mem_cons.mp hj with (rfl | hj)
      -- ⊢ u * ↑(μ i) ∈ I j
      · exact mul_mem_right _ _ hu
        -- 🎉 no goals
      · exact mul_mem_left _ _ (this _ hj ij)
        -- 🎉 no goals
    · dsimp only
      -- ⊢ (Finset.sum (Finset.cons a t hat) fun i => ↑(if hi : i = a then { val := v,  …
      rw [Finset.sum_cons, dif_pos rfl, add_comm]
      -- ⊢ (Finset.sum t fun x => ↑(if hi : x = a then { val := v, property := (_ : v ∈ …
      rw [← mul_one u] at huv
      -- ⊢ (Finset.sum t fun x => ↑(if hi : x = a then { val := v, property := (_ : v ∈ …
      rw [← huv, ← hμ, Finset.mul_sum]
      -- ⊢ (Finset.sum t fun x => ↑(if hi : x = a then { val := v, property := (_ : v ∈ …
      congr 1
      -- ⊢ (Finset.sum t fun x => ↑(if hi : x = a then { val := v, property := (_ : v ∈ …
      apply Finset.sum_congr rfl
      -- ⊢ ∀ (x : ι), x ∈ t → ↑(if hi : x = a then { val := v, property := (_ : v ∈ ⨅ ( …
      intro j hj
      -- ⊢ ↑(if hi : j = a then { val := v, property := (_ : v ∈ ⨅ (j_1 : ι) (_ : j_1 ∈ …
      rw [dif_neg]
      -- ⊢ ¬j = a
      rintro rfl
      -- ⊢ False
      exact hat hj
      -- 🎉 no goals
#align ideal.supr_infi_eq_top_iff_pairwise Ideal.iSup_iInf_eq_top_iff_pairwise

end Ideal
