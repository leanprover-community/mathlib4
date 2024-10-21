/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Index of submodules of free ℤ-modules (considered as an `AddSubgroup`).

This file provides lemmas about when a submodule of a free ℤ-module is a subgroup of finite
index.

-/


namespace Basis.SmithNormalForm

lemma toAddSubgroup_index_ne_zero_iff {M : Type*} {m n : ℕ} [AddCommGroup M] {N : Submodule ℤ M}
    (snf : Basis.SmithNormalForm N (Fin m) n) : N.toAddSubgroup.index ≠ 0 ↔ n = m := by
  rcases snf with ⟨bM, bN, f, a, snf⟩
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    apply Basis.ne_zero bN i
    specialize snf i
    simpa [hi] using snf
  let N' : Submodule ℤ (Fin m → ℤ) := N.map bM.equivFun
  let bN' : Basis (Fin n) ℤ N' := bN.map (bM.equivFun.submoduleMap N)
  have snf' : ∀ i, (bN' i : Fin m → ℤ) = Pi.single (f i) (a i) := by
    intro i
    simp only [map_apply, bN']
    erw [LinearEquiv.submoduleMap_apply]
    simp only [equivFun_apply, snf, map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
               Finsupp.single_eq_pi_single]
    ext j
    simp [Pi.single_apply]
  suffices N'.toAddSubgroup.index ≠ 0 ↔ n = m by
    convert this
    let e : (Fin m → ℤ) ≃+ M := bM.equivFun.symm
    let e' : (Fin m → ℤ) →+ M := e
    have he' : Function.Surjective e' := e.surjective
    simp only [N']
    erw [Submodule.map_toAddSubgroup]
    convert (AddSubgroup.index_comap_of_surjective N.toAddSubgroup he').symm using 2
    simp only [e']
    rw [AddSubgroup.comap_equiv_eq_map_symm]
    rfl
  have hN' : N'.toAddSubgroup = AddSubgroup.pi Set.univ
      (fun i ↦ AddSubgroup.zmultiples (if h : ∃ j, f j = i then a h.choose else 0)) := by
    ext g
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies,
               Int.mem_zmultiples_iff, bN'.mem_submodule_iff', snf']
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with ⟨c, rfl⟩
      intro i
      simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Finset.sum_apply, Pi.mul_apply,
                 Pi.single_apply]
      split_ifs with h
      · convert dvd_mul_left (a h.choose) (c h.choose)
        calc ∑ x : Fin n, _ = c h.choose * if i = f h.choose then a h.choose else 0 := by
              refine Finset.sum_eq_single h.choose ?_ (by simp)
              rintro j - hj
              have hinj := f.injective.ne hj
              rw [h.choose_spec] at hinj
              simp [hinj.symm]
          _ = c h.choose * a h.choose := by simp [h.choose_spec]
      · convert dvd_refl (0 : ℤ)
        convert Finset.sum_const_zero with j
        rw [not_exists] at h
        specialize h j
        rw [eq_comm] at h
        simp [h]
    · refine ⟨fun j ↦ (h (f j)).choose, ?_⟩
      ext i
      simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq,
                 zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Finset.sum_apply, Pi.mul_apply,
                 Pi.single_apply, mul_ite, mul_zero]
      rw [eq_comm]
      by_cases hj : ∃ j, f j = i
      · calc ∑ x : Fin n, _ =
            if i = f hj.choose then (h (f hj.choose)).choose * a hj.choose else 0 := by
              convert Finset.sum_eq_single (β := ℤ) hj.choose ?_ ?_
              · simp [hj]
              · rintro j - h
                have hinj := f.injective.ne h
                rw [hj.choose_spec] at hinj
                simp [hinj.symm]
              · simp
          _ = g i := by
              simp only [hj.choose_spec, ↓reduceIte]
              rw [mul_comm]
              conv_rhs =>
                rw [← hj.choose_spec, (h (f hj.choose)).choose_spec]
              simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte,
                         Classical.choose_eq, mul_eq_mul_left_iff]
              convert Or.inl rfl
              · exact hj.choose_spec
              · simp [hj]
      · convert Finset.sum_const_zero with x
        · rw [not_exists] at hj
          specialize hj x
          rw [eq_comm] at hj
          simp [hj]
        · rw [← zero_dvd_iff]
          convert h i
          simp [hj]
  rw [hN', AddSubgroup.index_pi, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, ne_eq, true_implies, Int.index_zmultiples, Int.natAbs_eq_zero,
             dite_eq_right_iff, forall_exists_index, not_forall]
  refine ⟨fun h ↦ le_antisymm ?_ ?_, fun h ↦ ?_⟩
  · simpa using Function.Embedding.nonempty_iff_card_le.1 ⟨f⟩
  · suffices Fintype.card (Fin m) ≤ Fintype.card (Fin n) by simpa using this
    apply Fintype.card_le_of_surjective f
    intro j
    obtain ⟨i, hi, -⟩ := h j
    exact ⟨i, hi⟩
  · subst h
    have hb : Function.Bijective f := (Nat.bijective_iff_injective_and_card _).2 ⟨f.injective, rfl⟩
    intro i
    refine ⟨(Equiv.ofBijective f hb).symm i, Equiv.ofBijective_apply_symm_apply _ _ _, ?_⟩
    exact ha _

end Basis.SmithNormalForm

namespace Int

lemma submodule_toAddSubgroup_index_ne_zero_iff {m : ℕ} {N : Submodule ℤ (Fin m → ℤ)} :
    N.toAddSubgroup.index ≠ 0 ↔ Nonempty (N ≃ₗ[ℤ] (Fin m → ℤ)) := by
  obtain ⟨n, snf⟩ := N.smithNormalForm <| Basis.ofEquivFun <| LinearEquiv.refl _ _
  rw [snf.toAddSubgroup_index_ne_zero_iff]
  rcases snf with ⟨-, bN, -, -, -⟩
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · subst h
    exact ⟨bN.equivFun⟩
  · have hc := card_eq_of_linearEquiv ℤ <| bN.equivFun.symm.trans e
    simpa using hc

lemma addSubgroup_index_ne_zero_iff {m : ℕ} {H : AddSubgroup (Fin m → ℤ)} :
    H.index ≠ 0 ↔ Nonempty (H ≃+ (Fin m → ℤ)) := by
  convert submodule_toAddSubgroup_index_ne_zero_iff (N := AddSubgroup.toIntSubmodule H) using 1
  exact ⟨fun ⟨e⟩ ↦ ⟨e.toIntLinearEquiv⟩, fun ⟨e⟩ ↦ ⟨e.toAddEquiv⟩⟩

lemma subgroup_index_ne_zero_iff {m : ℕ} {H : Subgroup (Fin m → Multiplicative ℤ)} :
    H.index ≠ 0 ↔ Nonempty (H ≃* (Fin m → Multiplicative ℤ)) := by
  let em : Multiplicative (Fin m → ℤ) ≃* (Fin m → Multiplicative ℤ) :=
    MulEquiv.funMultiplicative _ _
  let H' : Subgroup (Multiplicative (Fin m → ℤ)) := H.comap em
  let eH' : H' ≃* H := (MulEquiv.subgroupCongr <| Subgroup.comap_equiv_eq_map_symm em H).trans
    (MulEquiv.subgroupMap em.symm _).symm
  have h : H'.index = H.index := Subgroup.index_comap_of_surjective _ em.surjective
  rw [← h, ← Subgroup.index_toAddSubgroup, addSubgroup_index_ne_zero_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨(eH'.symm.trans (AddEquiv.toMultiplicative e)).trans em⟩,
    fun ⟨e⟩ ↦ ⟨(MulEquiv.toAdditive ((eH'.trans e).trans em.symm)).trans
      (AddEquiv.additiveMultiplicative _)⟩⟩

end Int
