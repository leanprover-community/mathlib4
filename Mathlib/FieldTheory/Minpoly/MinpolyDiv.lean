/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Results about `minpoly R x / (X - C x)`

## Main definition
- `minpolyDiv`: The polynomial `minpoly R x / (X - C x)`.

We used the contents of this file to describe the dual basis of a powerbasis under the trace form.
See `traceForm_dualBasis_powerBasis_eq`.

## Main results
- `span_coeff_minpolyDiv`: The coefficients of `minpolyDiv` spans `R<x>`.
-/

open Polynomial Module

variable (R K) {L S} [CommRing R] [Field K] [Field L] [CommRing S] [Algebra R S] [Algebra K L]
variable (x : S)

/-- `minpolyDiv R x : S[X]` for `x : S` is the polynomial `minpoly R x / (X - C x)`. -/
noncomputable def minpolyDiv : S[X] := (minpoly R x).map (algebraMap R S) /ₘ (X - C x)

lemma minpolyDiv_spec :
    minpolyDiv R x * (X - C x) = (minpoly R x).map (algebraMap R S) := by
  delta minpolyDiv
  rw [mul_comm, mul_divByMonic_eq_iff_isRoot, IsRoot, eval_map, ← aeval_def, minpoly.aeval]

lemma coeff_minpolyDiv (i) : coeff (minpolyDiv R x) i =
    algebraMap R S (coeff (minpoly R x) (i + 1)) + coeff (minpolyDiv R x) (i + 1) * x := by
  rw [← coeff_map, ← minpolyDiv_spec R x]; simp [mul_sub]

variable {R x}

lemma minpolyDiv_eq_zero (hx : ¬IsIntegral R x) : minpolyDiv R x = 0 := by
  delta minpolyDiv minpoly
  rw [dif_neg hx, Polynomial.map_zero, zero_divByMonic]

lemma eval_minpolyDiv_self : (minpolyDiv R x).eval x = aeval x (derivative <| minpoly R x) := by
  rw [aeval_def, ← eval_map, ← derivative_map, ← minpolyDiv_spec R x]; simp

lemma minpolyDiv_eval_eq_zero_of_ne_of_aeval_eq_zero [IsDomain S]
    {y} (hxy : y ≠ x) (hy : aeval y (minpoly R x) = 0) : (minpolyDiv R x).eval y = 0 := by
  rw [aeval_def, ← eval_map, ← minpolyDiv_spec R x] at hy
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by rwa [sub_eq_zero])

lemma eval₂_minpolyDiv_of_eval₂_eq_zero {T} [CommRing T]
    [IsDomain T] [DecidableEq T] {x y}
    (σ : S →+* T) (hy : eval₂ (σ.comp (algebraMap R S)) y (minpoly R x) = 0) :
    eval₂ σ y (minpolyDiv R x) =
      if σ x = y then σ (aeval x (derivative <| minpoly R x)) else 0 := by
  split_ifs with h
  · rw [← h, eval₂_hom, eval_minpolyDiv_self]
  · rw [← eval₂_map, ← minpolyDiv_spec] at hy
    simpa [sub_eq_zero, Ne.symm h] using hy

lemma eval₂_minpolyDiv_self {T} [CommRing T] [Algebra R T] [IsDomain T] [DecidableEq T] (x : S)
    (σ₁ σ₂ : S →ₐ[R] T) :
    eval₂ σ₁ (σ₂ x) (minpolyDiv R x) =
      if σ₁ x = σ₂ x then σ₁ (aeval x (derivative <| minpoly R x)) else 0 := by
  apply eval₂_minpolyDiv_of_eval₂_eq_zero
  rw [AlgHom.comp_algebraMap, ← σ₂.comp_algebraMap, ← eval₂_map, ← RingHom.coe_coe, eval₂_hom,
    eval_map, ← aeval_def, minpoly.aeval, map_zero]

lemma eval_minpolyDiv_of_aeval_eq_zero [IsDomain S] [DecidableEq S]
    {y} (hy : aeval y (minpoly R x) = 0) :
    (minpolyDiv R x).eval y = if x = y then aeval x (derivative <| minpoly R x) else 0 := by
  rw [eval, eval₂_minpolyDiv_of_eval₂_eq_zero, RingHom.id_apply, RingHom.id_apply]
  simpa [aeval_def] using hy


lemma coeff_minpolyDiv_mem_adjoin (x : S) (i) :
    coeff (minpolyDiv R x) i ∈ Algebra.adjoin R {x} := by
  by_contra H
  have : ∀ j, coeff (minpolyDiv R x) (i + j) ∉ Algebra.adjoin R {x} := by
    intro j; induction j with
    | zero => exact H
    | succ j IH =>
      intro H; apply IH
      rw [coeff_minpolyDiv]
      refine add_mem ?_ (mul_mem H (Algebra.self_mem_adjoin_singleton R x))
      exact Subalgebra.algebraMap_mem _ _
  apply this (natDegree (minpolyDiv R x) + 1)
  rw [coeff_eq_zero_of_natDegree_lt]
  · exact zero_mem _
  · cutsat

section IsIntegral
variable (hx : IsIntegral R x)
include hx

lemma minpolyDiv_ne_zero [Nontrivial S] : minpolyDiv R x ≠ 0 := by
  intro e
  have := minpolyDiv_spec R x
  rw [e, zero_mul] at this
  exact ((minpoly.monic hx).map (algebraMap R S)).ne_zero this.symm

lemma minpolyDiv_monic : Monic (minpolyDiv R x) := by
  nontriviality S
  have := congr_arg leadingCoeff (minpolyDiv_spec R x)
  rw [leadingCoeff_mul', ((minpoly.monic hx).map (algebraMap R S)).leadingCoeff] at this
  · simpa using this
  · simpa using minpolyDiv_ne_zero hx

lemma natDegree_minpolyDiv_succ [Nontrivial S] :
    natDegree (minpolyDiv R x) + 1 = natDegree (minpoly R x) := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap R S), ← minpolyDiv_spec, natDegree_mul']
  · simp
  · simpa using minpolyDiv_ne_zero hx

lemma natDegree_minpolyDiv_lt [Nontrivial S] :
    natDegree (minpolyDiv R x) < natDegree (minpoly R x) := by
  rw [← natDegree_minpolyDiv_succ hx]
  exact Nat.lt_succ_self _

lemma minpolyDiv_eq_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R K] [Algebra K S] [IsScalarTower R K S] [IsFractionRing R K] :
    minpolyDiv R x = minpolyDiv K x := by
  delta minpolyDiv
  rw [IsScalarTower.algebraMap_eq R K S, ← map_map,
    ← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx]

lemma coeff_minpolyDiv_sub_pow_mem_span {i} (hi : i ≤ natDegree (minpolyDiv R x)) :
    coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) - x ^ i ∈
      Submodule.span R ((x ^ ·) '' Set.Iio i) := by
  induction i with
  | zero => simp [(minpolyDiv_monic hx).leadingCoeff]
  | succ i IH =>
    rw [coeff_minpolyDiv, add_sub_assoc, pow_succ, ← sub_mul, Algebra.algebraMap_eq_smul_one]
    refine add_mem ?_ ?_
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨0, Nat.zero_lt_succ _, pow_zero _⟩
    · rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left (b := 1) hi)]
      apply SetLike.le_def.mp ?_
        (Submodule.mul_mem_mul (IH ((Nat.le_succ _).trans hi))
          (Submodule.mem_span_singleton_self x))
      rw [Submodule.span_mul_span, Set.mul_singleton, Set.image_image]
      apply Submodule.span_mono
      rintro _ ⟨j, hj, rfl⟩
      rw [Set.mem_Iio] at hj
      exact ⟨j + 1, Nat.add_lt_of_lt_sub hj, pow_succ x j⟩

lemma span_coeff_minpolyDiv :
    Submodule.span R (Set.range (coeff (minpolyDiv R x))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality S
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply coeff_minpolyDiv_mem_adjoin
  · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx) (minpoly.aeval _ _),
      Submodule.span_le]
    simp only [Finset.coe_image, Finset.coe_range, Set.image_subset_iff]
    intro i
    induction i using Nat.strongRecOn with | ind i hi => ?_
    intro hi'
    have : coeff (minpolyDiv R x) (natDegree (minpolyDiv R x) - i) ∈
        Submodule.span R (Set.range (coeff (minpolyDiv R x))) :=
      Submodule.subset_span (Set.mem_range_self _)
    rw [Set.mem_preimage, SetLike.mem_coe, ← Submodule.sub_mem_iff_right _ this]
    refine SetLike.le_def.mp ?_ (coeff_minpolyDiv_sub_pow_mem_span hx ?_)
    · rw [Submodule.span_le, Set.image_subset_iff]
      intro j (hj : j < i)
      exact hi j hj (lt_trans hj hi')
    · rwa [← natDegree_minpolyDiv_succ hx, Set.mem_Iio, Nat.lt_succ_iff] at hi'

end IsIntegral

lemma natDegree_minpolyDiv :
    natDegree (minpolyDiv R x) = natDegree (minpoly R x) - 1 := by
  nontriviality S
  by_cases hx : IsIntegral R x
  · rw [← natDegree_minpolyDiv_succ hx]; rfl
  · rw [minpolyDiv_eq_zero hx, minpoly.eq_zero hx]; rfl


section PowerBasis

variable {K}

lemma sum_smul_minpolyDiv_eq_X_pow (E) [Field E] [Algebra K E] [IsAlgClosed E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {x : L} (hxL : Algebra.adjoin K {x} = ⊤) {r : ℕ} (hr : r < finrank K L) :
    ∑ σ : L →ₐ[K] E, ((x ^ r / aeval x (derivative <| minpoly K x)) •
      minpolyDiv K x).map σ = (X ^ r : E[X]) := by
  classical
  rw [← sub_eq_zero]
  have : Function.Injective (fun σ : L →ₐ[K] E ↦ σ x) := fun _ _ h =>
    AlgHom.ext_of_adjoin_eq_top hxL (fun _ hx ↦ hx ▸ h)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ this
  · intro σ
    simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, eval_sub, eval_finset_sum,
      eval_smul, eval_map, eval₂_minpolyDiv_self, this.eq_iff, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, eval_pow, eval_X]
    rw [sub_eq_zero, div_mul_cancel₀]
    rw [ne_eq, map_eq_zero_iff σ σ.toRingHom.injective]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · refine (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt ((Polynomial.natDegree_sum_le _ _).trans_lt ?_) ?_)
    · simp only [Polynomial.map_smul,
        map_div₀, map_pow, RingHom.coe_coe, Function.comp_apply,
        Finset.mem_univ, forall_true_left, Finset.fold_max_lt, AlgHom.card]
      refine ⟨finrank_pos, ?_⟩
      intro σ
      exact ((Polynomial.natDegree_smul_le _ _).trans natDegree_map_le).trans_lt
        ((natDegree_minpolyDiv_lt (Algebra.IsIntegral.isIntegral x)).trans_le
          (minpoly.natDegree_le _))
    · rwa [natDegree_pow, natDegree_X, mul_one, AlgHom.card]

end PowerBasis
