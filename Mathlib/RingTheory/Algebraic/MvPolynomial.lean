/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Transcendental elements in `MvPolynomial`

This file lists some results on some elements in `MvPolynomial σ R` being transcendental
over the base ring `R` and subrings `MvPolynomial.supported` of `MvPolynomial σ R`.
-/

universe u v w

open Polynomial

namespace MvPolynomial

variable {σ : Type*} (R : Type*) [CommRing R]

theorem transcendental_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s)
    {f : R[X]} (hf : Transcendental R f) :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  classical
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
      (renameEquiv R (Set.subtypeInsertEquivOption h).symm) |>.trans
      (supportedEquivMvPolynomial _).symm).toAlgHom |>.comp
    g |>.comp
    ((optionEquivLeft R s).symm.trans (optionEquivRight R s)).toAlgHom
  let v := ((Polynomial.aeval (R := supported R s)
    (Polynomial.aeval (X i : MvPolynomial σ R) f)).restrictScalars R).comp
      (Polynomial.mapAlgEquiv (supportedEquivMvPolynomial s).symm).toAlgHom
  replace hf : Function.Injective u := by
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, Subalgebra.coe_val,
      AlgHom.coe_coe, AlgEquiv.coe_trans, Function.comp_assoc, u]
    apply Subtype.val_injective.comp
    simp only [EquivLike.comp_injective]
    apply hf.comp
    simp only [EquivLike.comp_injective, EquivLike.injective]
  have h1 : Polynomial.aeval (X i : MvPolynomial σ R) = ((Subalgebra.val _).comp
      (supportedEquivMvPolynomial _).symm.toAlgHom |>.comp
      (Polynomial.aeval (X ⟨i, s.mem_insert i⟩ : MvPolynomial ↑(insert i s) R))) := by
    ext1; simp
  have h2 : u = v := by
    simp only [u, v, g]
    ext1
    · ext1
      simp [Set.subtypeInsertEquivOption, Subalgebra.algebraMap_eq, optionEquivLeft_symm_apply]
    · simp [Set.subtypeInsertEquivOption, h1, optionEquivLeft_symm_apply]
  simpa only [h2, v, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.injective_comp, AlgHom.coe_restrictScalars'] using hf

theorem transcendental_polynomial_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  have := transcendental_supported_polynomial_aeval_X R (Set.notMem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolynomial σ R))
    Function.injective_id (by ext1; rfl), RingHom.id_apply, ← Transcendental]

theorem transcendental_polynomial_aeval_X_iff (i : σ) {f : R[X]} :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔ Transcendental R f := by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h ↦ h.algHom _

theorem transcendental_supported_polynomial_aeval_X_iff
    [Nontrivial R] {i : σ} {s : Set σ} {f : R[X]} :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔
    i ∉ s ∧ Transcendental R f := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, hf⟩ ↦ transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose! h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ h))
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  · rw [← transcendental_polynomial_aeval_X_iff R i]
    refine h.restrictScalars fun _ _ heq ↦ MvPolynomial.C_injective σ R ?_
    simp_rw [← MvPolynomial.algebraMap_eq]
    exact congr($(heq).1)

theorem transcendental_supported_X {i : σ} {s : Set σ} (h : i ∉ s) :
    Transcendental (supported R s) (X i : MvPolynomial σ R) := by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)

theorem transcendental_X (i : σ) : Transcendental R (X i : MvPolynomial σ R) := by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)

theorem transcendental_supported_X_iff [Nontrivial R] {i : σ} {s : Set σ} :
    Transcendental (supported R s) (X i : MvPolynomial σ R) ↔ i ∉ s := by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

end MvPolynomial
