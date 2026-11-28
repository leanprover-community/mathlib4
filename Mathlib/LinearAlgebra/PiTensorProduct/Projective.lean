/-
Copyright (c) 2026 Daniel Horton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Horton
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.PiTensorProduct

/-!

# Tensor Products of Families of Projective Modules

This file develops the properties of tensor products of families of projective modules. Results for
binary tensor products from `LinearAlgebra/Contraction` are extended to `PiTensorProduct`, and the
main result `dualDistribEquiv` of `LinearAlgebra/PiTensorProduct/Dual` is generalized from free
modules over a ring to projective modules over a semiring.

## Main definitions

* `PiTensorProduct.Projective`: The tensor product `⨂[R] i, P i` of a finite collection of
  projective modules `P i` over a `CommSemiring` is projective.

* `PiTensorProduct.piTensorHomEquiv`: The linear map `PiTensorProduct.piTensorHomMap` is an
  equivalence `(⨂[R] i, P i →ₗ[R] M i) ≃ₗ[R] (⨂[R] i, P i) →ₗ[R] ⨂[R] i, M i` when each `P i`
  is finite projective and the index set is finite.

  This is `homTensorHomEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

* `PiTensorProduct.dualDistribEquivOfProjective`: The linear map `PiTensorProduct.dualDistrib`
  is an equivalence `⨂[R] i, Dual R (P i) ≃ₗ[R] Dual R (⨂[R] i, P i)` when all `P i` are finite
  projective modules and the index set is finite (implemented as a special case of
  `piTensorHomEquiv`).

  This is `dualDistribEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

  This is also a generalization of `PiTensorProduct.dualDistribEquiv` from
  `LinearAlgebra/PiTensorProduct/Dual`, replacing `[CommRing R]` with `[CommSemiring R]` and
  `[∀ i, Module.Free R (P i)]` with `[∀ i, Module.Projective R (P i)]`.

## Tags

contraction, dual module, projective module, tensor, tensor product
-/

namespace PiTensorProduct

open TensorProduct PiTensorProduct Module

public section Projective

variable {R ι : Type*} {P : ι → Type*} [_root_.Finite ι] [CommSemiring R]
variable [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)] [∀ i, Module.Projective R (P i)]

/-- The tensor product `⨂[R] i, P i` of a finite collection of projective modules `P i` over a
`CommSemiring` is projective.
-/
instance Projective : Projective R (⨂[R] i, P i) := by
  obtain ⟨n, hι⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    have : IsEmpty ι := Finite.card_eq_zero_iff.mp hι
    exact Projective.of_equiv' (isEmptyEquiv ι).symm
  | succ n hn =>
    classical
    have : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).left
    have i₀ := Classical.arbitrary ι
    have hi₀ : Nat.card ({i₀}ᶜ : Set ι) = n := by
      let := Fintype.ofFinite ι
      rw [← Fintype.card_eq_nat_card, Fintype.card_compl_set, Fintype.card_eq_nat_card, hι,
        Fintype.card_unique, add_tsub_cancel_right]
    have : Projective R (⨂[R] i : ({i₀}ᶜ : Set ι), P i) := hn hi₀
    exact Projective.of_equiv' (equivPiTensorComplSingletonTensor R P i₀).symm

/-- A helper for `piTensorHomEquiv` which constructs the underlying equivalence recursively
assuming an index type of `Fin n`. -/
private noncomputable def piTensorHomEquiv_of_Fin (n : ℕ) {P' M' : Fin n → Type*}
    [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)] [∀ i, Module.Projective R (P' i)]
    [∀ i, Module.Finite R (P' i)] [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)] :
    (⨂[R] i, P' i →ₗ[R] M' i) ≃ₗ[R] (⨂[R] i, P' i) →ₗ[R] ⨂[R] i, M' i := by
  cases n with
    | zero =>
      exact isEmptyEquiv _ ≪≫ₗ (Dual.dualBaseRingEquiv R).symm ≪≫ₗ
        (LinearEquiv.arrowCongr (isEmptyEquiv _) (isEmptyEquiv _)).symm
    | succ n =>
      classical
      let zero_compl := ({0} : Set (Fin (n + 1)))ᶜ
      let e : Fin n ≃ zero_compl := finSuccAboveEquiv 0
      exact
        -- `(⨂ i : Fin (n + 1), P' i →ₗ M' i) ≃ₗ (⨂ i : {0}ᶜ, P' i →ₗ M' i) ⊗ (P' 0 →ₗ M' 0)`
        equivPiTensorComplSingletonTensor R (fun i ↦ P' i →ₗ[R] M' i) 0 ≪≫ₗ
        -- `≃ₗ ((⨂ i : Fin n, P' (e i)) →ₗ ⨂ i : Fin n, M' (e i)) ⊗ (P' 0 →ₗ M' 0)`
        LinearEquiv.rTensor (P' 0 →ₗ[R] M' 0)
          ((reindex R (fun i : zero_compl ↦ P' i →ₗ[R] M' i) e.symm) ≪≫ₗ
            piTensorHomEquiv_of_Fin n) ≪≫ₗ
        -- `≃ₗ (⨂ i : Fin n, P' (e i)) ⊗ P' 0 →ₗ (⨂ i : Fin n, M' (e i)) ⊗ M' 0`
        homTensorHomEquiv R (⨂[R] i : Fin n, P' (e i)) _ (⨂[R] (i : Fin n), M' (e i)) _ ≪≫ₗ
        -- `≃ₗ (⨂[R] i, P' i) →ₗ[R] ⨂[R] i, M' i`
        LinearEquiv.arrowCongr
          (LinearEquiv.rTensor (P' 0) (reindex R (fun i : zero_compl ↦ P' i) e.symm).symm ≪≫ₗ
            (equivPiTensorComplSingletonTensor R (fun i ↦ P' i) 0).symm)
          (LinearEquiv.rTensor (M' 0) (reindex R (fun i : zero_compl ↦ M' i) e.symm).symm ≪≫ₗ
            (equivPiTensorComplSingletonTensor R (fun i ↦ M' i) 0).symm)

/-- This lemma has no `@[simp]` tag because it should only be used in `piTensorHomEquiv` -/
private lemma piTensorHomEquiv_of_Fin_tprod (n : ℕ) {P' M' : Fin n → Type*}
    [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)] [∀ i, Module.Projective R (P' i)]
    [∀ i, Module.Finite R (P' i)] [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, P' i →ₗ[R] M' i) : piTensorHomEquiv_of_Fin n (⨂ₜ[R] i, f i) = map f := by
  cases n with
    | zero =>
      rw [piTensorHomEquiv_of_Fin]
      ext x
      have : isEmptyElim = fun i ↦ f i (x i) := by ext i; exact Fin.elim0 i
      simp_all
    | succ n =>
      let zero_compl := ({0} : Set (Fin (n + 1)))ᶜ
      let e : Fin n ≃ zero_compl := finSuccAboveEquiv 0
      rw [piTensorHomEquiv_of_Fin]
      ext x
      apply (equivPiTensorComplSingletonTensor R M' 0).injective
      have : (reindex R (fun i : zero_compl ↦ M' i) e.symm).symm ((piTensorHomEquiv_of_Fin n)
          (⨂ₜ[R] i, f (e i)) (⨂ₜ[R] i, x (e i))) = ⨂ₜ[R] i : zero_compl, f i (x i) := by
        rw [piTensorHomEquiv_of_Fin_tprod, map_tprod,
          reindex_symm_symm_tprod e (fun i : zero_compl ↦ f i (x i))]
      simp
      congr

variable (R P) (M : ι → Type*) [∀ i, Module.Finite R (P i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

/-- The linear map `PiTensorProduct.piTensorHomMap` is an equivalence when each `P i` is finite
projective and the index set is finite.

This is `homTensorHomEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.
-/
@[expose]
noncomputable def piTensorHomEquiv :
    (⨂[R] i, P i →ₗ[R] M i) ≃ₗ[R] (⨂[R] i, P i) →ₗ[R] ⨂[R] i, M i :=
  /- Implementation Detail: This definition is exposed and constructed using `ofBijective` to make
  `homTensorHomEquiv_toLinearMap` and `homTensorHomEquiv_apply` true by definition. This design is
  also used in `homTensorHomEquiv`. -/
  .ofBijective piTensorHomMap <| by
    have := Fintype.ofFinite ι
    convert (reindex R (fun i ↦ P i →ₗ[R] M i) (Fintype.equivFin ι) ≪≫ₗ
      piTensorHomEquiv_of_Fin _ ≪≫ₗ LinearEquiv.arrowCongr (reindex R P (Fintype.equivFin ι)).symm
        (reindex R M (Fintype.equivFin ι)).symm).bijective
    congr
    ext f x
    have : (⨂ₜ[R] i : ι, f i (x i)) = (reindex R M (Fintype.equivFin ι)).symm
        (⨂ₜ[R] i, f ((Fintype.equivFin ι).symm i) (x ((Fintype.equivFin ι).symm i))) := by
      rw [reindex_symm_tprod (Fintype.equivFin ι) fun i ↦ f i (x i)]
    simpa [piTensorHomEquiv_of_Fin_tprod]

@[simp]
lemma piTensorHomEquiv_toLinearMap : (piTensorHomEquiv R P M).toLinearMap = piTensorHomMap := rfl

variable {R P M} in
@[simp]
lemma piTensorHomEquiv_apply (f : ⨂[R] i, P i →ₗ[R] M i) :
    piTensorHomEquiv R P M f = piTensorHomMap f := rfl

/-- The linear map `PiTensorProduct.dualDistrib` is an equivalence when all `P i` are finite
projective modules (implemented as a special case of `piTensorHomEquiv`).

This is `dualDistribEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

This is also a generalization of `PiTensorProduct.dualDistribEquiv` from
`LinearAlgebra/PiTensorProduct/Dual`, replacing `[CommRing R]` with `[CommSemiring R]` and
`[∀ i, Module.Free R (P i)]` with `[∀ i, Module.Projective R (P i)]`.
-/
@[expose]
noncomputable def dualDistribEquivOfProjective :
    (⨂[R] i, Dual R (P i)) ≃ₗ[R] Dual R (⨂[R] i, P i) :=
  have := Fintype.ofFinite ι
  piTensorHomEquiv R P _ ≪≫ₗ (LinearEquiv.congrRight (constantBaseRingEquiv ι R).toLinearEquiv)

@[simp]
lemma dualDistribEquivOfProjective_toLinearMap :
    (dualDistribEquivOfProjective R P).toLinearMap = dualDistrib := rfl

variable {R P} in
@[simp]
lemma dualDistribEquivOfProjective_tprod_tprod (f : ∀ i, Dual R (P i)) (x : ∀ i, P i) :
    dualDistribEquivOfProjective R P (⨂ₜ[R] i, f i) (⨂ₜ[R] i, x i) = ∏ᶠ i, f i (x i) := by
  let := Fintype.ofFinite ι
  simp [dualDistribEquivOfProjective, finprod_eq_prod_of_fintype]

end Projective

end PiTensorProduct
