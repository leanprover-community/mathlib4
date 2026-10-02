/-
Copyright (c) 2025 Daniel Horton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Horton
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.PiTensorProduct

/-!

# Tensor Products of Families of Projective Modules

## Main definitions

* `PiTensorProduct.Projective`: The tensor product `⨂[R] i, P i` of a finite collection of
  projective modules `P i` over a `CommSemiring` is projective.

* `PiTensorProduct.piTensorHomEquiv`: The linear map given by `PiTensorProduct.piTensorHomMap` is
  an equivalence `(⨂[R] i, P i →ₗ[R] M i) ≃ₗ[R] (⨂[R] i, P i) →ₗ[R] ⨂[R] i, M i` when each `P i`
  is projective and the index set is finite.

  This is `homTensorHomEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

* `PiTensorProduct.dualDistribEquiv_of_Projective`: A linear equivalence between
  `⨂[R] i, Dual R (P i)` and `Dual R (⨂[R] i, P i)` when all `P i` are finite projective modules
  and the index set is finite. Implemented as a special case of `PiTensorProduct.piTensorHomEquiv`.

  This is `dualDistribEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

  This is also a generalization of `PiTensorProduct.dualDistribEquiv` from
  `LinearAlgebra/PiTensorProduct/Dual` which reduces its assumptions of `[CommRing R]` and
  `[Π i, Module.Free R (P i)]` to `[CommSemiring R]` and `[Π i, Module.Projective R (P i)]`.

-/

namespace PiTensorProduct

open TensorProduct PiTensorProduct Module

public section Projective

variable {R ι : Type*} {P : ι → Type*} [_root_.Finite ι] [CommSemiring R]
variable [Π i, AddCommMonoid (P i)] [Π i, Module R (P i)] [Π i, Module.Projective R (P i)]

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
    have : Projective R (⨂[R] (i : ({i₀}ᶜ : Set ι)), P i) := by
      exact hn hi₀
    exact Projective.of_equiv' (equivPiTensorComplSingletonTensor R P i₀).symm

/-- A helper function for `piTensorHomEquiv` (where the index type is `Fin n`) which constructs the
underlying equivalence -/
private noncomputable def piTensorHomEquiv_of_Fin (n : ℕ) {P' M' : Fin n → Type*}
    [Π i, AddCommMonoid (P' i)] [Π i, Module R (P' i)] [Π i, Module.Projective R (P' i)]
    [Π i, Module.Finite R (P' i)] [Π i, AddCommMonoid (M' i)] [Π i, Module R (M' i)] :
    (⨂[R] i, P' i →ₗ[R] M' i) ≃ₗ[R] (⨂[R] i, P' i) →ₗ[R] ⨂[R] i, M' i := by
  cases n with
    | zero =>
      exact (isEmptyEquiv _) ≪≫ₗ (Dual.dualBaseRingEquiv R).symm ≪≫ₗ
        (LinearEquiv.arrowCongr (isEmptyEquiv _) (isEmptyEquiv _)).symm
    | succ n =>
      classical
      let compl := ↑({0} : Set (Fin (n + 1)))ᶜ
      let e : Fin n ≃ compl := finSuccAboveEquiv 0
      exact
        -- `(⨂ (i : Fin (n + 1)), P' i →ₗ M' i) ≃ₗ (⨂ (i : ↑{0}ᶜ), P' i →ₗ M' i) ⊗ (P' 0 →ₗ M' 0)`
        (equivPiTensorComplSingletonTensor R (fun i => (P' i) →ₗ[R] (M' i)) 0) ≪≫ₗ
        -- `≃ₗ ((⨂ (i : Fin n), P' (e i)) →ₗ ⨂ (i : Fin n), M' (e i)) ⊗ (P' 0 →ₗ M' 0)`
        (LinearEquiv.rTensor ((P' 0) →ₗ[R] (M' 0))
          ((reindex R (fun (i : compl) => (P' i) →ₗ[R] (M' i)) e.symm) ≪≫ₗ
            piTensorHomEquiv_of_Fin _)) ≪≫ₗ
        -- `≃ₗ (⨂ (i : Fin n), P' (e i)) ⊗ P' 0 →ₗ (⨂ (i : Fin n), M' (e i)) ⊗ M' 0`
        (homTensorHomEquiv R (⨂[R] (i : Fin n), P' (e i)) _ (⨂[R] (i : Fin n), M' (e i)) _) ≪≫ₗ
        -- `≃ₗ (⨂[R] i, P' i) →ₗ[R] ⨂[R] i, M' i`
        LinearEquiv.arrowCongr
          ((LinearEquiv.rTensor (P' 0) (reindex R (fun (i : compl) => P' i) e.symm).symm) ≪≫ₗ
            (equivPiTensorComplSingletonTensor R (fun i => P' i) 0).symm)
          ((LinearEquiv.rTensor (M' 0) (reindex R (fun (i : compl) => M' i) e.symm).symm) ≪≫ₗ
            (equivPiTensorComplSingletonTensor R (fun i => M' i) 0).symm)

/-- This theorem has no @[simp] tag because it should only be used in `piTensorHomEquiv`
-/
private theorem piTensorHomEquiv_of_Fin_apply (n : ℕ) {P' M' : Fin n → Type*}
    [Π i, AddCommMonoid (P' i)] [Π i, Module R (P' i)] [Π i, Module.Projective R (P' i)]
    [Π i, Module.Finite R (P' i)] [Π i, AddCommMonoid (M' i)] [Π i, Module R (M' i)]
    (x : ⨂[R] i, P' i →ₗ[R] M' i) : piTensorHomEquiv_of_Fin n x = piTensorHomMap x := by
  cases n with
    | zero => sorry
    | succ n => sorry

variable (R P) [Π i, Module.Finite R (P i)]
/-- The linear map given by `PiTensorProduct.piTensorHomMap` is an equivalence
`(⨂[R] i, P i →ₗ[R] M i) ≃ₗ[R] (⨂[R] i, P i) →ₗ[R] ⨂[R] i, M i` when each `P i` is finite
projective and the index set is finite.

This is `homTensorHomEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.
-/
noncomputable def piTensorHomEquiv (M : ι → Type*) [Π i, AddCommMonoid (M i)]
    [Π i, Module R (M i)] : (⨂[R] i, P i →ₗ[R] M i) ≃ₗ[R] (⨂[R] i, P i) →ₗ[R] ⨂[R] i, M i :=
  /- Implementation Detail: Rather than defining `piTensorHomEquiv` as the composition of linear
  equivalences in the `convert` tactic below, and then proving the underlying linear map is
  `piTensorHomMap` later in `piTensorHomEquiv_toLinearMap`, we instead define `piTensorHomEquiv`
  in a way that incorporates this proof into the definition. This way `piTensorHomEquiv_toLinearMap`
  is true by definition. -/
  .ofBijective (piTensorHomMap) <| by
    let := Fintype.ofFinite ι
    convert ((reindex R (fun i => P i →ₗ[R] M i) (Fintype.equivFin ι)) ≪≫ₗ
      piTensorHomEquiv_of_Fin _ ≪≫ₗ LinearEquiv.arrowCongr (reindex R P (Fintype.equivFin ι)).symm
        (reindex R M (Fintype.equivFin ι)).symm).bijective
    congr
    ext
    simp [piTensorHomEquiv_of_Fin_apply]
    sorry

/-- A linear equivalence between `⨂[R] i, Dual R (P i)` and `Dual R (⨂[R] i, P i)` when all `P i`
are finite projective modules and the index set is finite. Implemented as a special case of
`PiTensorProduct.piTensorHomEquiv`.

This is `dualDistribEquiv` from `LinearAlgebra/Contraction` for an arbitrary family of modules.

This is also a generalization of `PiTensorProduct.dualDistribEquiv` from
`LinearAlgebra/PiTensorProduct/Dual` which reduces its assumptions of `[CommRing R]` and
`[Π i, Module.Free R (P i)]` to `[CommSemiring R]` and `[Π i, Module.Projective R (P i)]`.
-/
noncomputable def dualDistribEquiv_of_Projective :
    (⨂[R] i, Dual R (P i)) ≃ₗ[R] Dual R (⨂[R] i, P i) :=
  let := Fintype.ofFinite ι
  piTensorHomEquiv R P _ ≪≫ₗ (LinearEquiv.congrRight (constantBaseRingEquiv _ R).toLinearEquiv)

end Projective

end PiTensorProduct
