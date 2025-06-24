/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry

/-!
# Isometric equivalences with respect to quadratic forms

## Main definitions

* `QuadraticForm.IsometryEquiv`: `LinearEquiv`s which map between two different quadratic forms
* `QuadraticForm.Equivalent`: propositional version of the above

## Main results

* `equivalent_weighted_sum_squares`: in finite dimensions, any quadratic form is equivalent to a
  parametrization of `QuadraticForm.weightedSumSquares`.
-/


variable {ι R K M M₁ M₂ M₃ V N : Type*}

open QuadraticMap

namespace QuadraticMap

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
         [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]

/-- An isometric equivalence between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
structure IsometryEquiv (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometric equivalence between them:
a linear equivalence that transforms one quadratic form into the other. -/
def Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop :=
  Nonempty (Q₁.IsometryEquiv Q₂)

namespace IsometryEquiv

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

instance : EquivLike (Q₁.IsometryEquiv Q₂) M₁ M₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (Q₁.IsometryEquiv Q₂) R M₁ M₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

-- Porting note: was `Coe`
instance : CoeOut (Q₁.IsometryEquiv Q₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
theorem coe_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
theorem map_app (f : Q₁.IsometryEquiv Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

/-- The identity isometric equivalence between a quadratic form and itself. -/
@[refl]
def refl (Q : QuadraticMap R M N) : Q.IsometryEquiv Q :=
  { LinearEquiv.refl R M with map_app' := fun _ => rfl }

/-- The inverse isometric equivalence of an isometric equivalence between two quadratic forms. -/
@[symm]
def symm (f : Q₁.IsometryEquiv Q₂) : Q₂.IsometryEquiv Q₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.toLinearEquiv.apply_symm_apply m }

/-- The composition of two isometric equivalences between quadratic forms. -/
@[trans]
def trans (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) : Q₁.IsometryEquiv Q₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }

/-- Isometric equivalences are isometric maps -/
@[simps]
def toIsometry (g : Q₁.IsometryEquiv Q₂) : Q₁ →qᵢ Q₂ where
  toFun x := g x
  __ := g

end IsometryEquiv

namespace Equivalent

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

@[refl]
theorem refl (Q : QuadraticMap R M N) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩

@[symm]
theorem symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁ :=
  h.elim fun f => ⟨f.symm⟩

@[trans]
theorem trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ :=
  h'.elim <| h.elim fun f g => ⟨f.trans g⟩

end Equivalent

/-- A quadratic form composed with a `LinearEquiv` is isometric to itself. -/
def isometryEquivOfCompLinearEquiv (Q : QuadraticMap R M N) (f : M₁ ≃ₗ[R] M) :
    Q.IsometryEquiv (Q.comp (f : M₁ →ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        LinearEquiv.apply_symm_apply, f.apply_symm_apply] }

variable [Finite ι]

/-- A quadratic form is isometrically equivalent to its bases representations. -/
noncomputable def isometryEquivBasisRepr (Q : QuadraticMap R M N) (v : Basis ι R M) :
    IsometryEquiv Q (Q.basisRepr v) :=
  isometryEquivOfCompLinearEquiv Q v.equivFun.symm

end QuadraticMap

namespace QuadraticForm
variable [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

/-- Given an orthogonal basis, a quadratic form is isometrically equivalent with a weighted sum of
squares. -/
noncomputable def isometryEquivWeightedSumSquares (Q : QuadraticForm K V)
    (v : Basis (Fin (Module.finrank K V)) K V)
    (hv₁ : (associated (R := K) Q).IsOrthoᵢ v) :
    Q.IsometryEquiv (weightedSumSquares K fun i => Q (v i)) := by
  let iso := Q.isometryEquivBasisRepr v
  refine ⟨iso, fun m => ?_⟩
  convert iso.map_app m
  rw [basisRepr_eq_of_iIsOrtho _ _ hv₁]

variable [FiniteDimensional K V]

open LinearMap.BilinForm

theorem equivalent_weightedSumSquares (Q : QuadraticForm K V) :
    ∃ w : Fin (Module.finrank K V) → K, Equivalent Q (weightedSumSquares K w) :=
  let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

theorem equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V)
    (hQ : (associated (R := K) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank K V) → Kˣ, Equivalent Q (weightedSumSquares K w) := by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm K Q)
  have hv₂ := hv₁.not_isOrtho_basis_self_of_separatingLeft hQ
  simp_rw [LinearMap.IsOrtho, associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

end QuadraticForm
