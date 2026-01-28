/-
Copyright (c) 2025 Sahan Wijetunga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sahan Wijetunga
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Isometry


/-!
# Isometric equivalences with respect to bilinear forms

## Main definitions

* `LinearMap.BilinForm.IsometryEquiv`: `LinearEquiv`s which map between two different bilinear forms
* `LinearMap.BilinForm.Equivalent`: propositional version of the above
-/
@[expose] public section

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace LinearMap

namespace BilinForm

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]


/-- An isometric equivalence between two bilinear spaces `M₁, B₁` and `M₂, B₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the bilinear forms. -/
structure IsometryEquiv (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : ∀ n m, B₂ (toFun n) (toFun m) = B₁ n m


/-- Two bilinear forms over a ring `R` are equivalent
if there exists an isometric equivalence between them:
a linear equivalence that transforms one bilinear form into the other. -/
def Equivalent (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂) :
  Prop :=  Nonempty (B₁.IsometryEquiv B₂)

namespace IsometryEquiv

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
  {B₃ : LinearMap.BilinForm R M₃}

instance : EquivLike (B₁.IsometryEquiv B₂) M₁ M₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (B₁.IsometryEquiv B₂) R M₁ M₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

instance : CoeOut (B₁.IsometryEquiv B₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
theorem coe_toLinearEquiv (f : B₁.IsometryEquiv B₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
theorem map_app (f : B₁.IsometryEquiv B₂) (m n : M₁) : B₂ (f n) (f m) = B₁ n m :=
  f.map_app' n m

/-- The identity isometric equivalence between a bilinear form and itself. -/
@[refl]
def refl (B : LinearMap.BilinForm R M) : B.IsometryEquiv B :=
  { LinearEquiv.refl R M with map_app' := fun _ _ => rfl }

/-- The inverse isometric equivalence of an isometric equivalence between two bilinear forms. -/
@[symm]
def symm (f : B₁.IsometryEquiv B₂) : B₂.IsometryEquiv B₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by
      intro _ _; rw [← f.map_app]; congr
      repeat exact f.toLinearEquiv.apply_symm_apply _
  }

/-- The composition of two isometric equivalences between bilinear forms. -/
@[trans]
def trans (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) : B₁.IsometryEquiv B₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro n m; rw [← f.map_app, ← g.map_app]; rfl }

/-- Isometric equivalences are isometric maps -/
@[simps]
def toIsometry (g : B₁.IsometryEquiv B₂) : B₁ →bᵢ B₂ where
  toFun x := g x
  __ := g


end IsometryEquiv

namespace Equivalent

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
  {B₃ : LinearMap.BilinForm R M₃}

@[refl]
theorem refl (Q : LinearMap.BilinForm R M) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩

@[symm]
theorem symm (h : B₁.Equivalent B₂) : B₂.Equivalent B₁ :=
  h.elim fun f => ⟨f.symm⟩

@[trans]
theorem trans (h : B₁.Equivalent B₂) (h' : B₂.Equivalent B₃) : B₁.Equivalent B₃ :=
  h'.elim <| h.elim fun f g => ⟨f.trans g⟩

end Equivalent

/-- A bilinear form composed with a `LinearEquiv` is isometric to itself. -/
def isometryEquivOfCompLinearEquiv (B : LinearMap.BilinForm R M) (f : M₁ ≃ₗ[R] M) :
    B.IsometryEquiv (B.comp (f : M₁ →ₗ[R] M) (f : M₁ →ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro _ _
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }


end BilinForm
end LinearMap
