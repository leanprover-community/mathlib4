/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Isometric linear maps

## Main definitions

* `QuadraticForm.Isometry`: `LinearMap`s which map between two different quadratic forms

## Notation

`Q₁ →qᵢ Q₂` is notation for `Q₁.Isometry Q₂`.
-/

variable {ι R M M₁ M₂ M₃ M₄ : Type*}

namespace QuadraticForm

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the quadratic forms. -/
structure Isometry (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) extends M₁ →ₗ[R] M₂ where
  /-- The quadratic form agrees across the map. -/
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

namespace Isometry

@[inherit_doc]
notation:25 Q₁ " →qᵢ " Q₂:0 => Isometry Q₁ Q₂

variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
variable {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}

instance instFunLike : FunLike (Q₁ →qᵢ Q₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance instLinearMapClass : LinearMapClass (Q₁ →qᵢ Q₂) R M₁ M₂ where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

theorem toLinearMap_injective :
    Function.Injective (Isometry.toLinearMap : (Q₁ →qᵢ Q₂) → M₁ →ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h : _)

@[ext]
theorem ext ⦃f g : Q₁ →qᵢ Q₂⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. -/
protected def Simps.apply (f : Q₁ →qᵢ Q₂) : M₁ → M₂ := f

initialize_simps_projections Isometry (toFun → apply)

@[simp]
theorem map_app (f : Q₁ →qᵢ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

@[simp]
theorem coe_toLinearMap (f : Q₁ →qᵢ Q₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a quadratic form to itself. -/
@[simps!]
def id (Q : QuadraticForm R M) : Q →qᵢ Q where
  __ := LinearMap.id
  map_app' _ := rfl

/-- The identity isometry between equal quadratic forms. -/
@[simps!]
def ofEq {Q₁ Q₂ : QuadraticForm R M₁} (h : Q₁ = Q₂) : Q₁ →qᵢ Q₂ where
  __ := LinearMap.id
  map_app' _ := h ▸ rfl

@[simp]
theorem ofEq_rfl {Q : QuadraticForm R M₁} : ofEq (rfl : Q = Q) = .id Q := rfl

/-- The composition of two isometries between quadratic forms. -/
@[simps]
def comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) : Q₁ →qᵢ Q₃ where
  toFun x := g (f x)
  map_app' x := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ →ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ →ₗ[R] M₂)

@[simp]
theorem toLinearMap_comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
theorem id_comp (f : Q₁ →qᵢ Q₂) : (id Q₂).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : Q₁ →qᵢ Q₂) : f.comp (id Q₁) = f :=
  ext fun _ => rfl

theorem comp_assoc (h : Q₃ →qᵢ Q₄) (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/-- There is a zero map from any module with the zero form. -/
instance : Zero ((0 : QuadraticForm R M₁) →qᵢ Q₂) where
  zero := { (0 : M₁ →ₗ[R] M₂) with map_app' := fun _ => map_zero _ }

/-- There is a zero map from the trivial module. -/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (Q₁ →qᵢ Q₂) where
  zero :=
  { (0 : M₁ →ₗ[R] M₂) with
    map_app' := fun m => Subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm }

/-- Maps into the zero module are trivial -/
instance [Subsingleton M₂] : Subsingleton (Q₁ →qᵢ Q₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end QuadraticForm
