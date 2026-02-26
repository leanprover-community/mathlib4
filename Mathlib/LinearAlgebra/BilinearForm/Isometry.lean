/-
Copyright (c) 2025 Sahan Wijetunga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sahan Wijetunga
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Isometric linear maps

## Main definitions

* ` LinearMap.BilinForm.Isometry`: `LinearMap`s which respect a given pair of bilinear forms

## Notation

`B₁ →bᵢ B₂` is notation for `B₁.Isometry B₂`.
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

/-- An isometry between two bilinear spaces `M₁, B₁` and `M₂, B₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the bilinear forms. -/
structure Isometry (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
extends M₁ →ₗ[R] M₂ where
  /-- The bilinear form agrees across the map. -/
  map_app (m m' : M₁) : B₂ (toFun m) (toFun m') = B₁ m m'

namespace Isometry

@[inherit_doc]
notation:25 B₁ " →bᵢ " B₂:0 => Isometry B₁ B₂

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
variable {B₃ : LinearMap.BilinForm R M₃} {B₄ : LinearMap.BilinForm R M₄}

instance instFunLike : FunLike (B₁ →bᵢ B₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance instLinearMapClass : LinearMapClass (B₁ →bᵢ B₂) R M₁ M₂ where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

theorem toLinearMap_injective :
    Function.Injective (Isometry.toLinearMap : (B₁ →bᵢ B₂) → M₁ →ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
theorem ext ⦃f g : B₁ →bᵢ B₂⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. -/
protected def Simps.apply (f : B₁ →bᵢ B₂) : M₁ → M₂ := f

initialize_simps_projections Isometry (toFun → apply)

@[simp]
theorem map_app (f : B₁ →bᵢ B₂) (m m' : M₁) : B₂ (f m) (f m') = B₁ m m' :=
  f.map_app' m  m'

@[simp]
theorem coe_toLinearMap (f : B₁ →bᵢ B₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a bilinear form to itself. -/
@[simps!]
def id (B : LinearMap.BilinForm R M) : B →bᵢ B where
  __ := LinearMap.id
  map_app' _ _ := rfl

/-- The identity isometry between equal bilinear forms. -/
@[simps!]
def ofEq {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂) : B₁ →bᵢ B₂ where
  __ := LinearMap.id
  map_app' _ _ := h ▸ rfl

@[simp]
theorem ofEq_rfl {B : LinearMap.BilinForm R M₁} : ofEq (rfl : B = B) = .id B := rfl

/-- The composition of two isometries between bilinear forms. -/
@[simps]
def comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) : B₁ →bᵢ B₃ where
  toFun x := g (f x)
  map_app' x y := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ →ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ →ₗ[R] M₂)

@[simp]
theorem toLinearMap_comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
theorem id_comp (f : B₁ →bᵢ B₂) : (id B₂).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : B₁ →bᵢ B₂) : f.comp (id B₁) = f :=
  ext fun _ => rfl

theorem comp_assoc (h : B₃ →bᵢ B₄) (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/-- There is a zero map from any module with the zero form. -/
instance : Zero ((0 : LinearMap.BilinForm R M₁) →bᵢ B₂) where
  zero := { (0 : M₁ →ₗ[R] M₂) with map_app' := fun _ _ => map_zero _ }

/-- There is a zero map from the trivial module. -/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (B₁ →bᵢ B₂) where
  zero :=
  { (0 : M₁ →ₗ[R] M₂) with
    map_app' := fun x y => by
      rw[Subsingleton.elim x 0, Subsingleton.elim y 0]
      simp
       }

/-- Maps into the zero module are trivial -/
instance [Subsingleton M₂] : Subsingleton (B₁ →bᵢ B₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end BilinForm

end LinearMap
