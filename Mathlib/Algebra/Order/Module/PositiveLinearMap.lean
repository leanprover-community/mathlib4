/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Positive linear maps

This file defines positive linear maps as a linear map that is also an order homomorphism.

## Implementation notes

We do not define `PositiveLinearMapClass` to avoid adding a class that mixes order and algebra.
One can achieve the same effect by using a combination of `LinearMapClass` and `OrderHomClass`.
We nevertheless use the namespace for lemmas using that combination of typeclasses.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

@[expose] public section

/-- A positive linear map is a linear map that is also an order homomorphism. -/
structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₗ[R] E₂, E₁ →o E₂

/-- The `OrderHom` underlying a `PositiveLinearMap`. -/
add_decl_doc PositiveLinearMap.toOrderHom

/-- Notation for a `PositiveLinearMap`. -/
notation:25 E " →ₚ[" R:25 "] " F:0 => PositiveLinearMap R E F

section PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
def PositiveLinearMap.ofClass (f : F) : E₁ →ₚ[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂) with }

@[deprecated (since := "2026-06-10")]
alias PositiveLinearMapClass.toPositiveLinearMap := PositiveLinearMap.ofClass

/-- A type of additive group homomorphisms that map nonnegative elements to nonnegative elements
is also a type of order homomorphisms. -/
lemma OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : ∀ f : F', ∀ x, 0 ≤ x → 0 ≤ f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]

instance : FunLike (E₁ →ₚ[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

initialize_simps_projections PositiveLinearMap (toFun → apply, as_prefix toLinearMap)

@[ext]
lemma ext {f g : E₁ →ₚ[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (R E₁) in
/-- The identity as a positive linear map. -/
@[simps! apply toLinearMap] protected def id : E₁ →ₚ[R] E₁ where
  __ := LinearMap.id
  __ := OrderHom.id

@[simp] lemma toOrderHom_id : (PositiveLinearMap.id R E₁).toOrderHom = .id := rfl

/-- The composition of positive linear maps is again a positive linear map. -/
@[simps! apply toLinearMap]
def comp (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂) : E₁ →ₚ[R] E₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'

@[simp] lemma toOrderHom_comp (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl

@[simp] lemma comp_id (f : E₁ →ₚ[R] E₂) : f.comp (.id R E₁) = f := rfl
@[simp] lemma id_comp (f : E₁ →ₚ[R] E₂) : (PositiveLinearMap.id R E₂).comp f = f := rfl

instance : LinearMapClass (E₁ →ₚ[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

instance : OrderHomClass (E₁ →ₚ[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →ₚ[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →ₚ[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  _root_.map_nonneg f hx

@[simp]
lemma coe_toLinearMap (f : E₁ →ₚ[R] E₂) : (f.toLinearMap : E₁ → E₂) = f :=
  rfl

lemma toLinearMap_injective : Function.Injective (toLinearMap : (E₁ →ₚ[R] E₂) → (E₁ →ₗ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

@[simp]
lemma toLinearMap_inj {f g : E₁ →ₚ[R] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff

instance : Zero (E₁ →ₚ[R] E₂) where
  zero := .mk (0 : E₁ →ₗ[R] E₂) fun _ ↦ by simp

@[simp]
lemma toLinearMap_zero : (0 : E₁ →ₚ[R] E₂).toLinearMap = 0 :=
  rfl

@[simp]
lemma zero_apply (x : E₁) : (0 : E₁ →ₚ[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂]

instance : Add (E₁ →ₚ[R] E₂) where
  add f g := .mk (f.toLinearMap + g.toLinearMap) fun _ _ h ↦
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]
lemma toLinearMap_add (f g : E₁ →ₚ[R] E₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

@[simp]
lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := rfl

instance : SMul ℕ (E₁ →ₚ[R] E₂) where
  smul n f := .mk (n • f.toLinearMap) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]
lemma toLinearMap_nsmul (f : E₁ →ₚ[R] E₂) (n : ℕ) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

@[simp]
lemma nsmul_apply (f : E₁ →ₚ[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

instance : AddCommMonoid (E₁ →ₚ[R] E₂) :=
  toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

end general

section addgroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂]

/-- Define a positive map from a linear map that maps nonnegative elements to nonnegative
elements -/
def mk₀ (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →ₚ[R] E₂ :=
  { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 ≤ f (b - a) := hf _ hab
      simpa using this }

end addgroup

end PositiveLinearMap
