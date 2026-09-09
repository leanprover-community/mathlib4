/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Positive continuous linear maps

This file contains the continuous version of `PositiveLinearMap`. While positive linear maps between
C⋆-algebras are automatically continuous (see `PositiveLinearMap.exists_norm_apply_le` which leads
to an instance of `ContinuousLinearMapClass`) there are other situations (e.g., in the theory of
W⋆-algebras) in which this does not hold and yet we wish to restrict to consider only *continuous*
positive linear maps.

## Implementation notes

We do not define `PositiveContinuousLinearMapClass` to avoid adding a class that mixes order and
algebra. One can achieve the same effect by using a combination of `ContinuousLinearMapClass` and
`OrderHomClass`.

-/

@[expose] public section

/-- A `PositiveContinuousLinearMap` is a linear map which is both an order homomorphism and
continuous. This comes equipped with the notation `E₁ →P[R] E₂`. -/
structure PositiveContinuousLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [PartialOrder E₂] [TopologicalSpace E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₚ[R] E₂, E₁ →L[R] E₂

/-- Notation for a `PositiveContinuousLinearMap`. -/
notation:25 E " →P[" R:25 "] " F:0 => PositiveContinuousLinearMap R E F

/-- The `ContinuousLinearMap` underlying a `PositiveContinuousLinearMap`. -/
add_decl_doc PositiveContinuousLinearMap.toContinuousLinearMap
/-- The `PositiveLinearMap` underlying a `PositiveContinuousLinearMap`. -/
add_decl_doc PositiveContinuousLinearMap.toPositiveLinearMap

namespace PositiveContinuousLinearMap

section General

variable {R E₁ E₂ E₃ E₄ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [TopologicalSpace E₁] [TopologicalSpace E₂]

instance : FunLike (E₁ →P[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance : ContinuousLinearMapClass (E₁ →P[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'
  map_continuous f := f.cont

instance : OrderHomClass (E₁ →P[R] E₂) E₁ E₂ where
  map_rel f _ _ h := f.monotone' h

initialize_simps_projections PositiveContinuousLinearMap
  (toFun → apply, as_prefix toPositiveLinearMap)

@[ext]
lemma ext {f g : E₁ →P[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →P[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →P[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  map_nonneg f hx

section ofClass

variable {F : Type*} [FunLike F E₁ E₂] [ContinuousLinearMapClass F R E₁ E₂] [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive continuous linear maps as
a positive continuous linear map. -/
def ofClass (f : F) : E₁ →P[R] E₂ where
  toPositiveLinearMap := .ofClass f
  cont := map_continuous f

@[simp]
lemma coe_ofClass (f : F) : ⇑(ofClass f) = f := rfl

end ofClass

instance : Coe (E₁ →P[R] E₂) (E₁ →L[R] E₂) := ⟨toContinuousLinearMap⟩
instance : Coe (E₁ →P[R] E₂) (E₁ →ₚ[R] E₂) := ⟨toPositiveLinearMap⟩

@[simp]
lemma coe_toPositiveLinearMap (f : E₁ →P[R] E₂) :
    (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl

@[simp]
lemma coe_toContinuousLinearMap (f : E₁ →P[R] E₂) :
    (f.toContinuousLinearMap : E₁ → E₂) = f :=
  rfl

lemma toPositiveLinearMap_injective :
    Function.Injective ((↑) : (E₁ →P[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

@[simp]
lemma toPositiveLinearMap_inj (f g : E₁ →P[R] E₂) :
    f.toPositiveLinearMap = g.toPositiveLinearMap ↔ f = g :=
  toPositiveLinearMap_injective.eq_iff

lemma toContinuousLinearMap_injective :
    Function.Injective ((↑) : (E₁ →P[R] E₂) → (E₁ →L[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

-- not marked `@[simp]` because `simp` can already prove it.
lemma toContinuousLinearMap_inj (f g : E₁ →P[R] E₂) :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  toContinuousLinearMap_injective.eq_iff

instance : Zero (E₁ →P[R] E₂) where
  zero := .mk (0 : E₁ →ₚ[R] E₂) <| by fun_prop

@[simp]
lemma toPositiveLinearMap_zero : (0 : E₁ →P[R] E₂).toPositiveLinearMap = 0 :=
  rfl

@[simp]
lemma toContinuousLinearMap_zero : (0 : E₁ →P[R] E₂).toContinuousLinearMap = 0 :=
  rfl

instance : IsZeroApply (E₁ →P[R] E₂) E₁ E₂ where
  zero_apply _ := rfl

variable (R E₁) in
/-- The identity as a positive continuous linear map. -/
@[simps! apply toPositiveLinearMap] protected def id : E₁ →P[R] E₁ where
  toPositiveLinearMap := .id R E₁
  cont := continuous_id

@[simp] lemma toContinuousLinearMap_id :
    (PositiveContinuousLinearMap.id R E₁).toContinuousLinearMap = .id R E₁ := rfl

section Comp

variable [AddCommMonoid E₃] [PartialOrder E₃] [Module R E₃] [TopologicalSpace E₃]
variable [AddCommMonoid E₄] [PartialOrder E₄] [Module R E₄] [TopologicalSpace E₄]

/-- Composition of positive continuous linear maps. -/
@[simps! apply toPositiveLinearMap]
def comp (g : E₂ →P[R] E₃) (f : E₁ →P[R] E₂) : E₁ →P[R] E₃ where
  toPositiveLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  cont := g.cont.comp f.cont

@[simp]
lemma toContinuousLinearMap_comp (g : E₂ →P[R] E₃) (f : E₁ →P[R] E₂) :
    (g.comp f).toContinuousLinearMap = g.toContinuousLinearMap.comp f.toContinuousLinearMap :=
  rfl

lemma comp_assoc (h : E₃ →P[R] E₄) (g : E₂ →P[R] E₃) (f : E₁ →P[R] E₂) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  rfl

@[simp] lemma comp_id (f : E₁ →P[R] E₂) : f.comp (.id R E₁) = f := rfl
@[simp] lemma id_comp (f : E₁ →P[R] E₂) : (PositiveContinuousLinearMap.id R E₂).comp f = f := rfl
@[simp] lemma zero_comp (f : E₁ →P[R] E₂) : (0 : E₂ →P[R] E₃).comp f = 0 := rfl
@[simp] lemma comp_zero (f : E₂ →P[R] E₃) : f.comp (0 : E₁ →P[R] E₂) = 0 := by ext; simp

end Comp

variable [IsOrderedAddMonoid E₂] [ContinuousAdd E₂]

instance : Add (E₁ →P[R] E₂) where
  add f g := .mk (f.toPositiveLinearMap + g.toPositiveLinearMap) <|
    show Continuous (fun x ↦ f x + g x) by fun_prop

@[simp]
lemma toPositiveLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toPositiveLinearMap = f.toPositiveLinearMap + g.toPositiveLinearMap := by
  rfl

@[simp]
lemma toContinuousLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := by
  rfl

instance : IsAddApply (E₁ →P[R] E₂) E₁ E₂ where
  add_apply _ _ _ := rfl

instance : SMul ℕ (E₁ →P[R] E₂) where
  smul n f := .mk (n • f.toPositiveLinearMap) <|
    show Continuous (fun x ↦ n • f x) by fun_prop

@[simp]
lemma toPositiveLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toPositiveLinearMap = n • f.toPositiveLinearMap :=
  rfl

@[simp]
lemma toContinuousLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toContinuousLinearMap = n • f.toContinuousLinearMap :=
  rfl

instance : IsSMulApply ℕ (E₁ →P[R] E₂) E₁ E₂ where
  smul_apply _ _ _ := rfl

instance : AddCommMonoid (E₁ →P[R] E₂) := fast_instance% FunLike.addCommMonoid

end General

section AddGroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [TopologicalSpace E₂]
  [Module R E₁] [Module R E₂]

/-- Define a positive continuous linear map from a continuous linear map that maps
nonnegative elements to nonnegative elements -/
@[simps toPositiveLinearMap]
def mk₀ (f : E₁ →L[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →P[R] E₂ where
  toPositiveLinearMap := .mk₀ f.toLinearMap hf
  cont := f.cont

@[simp]
lemma mk₀_apply (f : E₁ →L[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) (x : E₁) :
    mk₀ f hf x = f x := rfl

@[simp]
lemma toContinuousLinearMap_mk₀ (f : E₁ →L[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) :
    (mk₀ f hf).toContinuousLinearMap = f := rfl

end AddGroup

end PositiveContinuousLinearMap
