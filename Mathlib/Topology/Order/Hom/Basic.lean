/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.order.hom.basic from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOrderHom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `ContinuousOrderHomClass`
-/


open Function

variable {F α β γ δ : Type*}

/-- The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOrderHom (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous toFun
#align continuous_order_hom ContinuousOrderHom

-- mathport name: «expr →Co »
infixr:25 " →Co " => ContinuousOrderHom

section

-- porting note: extending `ContinuousMapClass` instead of `OrderHomClass`
/-- `ContinuousOrderHomClass F α β` states that `F` is a type of continuous monotone maps.

You should extend this class when you extend `ContinuousOrderHom`. -/
class ContinuousOrderHomClass (F : Type*) (α β : outParam <| Type*) [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] extends
    ContinuousMapClass F α β where
  map_monotone (f : F) : Monotone f
#align continuous_order_hom_class ContinuousOrderHomClass

-- Porting note: namespaced these results since there are more than 3 now
namespace ContinuousOrderHomClass

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [ContinuousOrderHomClass F α β]

-- See note [lower instance priority]
instance (priority := 100) toOrderHomClass  :
    OrderHomClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }
#align continuous_order_hom_class.to_continuous_map_class ContinuousOrderHomClass.toContinuousMapClass

-- Porting note: following `OrderHomClass.toOrderHom` design, introduced a wrapper
-- for the original coercion. The original one directly exposed
-- ContinuousOrderHom.mk which allowed simp to apply more eagerly than in all
-- the other results in `Topology.Order.Hom.Esakia`.
/-- Turn an element of a type `F` satisfying `ContinuousOrderHomClass F α β` into an actual
`ContinuousOrderHom`. This is declared as the default coercion from `F` to `α →Co β`. -/
@[coe]
def toContinuousOrderHom (f : F) : α →Co β :=
    { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }

instance : CoeTC F (α →Co β) :=
  ⟨toContinuousOrderHom⟩

end ContinuousOrderHomClass
/-! ### Top homomorphisms -/


namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]

section Preorder

variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]

/-- Reinterpret a `ContinuousOrderHom` as a `ContinuousMap`. -/
def toContinuousMap (f : α →Co β) : C(α, β) :=
  { f with }
#align continuous_order_hom.to_continuous_map ContinuousOrderHom.toContinuousMap

instance : ContinuousOrderHomClass (α →Co β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    -- ⊢ { toOrderHom := { toFun := toFun✝, monotone' := monotone'✝ }, continuous_toF …
    obtain ⟨⟨_, _⟩, _⟩ := g
    -- ⊢ { toOrderHom := { toFun := toFun✝¹, monotone' := monotone'✝¹ }, continuous_t …
    congr
    -- 🎉 no goals
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun

-- porting note: new lemma
@[simp] theorem coe_toOrderHom (f : α →Co β) : ⇑f.toOrderHom = f := rfl

theorem toFun_eq_coe {f : α →Co β} : f.toFun = (f : α → β) := rfl
#align continuous_order_hom.to_fun_eq_coe ContinuousOrderHom.toFun_eq_coe

@[ext]
theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align continuous_order_hom.ext ContinuousOrderHom.ext

/-- Copy of a `ContinuousOrderHom` with a new `ContinuousMap` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
  ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩
#align continuous_order_hom.copy ContinuousOrderHom.copy

@[simp]
theorem coe_copy (f : α →Co β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_order_hom.coe_copy ContinuousOrderHom.coe_copy

theorem copy_eq (f : α →Co β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_order_hom.copy_eq ContinuousOrderHom.copy_eq

variable (α)

/-- `id` as a `ContinuousOrderHom`. -/
protected def id : α →Co α :=
  ⟨OrderHom.id, continuous_id⟩
#align continuous_order_hom.id ContinuousOrderHom.id

instance : Inhabited (α →Co α) :=
  ⟨ContinuousOrderHom.id _⟩

@[simp]
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl
#align continuous_order_hom.coe_id ContinuousOrderHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl
#align continuous_order_hom.id_apply ContinuousOrderHom.id_apply

/-- Composition of `ContinuousOrderHom`s as a `ContinuousOrderHom`. -/
def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩
#align continuous_order_hom.comp ContinuousOrderHom.comp

@[simp]
theorem coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align continuous_order_hom.coe_comp ContinuousOrderHom.coe_comp

@[simp]
theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align continuous_order_hom.comp_apply ContinuousOrderHom.comp_apply

@[simp]
theorem comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_order_hom.comp_assoc ContinuousOrderHom.comp_assoc

@[simp]
theorem comp_id (f : α →Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun _ => rfl
#align continuous_order_hom.comp_id ContinuousOrderHom.comp_id

@[simp]
theorem id_comp (f : α →Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun _ => rfl
#align continuous_order_hom.id_comp ContinuousOrderHom.id_comp

theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align continuous_order_hom.cancel_right ContinuousOrderHom.cancel_right

theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align continuous_order_hom.cancel_left ContinuousOrderHom.cancel_left

instance : Preorder (α →Co β) :=
  Preorder.lift ((↑) : (α →Co β) → α → β)

end Preorder

instance [PartialOrder β] : PartialOrder (α →Co β) :=
  PartialOrder.lift ((↑) : (α →Co β) → α → β) FunLike.coe_injective

end ContinuousOrderHom
