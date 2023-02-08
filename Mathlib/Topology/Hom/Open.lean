/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.hom.open
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuous open maps

This file defines bundled continuous open maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_open_map`: Continuous open maps.

## Typeclasses

* `continuous_open_map_class`
-/


open Function

variable {F α β γ δ : Type _}

/-- The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOpenMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap to_fun
#align continuous_open_map ContinuousOpenMap

-- mathport name: «expr →CO »
infixr:25 " →CO " => ContinuousOpenMap

section

/-- `continuous_open_map_class F α β` states that `F` is a type of continuous open maps.

You should extend this class when you extend `continuous_open_map`. -/
class ContinuousOpenMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends ContinuousMapClass F α β where
  map_open (f : F) : IsOpenMap f
#align continuous_open_map_class ContinuousOpenMapClass

end

export ContinuousOpenMapClass (map_open)

instance [TopologicalSpace α] [TopologicalSpace β] [ContinuousOpenMapClass F α β] :
    CoeTC F (α →CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/


namespace ContinuousOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : ContinuousOpenMapClass (α →CO β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous f := f.continuous_toFun
  map_open f := f.map_open'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →CO β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : α →CO β} : f.toFun = (f : α → β) :=
  rfl
#align continuous_open_map.to_fun_eq_coe ContinuousOpenMap.toFun_eq_coe

@[ext]
theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align continuous_open_map.ext ContinuousOpenMap.ext

/-- Copy of a `continuous_open_map` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
  ⟨f.toContinuousMap.copy f' <| h, h.symm.subst f.map_open'⟩
#align continuous_open_map.copy ContinuousOpenMap.copy

@[simp]
theorem coe_copy (f : α →CO β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_open_map.coe_copy ContinuousOpenMap.coe_copy

theorem copy_eq (f : α →CO β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_open_map.copy_eq ContinuousOpenMap.copy_eq

variable (α)

/-- `id` as a `continuous_open_map`. -/
protected def id : α →CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩
#align continuous_open_map.id ContinuousOpenMap.id

instance : Inhabited (α →CO α) :=
  ⟨ContinuousOpenMap.id _⟩

@[simp]
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl
#align continuous_open_map.coe_id ContinuousOpenMap.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl
#align continuous_open_map.id_apply ContinuousOpenMap.id_apply

/-- Composition of `continuous_open_map`s as a `continuous_open_map`. -/
def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩
#align continuous_open_map.comp ContinuousOpenMap.comp

@[simp]
theorem coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align continuous_open_map.coe_comp ContinuousOpenMap.coe_comp

@[simp]
theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align continuous_open_map.comp_apply ContinuousOpenMap.comp_apply

@[simp]
theorem comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_open_map.comp_assoc ContinuousOpenMap.comp_assoc

@[simp]
theorem comp_id (f : α →CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun a => rfl
#align continuous_open_map.comp_id ContinuousOpenMap.comp_id

@[simp]
theorem id_comp (f : α →CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun a => rfl
#align continuous_open_map.id_comp ContinuousOpenMap.id_comp

theorem cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align continuous_open_map.cancel_right ContinuousOpenMap.cancel_right

theorem cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_open_map.cancel_left ContinuousOpenMap.cancel_left

end ContinuousOpenMap

