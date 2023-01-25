/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.bornology.hom
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Bornology.Basic

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `locally_bounded_map`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `locally_bounded_map_class`
-/


open Bornology Filter Function Set

variable {F α β γ δ : Type _}

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure LocallyBoundedMap (α β : Type _) [Bornology α] [Bornology β] where
  toFun : α → β
  comap_cobounded_le' : (cobounded β).comap to_fun ≤ cobounded α
#align locally_bounded_map LocallyBoundedMap

section

/-- `locally_bounded_map_class F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `locally_bounded_map`. -/
class LocallyBoundedMapClass (F : Type _) (α β : outParam <| Type _) [Bornology α]
  [Bornology β] extends FunLike F α fun _ => β where
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α
#align locally_bounded_map_class LocallyBoundedMapClass

end

export LocallyBoundedMapClass (comap_cobounded_le)

theorem IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] {f : F}
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs
#align is_bounded.image IsBounded.image

instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] :
    CoeTC F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  comap_cobounded_le f := f.comap_cobounded_le'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LocallyBoundedMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : LocallyBoundedMap α β} : f.toFun = (f : α → β) :=
  rfl
#align locally_bounded_map.to_fun_eq_coe LocallyBoundedMap.toFun_eq_coe

@[ext]
theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align locally_bounded_map.ext LocallyBoundedMap.ext

/-- Copy of a `locally_bounded_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩
#align locally_bounded_map.copy LocallyBoundedMap.copy

@[simp]
theorem coe_copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align locally_bounded_map.coe_copy LocallyBoundedMap.coe_copy

theorem copy_eq (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align locally_bounded_map.copy_eq LocallyBoundedMap.copy_eq

/-- Construct a `locally_bounded_map` from the fact that the function maps bounded sets to bounded
sets. -/
def ofMapBounded (f : α → β) (h) : LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩
#align locally_bounded_map.of_map_bounded LocallyBoundedMap.ofMapBounded

@[simp]
theorem coe_ofMapBounded (f : α → β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl
#align locally_bounded_map.coe_of_map_bounded LocallyBoundedMap.coe_ofMapBounded

@[simp]
theorem ofMapBounded_apply (f : α → β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl
#align locally_bounded_map.of_map_bounded_apply LocallyBoundedMap.ofMapBounded_apply

variable (α)

/-- `id` as a `locally_bounded_map`. -/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩
#align locally_bounded_map.id LocallyBoundedMap.id

instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

@[simp]
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl
#align locally_bounded_map.coe_id LocallyBoundedMap.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl
#align locally_bounded_map.id_apply LocallyBoundedMap.id_apply

/-- Composition of `locally_bounded_map`s as a `locally_bounded_map`. -/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ
    where
  toFun := f ∘ g
  comap_cobounded_le' :=
    comap_comap.ge.trans <| (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'
#align locally_bounded_map.comp LocallyBoundedMap.comp

@[simp]
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align locally_bounded_map.coe_comp LocallyBoundedMap.coe_comp

@[simp]
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
    f.comp g a = f (g a) :=
  rfl
#align locally_bounded_map.comp_apply LocallyBoundedMap.comp_apply

@[simp]
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
    (h : LocallyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align locally_bounded_map.comp_assoc LocallyBoundedMap.comp_assoc

@[simp]
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun a => rfl
#align locally_bounded_map.comp_id LocallyBoundedMap.comp_id

@[simp]
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun a => rfl
#align locally_bounded_map.id_comp LocallyBoundedMap.id_comp

theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align locally_bounded_map.cancel_right LocallyBoundedMap.cancel_right

theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align locally_bounded_map.cancel_left LocallyBoundedMap.cancel_left

end LocallyBoundedMap

