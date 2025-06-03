/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Bornology.Basic

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `LocallyBoundedMap`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `LocallyBoundedMapClass`
-/


open Bornology Filter Function Set

variable {F α β γ δ : Type*}

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure LocallyBoundedMap (α β : Type*) [Bornology α] [Bornology β] where
  /-- The function underlying a locally bounded map -/
  toFun : α → β
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le' : (cobounded β).comap toFun ≤ cobounded α

section

/-- `LocallyBoundedMapClass F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `LocallyBoundedMap`. -/
class LocallyBoundedMapClass (F : Type*) (α β : outParam Type*) [Bornology α]
    [Bornology β] [FunLike F α β] : Prop where
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α

end

export LocallyBoundedMapClass (comap_cobounded_le)

variable [FunLike F α β]

theorem Bornology.IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

/-- Turn an element of a type `F` satisfying `LocallyBoundedMapClass F α β` into an actual
`LocallyBoundedMap`. This is declared as the default coercion from `F` to
`LocallyBoundedMap α β`. -/
@[coe]
def LocallyBoundedMapClass.toLocallyBoundedMap [Bornology α] [Bornology β]
    [LocallyBoundedMapClass F α β] (f : F) : LocallyBoundedMap α β where
  toFun := f
  comap_cobounded_le' := comap_cobounded_le f

instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] :
    CoeTC F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

instance : FunLike (LocallyBoundedMap α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr

instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β where
  comap_cobounded_le f := f.comap_cobounded_le'

@[ext]
theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LocallyBoundedMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp]
theorem coe_copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- Construct a `LocallyBoundedMap` from the fact that the function maps bounded sets to bounded
sets. -/
def ofMapBounded (f : α → β) (h : ∀ ⦃s : Set α⦄, IsBounded s → IsBounded (f '' s)) :
    LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]
theorem coe_ofMapBounded (f : α → β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl

@[simp]
theorem ofMapBounded_apply (f : α → β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl

variable (α)

/-- `id` as a `LocallyBoundedMap`. -/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩

instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl

/-- Composition of `LocallyBoundedMap`s as a `LocallyBoundedMap`. -/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
  toFun := f ∘ g
  comap_cobounded_le' :=
    comap_comap.ge.trans <| (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
    f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
    (h : LocallyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congrArg (comp · _)⟩

@[simp]
theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end LocallyBoundedMap
