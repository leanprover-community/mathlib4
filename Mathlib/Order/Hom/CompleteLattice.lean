/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Complete lattice homomorphisms

This file defines frame homomorphisms and complete lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sSupHom`: Maps which preserve `⨆`.
* `sInfHom`: Maps which preserve `⨅`.
* `FrameHom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `CompleteLatticeHom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `sSupHomClass`
* `sInfHomClass`
* `FrameHomClass`
* `CompleteLatticeHomClass`

## Concrete homs

* `CompleteLatticeHom.setPreimage`: `Set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/

@[expose] public section
assert_not_exists Monoid

open Function OrderDual Set

variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α → β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
@[to_dual]
structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  /-- The underlying function of an `sInfHom`. -/
  toFun : α → β
  /-- The proposition that a `sInfHom` commutes with arbitrary infima/meets -/
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)


/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β, sSupHom α β where

attribute [to_dual existing] CompleteLatticeHom.tosSupHom

attribute [nolint docBlame] CompleteLatticeHom.tosSupHom

section

/-- `sSupHomClass F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `sSupHom`. -/
class sSupHomClass (F α β : Type*) [SupSet α] [SupSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sSupHomClass`s commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/-- `sInfHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `sInfHom`. -/
@[to_dual]
class sInfHomClass (F α β : Type*) [InfSet α] [InfSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sInfHomClass`s commute with arbitrary infima/meets. -/
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)

/-- `FrameHomClass F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `FrameHom`. -/
class FrameHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β] [FunLike F α β] : Prop
  extends InfTopHomClass F α β where
  /-- The proposition that members of `FrameHomClass` commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/-- `CompleteLatticeHomClass F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `CompleteLatticeHom`. -/
class CompleteLatticeHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β]
    [FunLike F α β] : Prop
  extends sInfHomClass F α β, sSupHomClass F α β where

attribute [to_dual existing] CompleteLatticeHomClass.tosSupHomClass

end

export sSupHomClass (map_sSup)

export sInfHomClass (map_sInf)

attribute [simp] map_sSup map_sInf

section Hom

variable [FunLike F α β]

@[to_dual (attr := simp)]
theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [iSup, ← Set.range_comp, Function.comp_def]

@[to_dual]
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [sSupHomClass F α β] : SupBotHomClass F α β :=
  { ‹sSupHomClass F α β› with
    map_sup := fun f a b => by
      rw [← sSup_pair, map_sSup]
      simp only [Set.image_pair, sSup_insert, sSup_singleton]
    map_bot := fun f => by
      rw [← sSup_empty, map_sSup, Set.image_empty, sSup_empty] }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sSupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sSup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sSup_le_iff, Set.forall_mem_image] }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.tosInfHomClass with }

end Equiv

variable [FunLike F α β]

set_option backward.isDefEq.respectTransparency false in
/-- Reinterpret an order isomorphism as a morphism of complete lattices. -/
@[simps] def OrderIso.toCompleteLatticeHom [CompleteLattice α] [CompleteLattice β]
    (f : OrderIso α β) : CompleteLatticeHom α β where
  toFun := f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

@[to_dual]
instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum and infimum homomorphisms -/


namespace sSupHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

@[to_dual]
instance : FunLike (sSupHom α β) α β where
  coe := sSupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[to_dual]
instance : sSupHomClass (sSupHom α β) α β where
  map_sSup := sSupHom.map_sSup'

@[to_dual (attr := simp)]
lemma toFun_eq_coe (f : sSupHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp, norm_cast)]
lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `sSupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual
/-- Copy of a `sInfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'

@[to_dual (attr := simp)]
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `sSupHom`. -/
@[to_dual /-- `id` as an `sInfHom`. -/]
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩

@[to_dual]
instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl

/-- Composition of `sSupHom`s as a `sSupHom`. -/
@[to_dual /-- Composition of `sInfHom`s as a `sInfHom`. -/]
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]

@[to_dual (attr := simp)]
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)]
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[to_dual (attr := simp)]
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end SupSet

variable {_ : CompleteLattice β}

@[to_dual]
instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

@[to_dual]
instance : OrderBot (sSupHom α β) where
  bot_le := fun _ _ ↦ OrderBot.bot_le _

@[to_dual (attr := simp)]
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl

end sSupHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FunLike (FrameHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : FrameHomClass (FrameHom α β) α β where
  map_sSup f := f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Reinterpret a `FrameHom` as a `LatticeHom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f

lemma toFun_eq_coe (f : FrameHom α β) : f.toFun = f := rfl

@[simp] lemma coe_toInfTopHom (f : FrameHom α β) : ⇑f.toInfTopHom = f := rfl
@[simp] lemma coe_toLatticeHom (f : FrameHom α β) : ⇑f.toLatticeHom = f := rfl
@[simp] lemma coe_mk (f : InfTopHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `FrameHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `FrameHom`. -/
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl

/-- Composition of `FrameHom`s as a `FrameHom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FunLike (CompleteLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  map_sSup f := f.map_sSup'
  map_sInf f := f.map_sInf'


/-- Reinterpret a `CompleteLatticeHom` as a `BoundedLatticeHom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f

lemma toFun_eq_coe (f : CompleteLatticeHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp)]
lemma coe_tosInfHom (f : CompleteLatticeHom α β) : ⇑f.tosInfHom = f := rfl

@[simp]
lemma coe_toBoundedLatticeHom (f : CompleteLatticeHom α β) : ⇑f.toBoundedLatticeHom = f := rfl

@[simp] lemma coe_mk (f : sInfHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `CompleteLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }

@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `CompleteLatticeHom`. -/
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl

variable {α}
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl

/-- Composition of `CompleteLatticeHom`s as a `CompleteLatticeHom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }

@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[to_dual (attr := simps)
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/]
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩

@[to_dual (attr := simp)]
theorem dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _ :=
  rfl

@[to_dual (attr := simp)]
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) :
    sSupHom.dual (g.comp f) = (sSupHom.dual g).comp (sSupHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl

@[to_dual (attr := simp)]
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl

end sSupHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps!]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩

@[simp]
theorem dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    CompleteLatticeHom.dual (g.comp f) =
      (CompleteLatticeHom.dual g).comp (CompleteLatticeHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/-- `Set.preimage` as a complete lattice homomorphism.

See also `sSupHom.setImage`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := preimage f
  map_sSup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_sInf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]

@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl

@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.preimage f :=
  rfl

@[simp]
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` syntactically)
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl

end CompleteLatticeHom

theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  Set.image_sUnion

/-- Using `Set.image`, a function between types yields a `sSupHom` between their lattices of
subsets.

See also `CompleteLatticeHom.setPreimage`. -/
@[simps]
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β) where
  toFun := image f
  map_sSup' := Set.image_sSup

/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩

variable [CompleteLattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `sSupHom`. -/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]

/-- The map `(a, b) ↦ a ⊓ b` as an `sInfHom`. -/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]

@[simp, norm_cast]
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl

@[simp, norm_cast]
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
