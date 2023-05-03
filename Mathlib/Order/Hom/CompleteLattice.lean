/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.hom.complete_lattice
! leanprover-community/mathlib commit 9d684a893c52e1d6692a504a118bfccbae04feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Lattice

/-!
# Complete lattice homomorphisms

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupₛHom`: Maps which preserve `⨆`.
* `InfₛHom`: Maps which preserve `⨅`.
* `FrameHom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `CompleteLatticeHom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `SupₛHomClass`
* `InfₛHomClass`
* `FrameHomClass`
* `CompleteLatticeHomClass`

## Concrete homs

* `Completelattice.setPreimage`: `Set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/


open Function OrderDual Set

variable {F α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

-- Porting note: mathport made this & InfₛHom into "SupHomCat" and "InfHomCat".
/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure SupₛHom (α β : Type _) [SupSet α] [SupSet β] where
  /-- The underlying function of a SupₛHom. -/
  toFun : α → β
  /-- The proposition that a `SupₛHom` commutes with arbitrary suprema/joins. -/
  map_supₛ' (s : Set α) : toFun (supₛ s) = supₛ (toFun '' s)
#align Sup_hom SupₛHom

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure InfₛHom (α β : Type _) [InfSet α] [InfSet β] where
  /-- The underlying function of an `InfₛHom`. -/
  toFun : α → β
  /-- The proposition that a `InfₛHom` commutes with arbitrary infima/meets -/
  map_infₛ' (s : Set α) : toFun (infₛ s) = infₛ (toFun '' s)
#align Inf_hom InfₛHom

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_supₛ' (s : Set α) : toFun (supₛ s) = supₛ (toFun '' s)
#align frame_hom FrameHom


/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfₛHom α β where
  /-- The proposition that complete lattice homomorphism commutes with arbitrary suprema/joins. -/
  map_supₛ' (s : Set α) : toFun (supₛ s) = supₛ (toFun '' s)
#align complete_lattice_hom CompleteLatticeHom

section

-- Porting note: mathport made this & InfHomClass into "SupHomClassCat" and "InfHomClassCat".
/-- `SupₛHomClass F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `SupₛHom`. -/
class SupₛHomClass (F : Type _) (α β : outParam <| Type _) [SupSet α] [SupSet β] extends
  FunLike F α fun _ => β where
  /-- The proposition that members of `SupₛHomClass`s commute with arbitrary suprema/joins. -/
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align Sup_hom_class SupₛHomClass

/-- `InfₛHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `InfₛHom`. -/
class InfₛHomClass (F : Type _) (α β : outParam <| Type _) [InfSet α] [InfSet β] extends
  FunLike F α fun _ => β where
  /-- The proposition that members of `InfₛHomClass`s commute with arbitrary infima/meets. -/
  map_infₛ (f : F) (s : Set α) : f (infₛ s) = infₛ (f '' s)
#align Inf_hom_class InfₛHomClass

/-- `FrameHomClass F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `FrameHom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfTopHomClass F α β where
  /-- The proposition that members of `FrameHomClass` commute with arbitrary suprema/joins. -/
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align frame_hom_class FrameHomClass

/-- `CompleteLatticeHomClass F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `CompleteLatticeHom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfₛHomClass F α β where
  /-- The proposition that members of `CompleteLatticeHomClass` commute with arbitrary
  suprema/joins. -/
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass

end

export SupₛHomClass (map_supₛ)

export InfₛHomClass (map_infₛ)

attribute [simp] map_supₛ map_infₛ

theorem map_supᵢ [SupSet α] [SupSet β] [SupₛHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [supᵢ, ← Set.range_comp, Function.comp]
#align map_supr map_supᵢ

theorem map_supᵢ₂ [SupSet α] [SupSet β] [SupₛHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_supᵢ]
#align map_supr₂ map_supᵢ₂

theorem map_infᵢ [InfSet α] [InfSet β] [InfₛHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by simp [infᵢ, ← Set.range_comp, Function.comp]
#align map_infi map_infᵢ

theorem map_infᵢ₂ [InfSet α] [InfSet β] [InfₛHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_infᵢ]
#align map_infi₂ map_infᵢ

-- See note [lower instance priority]
instance (priority := 100) SupₛHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [SupₛHomClass F α β] : SupBotHomClass F α β :=
  {  ‹SupₛHomClass F α β› with
    map_sup := fun f a b => by
      rw [← supₛ_pair, map_supₛ]
      simp only [Set.image_pair, supₛ_insert, supₛ_singleton]
    map_bot := fun f => by
      rw [← supₛ_empty, map_supₛ, Set.image_empty]
      -- Porting note: rw [supₛ_empty] does not work, but exact supₛ_empty does?
      exact supₛ_empty  }
#align Sup_hom_class.to_sup_bot_hom_class SupₛHomClass.toSupBotHomClass

-- See note [lower instance priority]
instance (priority := 100) InfₛHomClass.toInfTopHomClass [CompleteLattice α]
    [CompleteLattice β] [InfₛHomClass F α β] : InfTopHomClass F α β :=
  { ‹InfₛHomClass F α β› with
    map_inf := fun f a b => by
      rw [← infₛ_pair, map_infₛ, Set.image_pair]
      simp only [Set.image_pair, infₛ_insert, infₛ_singleton]
    map_top := fun f => by
      rw [← infₛ_empty, map_infₛ, Set.image_empty]
      -- Porting note: rw [infₛ_empty] does not work, but exact infₛ_empty does?
      exact infₛ_empty  }
#align Inf_hom_class.to_inf_top_hom_class InfₛHomClass.toInfTopHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toSupₛHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : SupₛHomClass F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.toSupₛHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, SupₛHomClass.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, InfₛHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β]  [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { SupₛHomClass.toSupBotHomClass, InfₛHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupₛHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : SupₛHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_supₛ := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, supₛ_le_iff, Set.ball_image_iff] }
#align order_iso_class.to_Sup_hom_class OrderIsoClass.toSupₛHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfₛHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : InfₛHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_infₛ := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_infₛ_iff, Set.ball_image_iff] }
#align order_iso_class.to_Inf_hom_class OrderIsoClass.toInfₛHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  -- Porting note: Used to be:
    -- { OrderIsoClass.toSupₛHomClass, OrderIsoClass.toLatticeHomClass,
    -- show InfₛHomClass F α β from inferInstance with }
  { OrderIsoClass.toSupₛHomClass, OrderIsoClass.toInfₛHomClass with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass

instance [SupSet α] [SupSet β] [SupₛHomClass F α β] : CoeTC F (SupₛHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [InfSet α] [InfSet β] [InfₛHomClass F α β] : CoeTC F (InfₛHom α β) :=
  ⟨fun f => ⟨f, map_infₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

/-! ### Supremum homomorphisms -/


namespace SupₛHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : SupₛHomClass (SupₛHom α β) α β
    where
  coe := SupₛHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_supₛ := SupₛHom.map_supₛ'

-- Porting note: We do not want CoeFun for this in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `funLike.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (SupₛHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

-- Porting note: times out
@[simp]
theorem toFun_eq_coe {f : SupₛHom α β} : f.toFun = ⇑f  :=
  rfl
#align Sup_hom.to_fun_eq_coe SupₛHom.toFun_eq_coe

@[ext]
theorem ext {f g : SupₛHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext SupₛHom.ext

/-- Copy of a `SupₛHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupₛHom α β) (f' : α → β) (h : f' = f) : SupₛHom α β
    where
  toFun := f'
  map_supₛ' := h.symm ▸ f.map_supₛ'
#align Sup_hom.copy SupₛHom.copy

@[simp]
theorem coe_copy (f : SupₛHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy SupₛHom.coe_copy

theorem copy_eq (f : SupₛHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq SupₛHom.copy_eq

variable (α)

/-- `id` as a `SupₛHom`. -/
protected def id : SupₛHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id SupₛHom.id

instance : Inhabited (SupₛHom α α) :=
  ⟨SupₛHom.id α⟩

@[simp]
theorem coe_id : ⇑(SupₛHom.id α) = id :=
  rfl
#align Sup_hom.coe_id SupₛHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : SupₛHom.id α a = a :=
  rfl
#align Sup_hom.id_apply SupₛHom.id_apply

/-- Composition of `SupₛHom`s as a `SupₛHom`. -/
def comp (f : SupₛHom β γ) (g : SupₛHom α β) : SupₛHom α γ
    where
  toFun := f ∘ g
  map_supₛ' s := by rw [comp_apply, map_supₛ, map_supₛ, Set.image_image]; simp only [Function.comp]
#align Sup_hom.comp SupₛHom.comp

@[simp]
theorem coe_comp (f : SupₛHom β γ) (g : SupₛHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp SupₛHom.coe_comp

@[simp]
theorem comp_apply (f : SupₛHom β γ) (g : SupₛHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply SupₛHom.comp_apply

@[simp]
theorem comp_assoc (f : SupₛHom γ δ) (g : SupₛHom β γ) (h : SupₛHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc SupₛHom.comp_assoc

@[simp]
theorem comp_id (f : SupₛHom α β) : f.comp (SupₛHom.id α) = f :=
  ext fun _ => rfl
#align Sup_hom.comp_id SupₛHom.comp_id

@[simp]
theorem id_comp (f : SupₛHom α β) : (SupₛHom.id β).comp f = f :=
  ext fun _ => rfl
#align Sup_hom.id_comp SupₛHom.id_comp

theorem cancel_right {g₁ g₂ : SupₛHom β γ} {f : SupₛHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align Sup_hom.cancel_right SupₛHom.cancel_right

theorem cancel_left {g : SupₛHom β γ} {f₁ f₂ : SupₛHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Sup_hom.cancel_left SupₛHom.cancel_left

end SupSet

variable { _ : CompleteLattice β}

instance : PartialOrder (SupₛHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (SupₛHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, supₛ_empty]
      · rw [hs.image_const, supₛ_singleton]⟩⟩

instance : OrderBot (SupₛHom α β) where
  bot := ⊥
  bot_le := fun _ _ ↦ CompleteLattice.bot_le _

@[simp]
theorem coe_bot : ⇑(⊥ : SupₛHom α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot SupₛHom.coe_bot

@[simp]
theorem bot_apply (a : α) : (⊥ : SupₛHom α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply SupₛHom.bot_apply

end SupₛHom

/-! ### Infimum homomorphisms -/


namespace InfₛHom

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : InfₛHomClass (InfₛHom α β) α β
    where
  coe := InfₛHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_infₛ := InfₛHom.map_infₛ'

-- Porting note: Do not want these CoeFun instances in lean4
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (InfₛHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : InfₛHom α β} : f.toFun = ⇑f :=
  rfl
#align Inf_hom.to_fun_eq_coe InfₛHom.toFun_eq_coe

@[ext]
theorem ext {f g : InfₛHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext InfₛHom.ext

/-- Copy of a `InfₛHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfₛHom α β) (f' : α → β) (h : f' = f) : InfₛHom α β
    where
  toFun := f'
  map_infₛ' := h.symm ▸ f.map_infₛ'
#align Inf_hom.copy InfₛHom.copy

@[simp]
theorem coe_copy (f : InfₛHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy InfₛHom.coe_copy

theorem copy_eq (f : InfₛHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq InfₛHom.copy_eq

variable (α)

/-- `id` as an `InfₛHom`. -/
protected def id : InfₛHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id InfₛHom.id

instance : Inhabited (InfₛHom α α) :=
  ⟨InfₛHom.id α⟩

@[simp]
theorem coe_id : ⇑(InfₛHom.id α) = id :=
  rfl
#align Inf_hom.coe_id InfₛHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : InfₛHom.id α a = a :=
  rfl
#align Inf_hom.id_apply InfₛHom.id_apply

/-- Composition of `InfₛHom`s as a `InfₛHom`. -/
def comp (f : InfₛHom β γ) (g : InfₛHom α β) : InfₛHom α γ
    where
  toFun := f ∘ g
  map_infₛ' s := by rw [comp_apply, map_infₛ, map_infₛ, Set.image_image]; simp only [Function.comp]
#align Inf_hom.comp InfₛHom.comp

@[simp]
theorem coe_comp (f : InfₛHom β γ) (g : InfₛHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp InfₛHom.coe_comp

@[simp]
theorem comp_apply (f : InfₛHom β γ) (g : InfₛHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply InfₛHom.comp_apply

@[simp]
theorem comp_assoc (f : InfₛHom γ δ) (g : InfₛHom β γ) (h : InfₛHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc InfₛHom.comp_assoc

@[simp]
theorem comp_id (f : InfₛHom α β) : f.comp (InfₛHom.id α) = f :=
  ext fun _ => rfl
#align Inf_hom.comp_id InfₛHom.comp_id

@[simp]
theorem id_comp (f : InfₛHom α β) : (InfₛHom.id β).comp f = f :=
  ext fun _ => rfl
#align Inf_hom.id_comp InfₛHom.id_comp

theorem cancel_right {g₁ g₂ : InfₛHom β γ} {f : InfₛHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align Inf_hom.cancel_right InfₛHom.cancel_right

theorem cancel_left {g : InfₛHom β γ} {f₁ f₂ : InfₛHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Inf_hom.cancel_left InfₛHom.cancel_left

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (InfₛHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (InfₛHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, infₛ_empty]
      · rw [hs.image_const, infₛ_singleton]⟩⟩

instance : OrderTop (InfₛHom α β) where
  top := ⊤
  le_top := fun _ _ => CompleteLattice.le_top _

@[simp]
theorem coe_top : ⇑(⊤ : InfₛHom α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top InfₛHom.coe_top

@[simp]
theorem top_apply (a : α) : (⊤ : InfₛHom α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply InfₛHom.top_apply

end InfₛHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  map_supₛ f := f.map_supₛ'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

-- Porting note: We do not want CoeFun for this in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (FrameHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

/-- Reinterpret a `FrameHom` as a `LatticeHom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
#align frame_hom.to_lattice_hom FrameHom.toLatticeHom

/- Porting note: SimpNF linter complains that lhs can be simplified,
added _aux version with [simp] attribute -/
-- @[simp]
theorem toFun_eq_coe {f : FrameHom α β} : f.toFun = ⇑f :=
  rfl
#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coe

@[simp]
theorem toFun_eq_coe_aux {f : FrameHom α β} : ↑f.toInfTopHom = ⇑f :=
  rfl

@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align frame_hom.ext FrameHom.ext

/-- Copy of a `FrameHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : SupₛHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy

@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align frame_hom.coe_copy FrameHom.coe_copy

theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align frame_hom.copy_eq FrameHom.copy_eq

variable (α)

/-- `id` as a `FrameHom`. -/
protected def id : FrameHom α α :=
  { SupₛHom.id α with toInfTopHom := InfTopHom.id α }
#align frame_hom.id FrameHom.id

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl
#align frame_hom.coe_id FrameHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl
#align frame_hom.id_apply FrameHom.id_apply

/-- Composition of `FrameHom`s as a `FrameHom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : SupₛHom β γ).comp (g : SupₛHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
#align frame_hom.comp FrameHom.comp

@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align frame_hom.coe_comp FrameHom.coe_comp

@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align frame_hom.comp_apply FrameHom.comp_apply

@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align frame_hom.comp_assoc FrameHom.comp_assoc

@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun _ => rfl
#align frame_hom.comp_id FrameHom.comp_id

@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun _ => rfl
#align frame_hom.id_comp FrameHom.id_comp

theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align frame_hom.cancel_right FrameHom.cancel_right

theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align frame_hom.cancel_left FrameHom.cancel_left

instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/


namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_supₛ f := f.map_supₛ'
  map_infₛ f := f.map_infₛ'

/-- Reinterpret a `CompleteLatticeHom` as a `SupₛHom`. -/
def toSupₛHom (f : CompleteLatticeHom α β) : SupₛHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.toSupₛHom

/-- Reinterpret a `CompleteLatticeHom` as a `BoundedLatticeHom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
#align complete_lattice_hom.to_bounded_lattice_hom CompleteLatticeHom.toBoundedLatticeHom

-- Porting note: We do not want CoeFun for this in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

/- Porting note: SimpNF linter complains that lhs can be simplified,
added _aux version with [simp] attribute -/
-- @[simp]
theorem toFun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = ⇑f :=
  rfl
#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coe

@[simp]
theorem toFun_eq_coe_aux {f : CompleteLatticeHom α β} : ↑f.toInfₛHom = ⇑f :=
  rfl

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext

/-- Copy of a `CompleteLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.toSupₛHom.copy f' h with toInfₛHom := f.toInfₛHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy

@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copy

theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eq

variable (α)

/-- `id` as a `CompleteLatticeHom`. -/
protected def id : CompleteLatticeHom α α :=
  { SupₛHom.id α, InfₛHom.id α with toFun := id }
#align complete_lattice_hom.id CompleteLatticeHom.id

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl
#align complete_lattice_hom.coe_id CompleteLatticeHom.coe_id

variable {α}
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl
#align complete_lattice_hom.id_apply CompleteLatticeHom.id_apply

/-- Composition of `CompleteLatticeHom`s as a `CompleteLatticeHom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.toSupₛHom.comp g.toSupₛHom with toInfₛHom := f.toInfₛHom.comp g.toInfₛHom }
#align complete_lattice_hom.comp CompleteLatticeHom.comp

@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_comp

@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
#align complete_lattice_hom.comp_apply CompleteLatticeHom.comp_apply

@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align complete_lattice_hom.comp_assoc CompleteLatticeHom.comp_assoc

@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun _ => rfl
#align complete_lattice_hom.comp_id CompleteLatticeHom.comp_id

@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun _ => rfl
#align complete_lattice_hom.id_comp CompleteLatticeHom.id_comp

theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_right

theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left

end CompleteLatticeHom

/-! ### Dual homs -/


namespace SupₛHom

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : SupₛHom α β ≃ InfₛHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_supₛ'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_infₛ'⟩
  left_inv _ := SupₛHom.ext fun _ => rfl
  right_inv _ := InfₛHom.ext fun _ => rfl
#align Sup_hom.dual SupₛHom.dual

@[simp]
theorem dual_id : SupₛHom.dual (SupₛHom.id α) = InfₛHom.id _ :=
  rfl
#align Sup_hom.dual_id SupₛHom.dual_id

@[simp]
theorem dual_comp (g : SupₛHom β γ) (f : SupₛHom α β) :
    SupₛHom.dual (g.comp f) = (SupₛHom.dual g).comp (SupₛHom.dual f) :=
  rfl
#align Sup_hom.dual_comp SupₛHom.dual_comp

@[simp]
theorem symm_dual_id : SupₛHom.dual.symm (InfₛHom.id _) = SupₛHom.id α :=
  rfl
#align Sup_hom.symm_dual_id SupₛHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : InfₛHom βᵒᵈ γᵒᵈ) (f : InfₛHom αᵒᵈ βᵒᵈ) :
    SupₛHom.dual.symm (g.comp f) = (SupₛHom.dual.symm g).comp (SupₛHom.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp SupₛHom.symm_dual_comp

end SupₛHom

namespace InfₛHom

variable [InfSet α] [InfSet β] [InfSet γ]

/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : InfₛHom α β ≃ SupₛHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_supₛ' := fun _ => congr_arg toDual (map_infₛ f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_infₛ' := fun _ => congr_arg ofDual (map_supₛ f _) }
  left_inv _ := InfₛHom.ext fun _ => rfl
  right_inv _ := SupₛHom.ext fun _ => rfl
#align Inf_hom.dual InfₛHom.dual

@[simp]
theorem dual_id : InfₛHom.dual (InfₛHom.id α) = SupₛHom.id _ :=
  rfl
#align Inf_hom.dual_id InfₛHom.dual_id

@[simp]
theorem dual_comp (g : InfₛHom β γ) (f : InfₛHom α β) :
    InfₛHom.dual (g.comp f) = (InfₛHom.dual g).comp (InfₛHom.dual f) :=
  rfl
#align Inf_hom.dual_comp InfₛHom.dual_comp

@[simp]
theorem symm_dual_id : InfₛHom.dual.symm (SupₛHom.id _) = InfₛHom.id α :=
  rfl
#align Inf_hom.symm_dual_id InfₛHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : SupₛHom βᵒᵈ γᵒᵈ) (f : SupₛHom αᵒᵈ βᵒᵈ) :
    InfₛHom.dual.symm (g.comp f) = (InfₛHom.dual.symm g).comp (InfₛHom.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp InfₛHom.symm_dual_comp

end InfₛHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps!]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨SupₛHom.dual f.toSupₛHom, fun s ↦ f.map_infₛ' s⟩
  invFun f := ⟨SupₛHom.dual f.toSupₛHom, fun s ↦ f.map_infₛ' s⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := ext fun _ => rfl
#align complete_lattice_hom.dual CompleteLatticeHom.dual

@[simp]
theorem dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.dual_id CompleteLatticeHom.dual_id

@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    CompleteLatticeHom.dual (g.comp f) =
      (CompleteLatticeHom.dual g).comp (CompleteLatticeHom.dual f) :=
  rfl
#align complete_lattice_hom.dual_comp CompleteLatticeHom.dual_comp

@[simp]
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl
#align complete_lattice_hom.symm_dual_id CompleteLatticeHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl
#align complete_lattice_hom.symm_dual_comp CompleteLatticeHom.symm_dual_comp

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/-- `Set.preimage` as a complete lattice homomorphism.

See also `SupₛHom.setImage`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_supₛ' s := preimage_unionₛ.trans <| by simp only [Set.supₛ_eq_unionₛ, Set.unionₛ_image]
  map_infₛ' s := preimage_interₛ.trans <| by simp only [Set.infₛ_eq_interₛ, Set.interₛ_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage

@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimage

@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.preimage f :=
  rfl
#align complete_lattice_hom.set_preimage_apply CompleteLatticeHom.setPreimage_apply

@[simp]
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.set_preimage_id CompleteLatticeHom.setPreimage_id

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl
#align complete_lattice_hom.set_preimage_comp CompleteLatticeHom.setPreimage_comp

end CompleteLatticeHom

theorem Set.image_supₛ {f : α → β} (s : Set (Set α)) : f '' supₛ s = supₛ (image f '' s) := by
  ext b
  simp only [supₛ_eq_unionₛ, mem_image, mem_unionₛ, exists_prop, unionₛ_image, mem_unionᵢ]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
#align set.image_Sup Set.image_supₛ

/-- Using `Set.image`, a function between types yields a `SupₛHom` between their lattices of
subsets.

See also `CompleteLatticeHom.setPreimage`. -/
@[simps]
def SupₛHom.setImage (f : α → β) : SupₛHom (Set α) (Set β)
    where
  toFun := image f
  map_supₛ' := Set.image_supₛ
#align Sup_hom.set_image SupₛHom.setImage

/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id.def, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id.def, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
#align equiv.to_order_iso_set Equiv.toOrderIsoSet

variable [CompleteLattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `SupₛHom`. -/
def supSupₛHom : SupₛHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_supₛ' s := by simp_rw [Prod.fst_supₛ, Prod.snd_supₛ, supₛ_image, supᵢ_sup_eq]
#align sup_Sup_hom supSupₛHom

/-- The map `(a, b) ↦ a ⊓ b` as an `InfₛHom`. -/
def infInfₛHom : InfₛHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_infₛ' s := by simp_rw [Prod.fst_infₛ, Prod.snd_infₛ, infₛ_image, infᵢ_inf_eq]
#align inf_Inf_hom infInfₛHom

@[simp, norm_cast]
theorem supSupₛHom_apply : supSupₛHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supSupₛHom_apply

@[simp, norm_cast]
theorem infInfₛHom_apply : infInfₛHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infInfₛHom_apply
