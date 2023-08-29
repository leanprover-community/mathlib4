/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Lattice

#align_import order.hom.complete_lattice from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Complete lattice homomorphisms

This file defines frame homomorphisms and complete lattice homomorphisms.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
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


open Function OrderDual Set

variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

-- Porting note: mathport made this & sInfHom into "SupHomCat" and "InfHomCat".
/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α → β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align Sup_hom sSupHom

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  /-- The underlying function of an `sInfHom`. -/
  toFun : α → β
  /-- The proposition that a `sInfHom` commutes with arbitrary infima/meets -/
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)
#align Inf_hom sInfHom

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align frame_hom FrameHom


/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β where
  /-- The proposition that complete lattice homomorphism commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align complete_lattice_hom CompleteLatticeHom

section

-- Porting note: mathport made this & InfHomClass into "SupHomClassCat" and "InfHomClassCat".
/-- `sSupHomClass F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `sSupHom`. -/
class sSupHomClass (F : Type*) (α β : outParam <| Type*) [SupSet α] [SupSet β] extends
  FunLike F α fun _ => β where
  /-- The proposition that members of `sSupHomClass`s commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align Sup_hom_class sSupHomClass

/-- `sInfHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `sInfHom`. -/
class sInfHomClass (F : Type*) (α β : outParam <| Type*) [InfSet α] [InfSet β] extends
  FunLike F α fun _ => β where
  /-- The proposition that members of `sInfHomClass`s commute with arbitrary infima/meets. -/
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)
#align Inf_hom_class sInfHomClass

/-- `FrameHomClass F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `FrameHom`. -/
class FrameHomClass (F : Type*) (α β : outParam <| Type*) [CompleteLattice α]
  [CompleteLattice β] extends InfTopHomClass F α β where
  /-- The proposition that members of `FrameHomClass` commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align frame_hom_class FrameHomClass

/-- `CompleteLatticeHomClass F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `CompleteLatticeHom`. -/
class CompleteLatticeHomClass (F : Type*) (α β : outParam <| Type*) [CompleteLattice α]
  [CompleteLattice β] extends sInfHomClass F α β where
  /-- The proposition that members of `CompleteLatticeHomClass` commute with arbitrary
  suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass

end

export sSupHomClass (map_sSup)

export sInfHomClass (map_sInf)

attribute [simp] map_sSup map_sInf

theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [iSup, ← Set.range_comp, Function.comp]
                                      -- 🎉 no goals
#align map_supr map_iSup

theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]
                                                      -- 🎉 no goals
#align map_supr₂ map_iSup₂

theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by simp [iInf, ← Set.range_comp, Function.comp]
                                      -- 🎉 no goals
#align map_infi map_iInf

theorem map_iInf₂ [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_iInf]
                                                      -- 🎉 no goals
#align map_infi₂ map_iInf

-- See note [lower instance priority]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [sSupHomClass F α β] : SupBotHomClass F α β :=
  {  ‹sSupHomClass F α β› with
    map_sup := fun f a b => by
      rw [← sSup_pair, map_sSup]
      -- ⊢ sSup (↑f '' {a, b}) = ↑f a ⊔ ↑f b
      simp only [Set.image_pair, sSup_insert, sSup_singleton]
      -- 🎉 no goals
    map_bot := fun f => by
      rw [← sSup_empty, map_sSup, Set.image_empty]
      -- ⊢ sSup ∅ = ⊥
      -- Porting note: rw [sSup_empty] does not work, but exact sSup_empty does?
      exact sSup_empty }
      -- 🎉 no goals
#align Sup_hom_class.to_sup_bot_hom_class sSupHomClass.toSupBotHomClass

-- See note [lower instance priority]
instance (priority := 100) sInfHomClass.toInfTopHomClass [CompleteLattice α]
    [CompleteLattice β] [sInfHomClass F α β] : InfTopHomClass F α β :=
  { ‹sInfHomClass F α β› with
    map_inf := fun f a b => by
      rw [← sInf_pair, map_sInf, Set.image_pair]
      -- ⊢ sInf {↑f a, ↑f b} = ↑f a ⊓ ↑f b
      simp only [Set.image_pair, sInf_insert, sInf_singleton]
      -- 🎉 no goals
    map_top := fun f => by
      rw [← sInf_empty, map_sInf, Set.image_empty]
      -- ⊢ sInf ∅ = ⊤
      -- Porting note: rw [sInf_empty] does not work, but exact sInf_empty does?
      exact sInf_empty }
      -- 🎉 no goals
#align Inf_hom_class.to_inf_top_hom_class sInfHomClass.toInfTopHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.tosSupHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sSupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sSup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sSup_le_iff, Set.ball_image_iff] }
        -- 🎉 no goals
#align order_iso_class.to_Sup_hom_class OrderIsoClass.tosSupHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosInfHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sInfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sInf := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_sInf_iff, Set.ball_image_iff] }
        -- 🎉 no goals
#align order_iso_class.to_Inf_hom_class OrderIsoClass.tosInfHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  -- Porting note: Used to be:
    -- { OrderIsoClass.tosSupHomClass, OrderIsoClass.toLatticeHomClass,
    -- show sInfHomClass F α β from inferInstance with }
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.tosInfHomClass with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass

instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [InfSet α] [InfSet β] [sInfHomClass F α β] : CoeTC F (sInfHom α β) :=
  ⟨fun f => ⟨f, map_sInf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum homomorphisms -/


namespace sSupHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : sSupHomClass (sSupHom α β) α β
    where
  coe := sSupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, map_sSup' := map_sSup'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, map_sSup' := map_sSup'✝¹ } = { toFun := toFun✝, map_sSup …
                                               -- 🎉 no goals
  map_sSup := sSupHom.map_sSup'

-- Porting note: We do not want CoeFun for this in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `funLike.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (sSupHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

-- Porting note: times out
@[simp]
theorem toFun_eq_coe {f : sSupHom α β} : f.toFun = ⇑f  :=
  rfl
#align Sup_hom.to_fun_eq_coe sSupHom.toFun_eq_coe

@[ext]
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext sSupHom.ext

/-- Copy of a `sSupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β
    where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'
#align Sup_hom.copy sSupHom.copy

@[simp]
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy sSupHom.coe_copy

theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq sSupHom.copy_eq

variable (α)

/-- `id` as a `sSupHom`. -/
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
                   -- 🎉 no goals
#align Sup_hom.id sSupHom.id

instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

@[simp]
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl
#align Sup_hom.coe_id sSupHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl
#align Sup_hom.id_apply sSupHom.id_apply

/-- Composition of `sSupHom`s as a `sSupHom`. -/
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ
    where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]
                    -- ⊢ sSup ((fun x => ↑f (↑g x)) '' s) = sSup (↑f ∘ ↑g '' s)
                                                                          -- 🎉 no goals
#align Sup_hom.comp sSupHom.comp

@[simp]
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp sSupHom.coe_comp

@[simp]
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply sSupHom.comp_apply

@[simp]
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc sSupHom.comp_assoc

@[simp]
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun _ => rfl
#align Sup_hom.comp_id sSupHom.comp_id

@[simp]
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun _ => rfl
#align Sup_hom.id_comp sSupHom.id_comp

theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align Sup_hom.cancel_right sSupHom.cancel_right

theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align Sup_hom.cancel_left sSupHom.cancel_left

end SupSet

variable { _ : CompleteLattice β}

instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      -- ⊢ (fun x => ⊥) (sSup ∅) = sSup ((fun x => ⊥) '' ∅)
      · rw [Set.image_empty, sSup_empty]
        -- 🎉 no goals
      · rw [hs.image_const, sSup_singleton]⟩⟩
        -- 🎉 no goals

instance : OrderBot (sSupHom α β) where
  bot := ⊥
  bot_le := fun _ _ ↦ CompleteLattice.bot_le _

@[simp]
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot sSupHom.coe_bot

@[simp]
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply sSupHom.bot_apply

end sSupHom

/-! ### Infimum homomorphisms -/


namespace sInfHom

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : sInfHomClass (sInfHom α β) α β
    where
  coe := sInfHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, map_sInf' := map_sInf'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, map_sInf' := map_sInf'✝¹ } = { toFun := toFun✝, map_sInf …
                                               -- 🎉 no goals
  map_sInf := sInfHom.map_sInf'

-- Porting note: Do not want these CoeFun instances in lean4
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_toFun`
-- directly. -/
-- instance : CoeFun (sInfHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : sInfHom α β} : f.toFun = ⇑f :=
  rfl
#align Inf_hom.to_fun_eq_coe sInfHom.toFun_eq_coe

@[ext]
theorem ext {f g : sInfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext sInfHom.ext

/-- Copy of a `sInfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : sInfHom α β
    where
  toFun := f'
  map_sInf' := h.symm ▸ f.map_sInf'
#align Inf_hom.copy sInfHom.copy

@[simp]
theorem coe_copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy sInfHom.coe_copy

theorem copy_eq (f : sInfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq sInfHom.copy_eq

variable (α)

/-- `id` as an `sInfHom`. -/
protected def id : sInfHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
                   -- 🎉 no goals
#align Inf_hom.id sInfHom.id

instance : Inhabited (sInfHom α α) :=
  ⟨sInfHom.id α⟩

@[simp]
theorem coe_id : ⇑(sInfHom.id α) = id :=
  rfl
#align Inf_hom.coe_id sInfHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : sInfHom.id α a = a :=
  rfl
#align Inf_hom.id_apply sInfHom.id_apply

/-- Composition of `sInfHom`s as a `sInfHom`. -/
def comp (f : sInfHom β γ) (g : sInfHom α β) : sInfHom α γ
    where
  toFun := f ∘ g
  map_sInf' s := by rw [comp_apply, map_sInf, map_sInf, Set.image_image]; simp only [Function.comp]
                    -- ⊢ sInf ((fun x => ↑f (↑g x)) '' s) = sInf (↑f ∘ ↑g '' s)
                                                                          -- 🎉 no goals
#align Inf_hom.comp sInfHom.comp

@[simp]
theorem coe_comp (f : sInfHom β γ) (g : sInfHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp sInfHom.coe_comp

@[simp]
theorem comp_apply (f : sInfHom β γ) (g : sInfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply sInfHom.comp_apply

@[simp]
theorem comp_assoc (f : sInfHom γ δ) (g : sInfHom β γ) (h : sInfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc sInfHom.comp_assoc

@[simp]
theorem comp_id (f : sInfHom α β) : f.comp (sInfHom.id α) = f :=
  ext fun _ => rfl
#align Inf_hom.comp_id sInfHom.comp_id

@[simp]
theorem id_comp (f : sInfHom α β) : (sInfHom.id β).comp f = f :=
  ext fun _ => rfl
#align Inf_hom.id_comp sInfHom.id_comp

theorem cancel_right {g₁ g₂ : sInfHom β γ} {f : sInfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align Inf_hom.cancel_right sInfHom.cancel_right

theorem cancel_left {g : sInfHom β γ} {f₁ f₂ : sInfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align Inf_hom.cancel_left sInfHom.cancel_left

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (sInfHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (sInfHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      -- ⊢ (fun x => ⊤) (sInf ∅) = sInf ((fun x => ⊤) '' ∅)
      · rw [Set.image_empty, sInf_empty]
        -- 🎉 no goals
      · rw [hs.image_const, sInf_singleton]⟩⟩
        -- 🎉 no goals

instance : OrderTop (sInfHom α β) where
  top := ⊤
  le_top := fun _ _ => CompleteLattice.le_top _

@[simp]
theorem coe_top : ⇑(⊤ : sInfHom α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top sInfHom.coe_top

@[simp]
theorem top_apply (a : α) : (⊤ : sInfHom α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply sInfHom.top_apply

end sInfHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    -- ⊢ { toInfTopHom := { toInfHom := { toFun := toFun✝, map_inf' := map_inf'✝ }, m …
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    -- ⊢ { toInfTopHom := { toInfHom := { toFun := toFun✝¹, map_inf' := map_inf'✝¹ }, …
    congr
    -- 🎉 no goals
  map_sSup f := f.map_sSup'
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
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
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
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
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
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
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
                                  -- 🎉 no goals
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
                             -- ⊢ { tosInfHom := { toFun := toFun✝, map_sInf' := map_sInf'✝ }, map_sSup' := ma …
                                                      -- ⊢ { tosInfHom := { toFun := toFun✝¹, map_sInf' := map_sInf'✝¹ }, map_sSup' :=  …
                                                                               -- 🎉 no goals
  map_sSup f := f.map_sSup'
  map_sInf f := f.map_sInf'

/-- Reinterpret a `CompleteLatticeHom` as a `sSupHom`. -/
def tosSupHom (f : CompleteLatticeHom α β) : sSupHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.tosSupHom

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
theorem toFun_eq_coe_aux {f : CompleteLatticeHom α β} : ↑f.tosInfHom = ⇑f :=
  rfl

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext

/-- Copy of a `CompleteLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }
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
  { sSupHom.id α, sInfHom.id α with toFun := id }
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
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }
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
                                  -- 🎉 no goals
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩
  left_inv _ := sSupHom.ext fun _ => rfl
  right_inv _ := sInfHom.ext fun _ => rfl
#align Sup_hom.dual sSupHom.dual

@[simp]
theorem dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _ :=
  rfl
#align Sup_hom.dual_id sSupHom.dual_id

@[simp]
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) :
    sSupHom.dual (g.comp f) = (sSupHom.dual g).comp (sSupHom.dual f) :=
  rfl
#align Sup_hom.dual_comp sSupHom.dual_comp

@[simp]
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl
#align Sup_hom.symm_dual_id sSupHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp sSupHom.symm_dual_comp

end sSupHom

namespace sInfHom

variable [InfSet α] [InfSet β] [InfSet γ]

/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sInfHom α β ≃ sSupHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_sSup' := fun _ => congr_arg toDual (map_sInf f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_sInf' := fun _ => congr_arg ofDual (map_sSup f _) }
  left_inv _ := sInfHom.ext fun _ => rfl
  right_inv _ := sSupHom.ext fun _ => rfl
#align Inf_hom.dual sInfHom.dual

@[simp]
theorem dual_id : sInfHom.dual (sInfHom.id α) = sSupHom.id _ :=
  rfl
#align Inf_hom.dual_id sInfHom.dual_id

@[simp]
theorem dual_comp (g : sInfHom β γ) (f : sInfHom α β) :
    sInfHom.dual (g.comp f) = (sInfHom.dual g).comp (sInfHom.dual f) :=
  rfl
#align Inf_hom.dual_comp sInfHom.dual_comp

@[simp]
theorem symm_dual_id : sInfHom.dual.symm (sSupHom.id _) = sInfHom.id α :=
  rfl
#align Inf_hom.symm_dual_id sInfHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : sSupHom βᵒᵈ γᵒᵈ) (f : sSupHom αᵒᵈ βᵒᵈ) :
    sInfHom.dual.symm (g.comp f) = (sInfHom.dual.symm g).comp (sInfHom.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp sInfHom.symm_dual_comp

end sInfHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps!]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
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

See also `sSupHom.setImage`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_sSup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
                                             -- 🎉 no goals
                                             -- 🎉 no goals
  map_sInf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]
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

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` syntactically)
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl
#align complete_lattice_hom.set_preimage_comp CompleteLatticeHom.setPreimage_comp

end CompleteLatticeHom

theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) := by
  ext b
  -- ⊢ b ∈ f '' sSup s ↔ b ∈ sSup (image f '' s)
  simp only [sSup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_iUnion]
  -- ⊢ (∃ x, (∃ t, t ∈ s ∧ x ∈ t) ∧ f x = b) ↔ ∃ i, i ∈ s ∧ ∃ x, x ∈ i ∧ f x = b
  constructor
  -- ⊢ (∃ x, (∃ t, t ∈ s ∧ x ∈ t) ∧ f x = b) → ∃ i, i ∈ s ∧ ∃ x, x ∈ i ∧ f x = b
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    -- ⊢ ∃ i, i ∈ s ∧ ∃ x, x ∈ i ∧ f x = f a
    exact ⟨t, ht₁, a, ht₂, rfl⟩
    -- 🎉 no goals
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    -- ⊢ ∃ x, (∃ t, t ∈ s ∧ x ∈ t) ∧ f x = f a
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    -- 🎉 no goals
#align set.image_Sup Set.image_sSup

/-- Using `Set.image`, a function between types yields a `sSupHom` between their lattices of
subsets.

See also `CompleteLatticeHom.setPreimage`. -/
@[simps]
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β)
    where
  toFun := image f
  map_sSup' := Set.image_sSup
#align Sup_hom.set_image sSupHom.setImage

/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id.def, image_id']
                   -- 🎉 no goals
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id.def, image_id']
                    -- 🎉 no goals
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
                 -- 🎉 no goals
#align equiv.to_order_iso_set Equiv.toOrderIsoSet

variable [CompleteLattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `sSupHom`. -/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
                    -- 🎉 no goals
#align sup_Sup_hom supsSupHom

/-- The map `(a, b) ↦ a ⊓ b` as an `sInfHom`. -/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]
                    -- 🎉 no goals
#align inf_Inf_hom infsInfHom

@[simp, norm_cast]
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supsSupHom_apply

@[simp, norm_cast]
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infsInfHom_apply
