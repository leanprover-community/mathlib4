/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.hom.complete_lattice
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Hom.Lattice

/-!
# Complete lattice homomorphisms

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `Sup_hom`: Maps which preserve `⨆`.
* `Inf_hom`: Maps which preserve `⨅`.
* `frame_hom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `complete_lattice_hom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `Sup_hom_class`
* `Inf_hom_class`
* `frame_hom_class`
* `complete_lattice_hom_class`

## Concrete homs

* `complete_lattice.set_preimage`: `set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/


open Function OrderDual Set

variable {F α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure SupHomCat (α β : Type _) [SupSet α] [SupSet β] where
  toFun : α → β
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align Sup_hom SupHomCat

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure InfHomCat (α β : Type _) [InfSet α] [InfSet β] where
  toFun : α → β
  map_Inf' (s : Set α) : to_fun (infₛ s) = infₛ (to_fun '' s)
#align Inf_hom InfHomCat

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align frame_hom FrameHom

/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfHomCat α β where
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align complete_lattice_hom CompleteLatticeHom

section

/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class SupHomClassCat (F : Type _) (α β : outParam <| Type _) [SupSet α] [SupSet β] extends
  FunLike F α fun _ => β where
  map_Sup (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align Sup_hom_class SupHomClassCat

/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class InfHomClassCat (F : Type _) (α β : outParam <| Type _) [InfSet α] [InfSet β] extends
  FunLike F α fun _ => β where
  map_Inf (f : F) (s : Set α) : f (infₛ s) = infₛ (f '' s)
#align Inf_hom_class InfHomClassCat

/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfTopHomClass F α β where
  map_Sup (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align frame_hom_class FrameHomClass

/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfHomClassCat F α β where
  map_Sup (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass

end

export SupHomClassCat (map_Sup)

export InfHomClassCat (map_Inf)

attribute [simp] map_Sup map_Inf

theorem map_supᵢ [SupSet α] [SupSet β] [SupHomClassCat F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by rw [supᵢ, supᵢ, map_Sup, Set.range_comp]
#align map_supr map_supᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_supr₂ [SupSet α] [SupSet β] [SupHomClassCat F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_supᵢ]
#align map_supr₂ map_supr₂

theorem map_infᵢ [InfSet α] [InfSet β] [InfHomClassCat F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by rw [infᵢ, infᵢ, map_Inf, Set.range_comp]
#align map_infi map_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_infi₂ [InfSet α] [InfSet β] [InfHomClassCat F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_infᵢ]
#align map_infi₂ map_infi₂

-- See note [lower instance priority]
instance (priority := 100) SupHomClassCat.toSupBotHomClass [CompleteLattice α] [CompleteLattice β]
    [SupHomClassCat F α β] : SupBotHomClass F α β :=
  {
    ‹SupHomClassCat F α
        β› with
    map_sup := fun f a b => by rw [← supₛ_pair, map_Sup, Set.image_pair, supₛ_pair]
    map_bot := fun f => by rw [← supₛ_empty, map_Sup, Set.image_empty, supₛ_empty] }
#align Sup_hom_class.to_sup_bot_hom_class SupHomClassCat.toSupBotHomClass

-- See note [lower instance priority]
instance (priority := 100) InfHomClassCat.toInfTopHomClass [CompleteLattice α] [CompleteLattice β]
    [InfHomClassCat F α β] : InfTopHomClass F α β :=
  {
    ‹InfHomClassCat F α
        β› with
    map_inf := fun f a b => by rw [← infₛ_pair, map_Inf, Set.image_pair, infₛ_pair]
    map_top := fun f => by rw [← infₛ_empty, map_Inf, Set.image_empty, infₛ_empty] }
#align Inf_hom_class.to_inf_top_hom_class InfHomClassCat.toInfTopHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toSupHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : SupHomClassCat F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.toSupHomClass

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, SupHomClassCat.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, InfHomClassCat.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { SupHomClassCat.toSupBotHomClass, InfHomClassCat.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass

/- warning: order_iso_class.to_Sup_hom_class clashes with order_iso_class.to_sup_hom_class -> OrderIsoClass.toSupHomClass
warning: order_iso_class.to_Sup_hom_class -> OrderIsoClass.toSupHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], SupHomClassCat.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : SemilatticeSup.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2)))], SupHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Sup_hom_class OrderIsoClass.toSupHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : SupHomClassCat F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_Sup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, supₛ_le_iff, Set.ball_image_iff] }
#align order_iso_class.to_Sup_hom_class OrderIsoClass.toSupHomClass

/- warning: order_iso_class.to_Inf_hom_class clashes with order_iso_class.to_inf_hom_class -> OrderIsoClass.toInfHomClass
warning: order_iso_class.to_Inf_hom_class -> OrderIsoClass.toInfHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], InfHomClassCat.{u1, u2, u3} F α β (CompleteSemilatticeInf.toHasInf.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : SemilatticeInf.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_2)))], InfHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Inf_hom_class OrderIsoClass.toInfHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : InfHomClassCat F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_Inf := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_infₛ_iff, Set.ball_image_iff] }
#align order_iso_class.to_Inf_hom_class OrderIsoClass.toInfHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toLatticeHomClass,
    show InfHomClassCat F α β from inferInstance with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass

instance [SupSet α] [SupSet β] [SupHomClassCat F α β] : CoeTC F (SupHomCat α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [InfSet α] [InfSet β] [InfHomClassCat F α β] : CoeTC F (InfHomCat α β) :=
  ⟨fun f => ⟨f, map_infₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

/-! ### Supremum homomorphisms -/


namespace SupHomCat

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : SupHomClassCat (SupHomCat α β) α β
    where
  coe := SupHomCat.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_Sup := SupHomCat.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHomCat α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : SupHomCat α β} : f.toFun = (f : α → β) :=
  rfl
#align Sup_hom.to_fun_eq_coe SupHomCat.toFun_eq_coe

@[ext]
theorem ext {f g : SupHomCat α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext SupHomCat.ext

/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHomCat α β) (f' : α → β) (h : f' = f) : SupHomCat α β
    where
  toFun := f'
  map_Sup' := h.symm ▸ f.map_Sup'
#align Sup_hom.copy SupHomCat.copy

@[simp]
theorem coe_copy (f : SupHomCat α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy SupHomCat.coe_copy

theorem copy_eq (f : SupHomCat α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq SupHomCat.copy_eq

variable (α)

/-- `id` as a `Sup_hom`. -/
protected def id : SupHomCat α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id SupHomCat.id

instance : Inhabited (SupHomCat α α) :=
  ⟨SupHomCat.id α⟩

@[simp]
theorem coe_id : ⇑(SupHomCat.id α) = id :=
  rfl
#align Sup_hom.coe_id SupHomCat.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : SupHomCat.id α a = a :=
  rfl
#align Sup_hom.id_apply SupHomCat.id_apply

/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : SupHomCat β γ) (g : SupHomCat α β) : SupHomCat α γ
    where
  toFun := f ∘ g
  map_Sup' s := by rw [comp_apply, map_Sup, map_Sup, Set.image_image]
#align Sup_hom.comp SupHomCat.comp

@[simp]
theorem coe_comp (f : SupHomCat β γ) (g : SupHomCat α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp SupHomCat.coe_comp

@[simp]
theorem comp_apply (f : SupHomCat β γ) (g : SupHomCat α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply SupHomCat.comp_apply

@[simp]
theorem comp_assoc (f : SupHomCat γ δ) (g : SupHomCat β γ) (h : SupHomCat α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc SupHomCat.comp_assoc

@[simp]
theorem comp_id (f : SupHomCat α β) : f.comp (SupHomCat.id α) = f :=
  ext fun a => rfl
#align Sup_hom.comp_id SupHomCat.comp_id

@[simp]
theorem id_comp (f : SupHomCat α β) : (SupHomCat.id β).comp f = f :=
  ext fun a => rfl
#align Sup_hom.id_comp SupHomCat.id_comp

theorem cancel_right {g₁ g₂ : SupHomCat β γ} {f : SupHomCat α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Sup_hom.cancel_right SupHomCat.cancel_right

theorem cancel_left {g : SupHomCat β γ} {f₁ f₂ : SupHomCat α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Sup_hom.cancel_left SupHomCat.cancel_left

end SupSet

variable [CompleteLattice β]

instance : PartialOrder (SupHomCat α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (SupHomCat α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, supₛ_empty]
      · rw [hs.image_const, supₛ_singleton]⟩⟩

instance : OrderBot (SupHomCat α β) :=
  ⟨⊥, fun f a => bot_le⟩

@[simp]
theorem coe_bot : ⇑(⊥ : SupHomCat α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot SupHomCat.coe_bot

@[simp]
theorem bot_apply (a : α) : (⊥ : SupHomCat α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply SupHomCat.bot_apply

end SupHomCat

/-! ### Infimum homomorphisms -/


namespace InfHomCat

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : InfHomClassCat (InfHomCat α β) α β
    where
  coe := InfHomCat.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_Inf := InfHomCat.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHomCat α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : InfHomCat α β} : f.toFun = (f : α → β) :=
  rfl
#align Inf_hom.to_fun_eq_coe InfHomCat.toFun_eq_coe

@[ext]
theorem ext {f g : InfHomCat α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext InfHomCat.ext

/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHomCat α β) (f' : α → β) (h : f' = f) : InfHomCat α β
    where
  toFun := f'
  map_Inf' := h.symm ▸ f.map_Inf'
#align Inf_hom.copy InfHomCat.copy

@[simp]
theorem coe_copy (f : InfHomCat α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy InfHomCat.coe_copy

theorem copy_eq (f : InfHomCat α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq InfHomCat.copy_eq

variable (α)

/-- `id` as an `Inf_hom`. -/
protected def id : InfHomCat α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id InfHomCat.id

instance : Inhabited (InfHomCat α α) :=
  ⟨InfHomCat.id α⟩

@[simp]
theorem coe_id : ⇑(InfHomCat.id α) = id :=
  rfl
#align Inf_hom.coe_id InfHomCat.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : InfHomCat.id α a = a :=
  rfl
#align Inf_hom.id_apply InfHomCat.id_apply

/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : InfHomCat β γ) (g : InfHomCat α β) : InfHomCat α γ
    where
  toFun := f ∘ g
  map_Inf' s := by rw [comp_apply, map_Inf, map_Inf, Set.image_image]
#align Inf_hom.comp InfHomCat.comp

@[simp]
theorem coe_comp (f : InfHomCat β γ) (g : InfHomCat α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp InfHomCat.coe_comp

@[simp]
theorem comp_apply (f : InfHomCat β γ) (g : InfHomCat α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply InfHomCat.comp_apply

@[simp]
theorem comp_assoc (f : InfHomCat γ δ) (g : InfHomCat β γ) (h : InfHomCat α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc InfHomCat.comp_assoc

@[simp]
theorem comp_id (f : InfHomCat α β) : f.comp (InfHomCat.id α) = f :=
  ext fun a => rfl
#align Inf_hom.comp_id InfHomCat.comp_id

@[simp]
theorem id_comp (f : InfHomCat α β) : (InfHomCat.id β).comp f = f :=
  ext fun a => rfl
#align Inf_hom.id_comp InfHomCat.id_comp

theorem cancel_right {g₁ g₂ : InfHomCat β γ} {f : InfHomCat α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Inf_hom.cancel_right InfHomCat.cancel_right

theorem cancel_left {g : InfHomCat β γ} {f₁ f₂ : InfHomCat α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Inf_hom.cancel_left InfHomCat.cancel_left

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (InfHomCat α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (InfHomCat α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, infₛ_empty]
      · rw [hs.image_const, infₛ_singleton]⟩⟩

instance : OrderTop (InfHomCat α β) :=
  ⟨⊤, fun f a => le_top⟩

@[simp]
theorem coe_top : ⇑(⊤ : InfHomCat α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top InfHomCat.coe_top

@[simp]
theorem top_apply (a : α) : (⊤ : InfHomCat α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply InfHomCat.top_apply

end InfHomCat

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
  map_Sup f := f.map_Sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (FrameHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
#align frame_hom.to_lattice_hom FrameHom.toLatticeHom

@[simp]
theorem toFun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl
#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coe

@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align frame_hom.ext FrameHom.ext

/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : SupHomCat α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy

@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align frame_hom.coe_copy FrameHom.coe_copy

theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align frame_hom.copy_eq FrameHom.copy_eq

variable (α)

/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { SupHomCat.id α with toInfTopHom := InfTopHom.id α }
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

/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : SupHomCat β γ).comp (g : SupHomCat α β) with
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
  ext fun a => rfl
#align frame_hom.comp_id FrameHom.comp_id

@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun a => rfl
#align frame_hom.id_comp FrameHom.id_comp

theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
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
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_Sup f := f.map_Sup'
  map_Inf f := f.map_Inf'

/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def toSupHom (f : CompleteLatticeHom α β) : SupHomCat α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.toSupHom

/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
#align complete_lattice_hom.to_bounded_lattice_hom CompleteLatticeHom.toBoundedLatticeHom

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coe

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext

/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.toSupHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy

@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copy

theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eq

variable (α)

/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { SupHomCat.id α, InfHomCat.id α with toFun := id }
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

/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom with toInfHom := f.toInfHom.comp g.toInfHom }
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
  ext fun a => rfl
#align complete_lattice_hom.comp_id CompleteLatticeHom.comp_id

@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun a => rfl
#align complete_lattice_hom.id_comp CompleteLatticeHom.id_comp

theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_right

theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left

end CompleteLatticeHom

/-! ### Dual homs -/


namespace SupHomCat

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : SupHomCat α β ≃ InfHomCat αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨to_dual ∘ f ∘ of_dual, f.map_Sup'⟩
  invFun f := ⟨of_dual ∘ f ∘ to_dual, f.map_Inf'⟩
  left_inv f := SupHomCat.ext fun a => rfl
  right_inv f := InfHomCat.ext fun a => rfl
#align Sup_hom.dual SupHomCat.dual

@[simp]
theorem dual_id : (SupHomCat.id α).dual = InfHomCat.id _ :=
  rfl
#align Sup_hom.dual_id SupHomCat.dual_id

@[simp]
theorem dual_comp (g : SupHomCat β γ) (f : SupHomCat α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Sup_hom.dual_comp SupHomCat.dual_comp

@[simp]
theorem symm_dual_id : SupHomCat.dual.symm (InfHomCat.id _) = SupHomCat.id α :=
  rfl
#align Sup_hom.symm_dual_id SupHomCat.symm_dual_id

@[simp]
theorem symm_dual_comp (g : InfHomCat βᵒᵈ γᵒᵈ) (f : InfHomCat αᵒᵈ βᵒᵈ) :
    SupHomCat.dual.symm (g.comp f) = (SupHomCat.dual.symm g).comp (SupHomCat.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp SupHomCat.symm_dual_comp

end SupHomCat

namespace InfHomCat

variable [InfSet α] [InfSet β] [InfSet γ]

/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : InfHomCat α β ≃ SupHomCat αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := to_dual ∘ f ∘ of_dual
      map_Sup' := fun _ => congr_arg toDual (map_infₛ f _) }
  invFun f :=
    { toFun := of_dual ∘ f ∘ to_dual
      map_Inf' := fun _ => congr_arg ofDual (map_supₛ f _) }
  left_inv f := InfHomCat.ext fun a => rfl
  right_inv f := SupHomCat.ext fun a => rfl
#align Inf_hom.dual InfHomCat.dual

@[simp]
theorem dual_id : (InfHomCat.id α).dual = SupHomCat.id _ :=
  rfl
#align Inf_hom.dual_id InfHomCat.dual_id

@[simp]
theorem dual_comp (g : InfHomCat β γ) (f : InfHomCat α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Inf_hom.dual_comp InfHomCat.dual_comp

@[simp]
theorem symm_dual_id : InfHomCat.dual.symm (SupHomCat.id _) = InfHomCat.id α :=
  rfl
#align Inf_hom.symm_dual_id InfHomCat.symm_dual_id

@[simp]
theorem symm_dual_comp (g : SupHomCat βᵒᵈ γᵒᵈ) (f : SupHomCat αᵒᵈ βᵒᵈ) :
    InfHomCat.dual.symm (g.comp f) = (InfHomCat.dual.symm g).comp (InfHomCat.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp InfHomCat.symm_dual_comp

end InfHomCat

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toSupHom.dual, f.map_Inf'⟩
  invFun f := ⟨f.toSupHom.dual, f.map_Inf'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl
#align complete_lattice_hom.dual CompleteLatticeHom.dual

@[simp]
theorem dual_id : (CompleteLatticeHom.id α).dual = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.dual_id CompleteLatticeHom.dual_id

@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
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

/-- `set.preimage` as a complete lattice homomorphism.

See also `Sup_hom.set_image`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_Sup' s := preimage_unionₛ.trans <| by simp only [Set.supₛ_eq_unionₛ, Set.unionₛ_image]
  map_Inf' s := preimage_interₛ.trans <| by simp only [Set.infₛ_eq_interₛ, Set.interₛ_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage

@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimage

@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.Preimage f :=
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

theorem Set.image_supₛ {f : α → β} (s : Set (Set α)) : f '' supₛ s = supₛ (image f '' s) :=
  by
  ext b
  simp only [Sup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_Union]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
#align set.image_Sup Set.image_supₛ

/-- Using `set.image`, a function between types yields a `Sup_hom` between their lattices of
subsets.

See also `complete_lattice_hom.set_preimage`. -/
@[simps]
def SupHomCat.setImage (f : α → β) : SupHomCat (Set α) (Set β)
    where
  toFun := image f
  map_Sup' := Set.image_supₛ
#align Sup_hom.set_image SupHomCat.setImage

/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun := image e
  invFun := image e.symm
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id.def, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id.def, image_id']
  map_rel_iff' s t :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
#align equiv.to_order_iso_set Equiv.toOrderIsoSet

variable [CompleteLattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `Sup_hom`. -/
def supSupHom : SupHomCat (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_Sup' s := by simp_rw [Prod.fst_supₛ, Prod.snd_supₛ, supₛ_image, supᵢ_sup_eq]
#align sup_Sup_hom supSupHom

/-- The map `(a, b) ↦ a ⊓ b` as an `Inf_hom`. -/
def infInfHom : InfHomCat (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_Inf' s := by simp_rw [Prod.fst_infₛ, Prod.snd_infₛ, infₛ_image, infᵢ_inf_eq]
#align inf_Inf_hom infInfHom

@[simp, norm_cast]
theorem supSupHom_apply : supSupHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supSupHom_apply

@[simp, norm_cast]
theorem infInfHom_apply : infInfHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infInfHom_apply

