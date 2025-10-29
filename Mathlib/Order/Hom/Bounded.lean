/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Basic

/-!
# Bounded order homomorphisms

This file defines (bounded) order homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `TopHom`: Maps which preserve `⊤`.
* `BotHom`: Maps which preserve `⊥`.
* `BoundedOrderHom`: Bounded order homomorphisms. Monotone maps which preserve `⊤` and `⊥`.

## Typeclasses

* `TopHomClass`
* `BotHomClass`
* `BoundedOrderHomClass`
-/


open Function OrderDual

variable {F α β γ δ : Type*}

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
structure TopHom (α β : Type*) [Top α] [Top β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α → β
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
structure BotHom (α β : Type*) [Bot α] [Bot β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α → β
  /-- The function preserves the bottom element. The preferred spelling is `map_bot`. -/
  map_bot' : toFun ⊥ = ⊥

/-- The type of bounded order homomorphisms from `α` to `β`. -/
structure BoundedOrderHom (α β : Type*) [Preorder α] [Preorder β] [BoundedOrder α]
  [BoundedOrder β] extends OrderHom α β where
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤
  /-- The function preserves the bottom element. The preferred spelling is `map_bot`. -/
  map_bot' : toFun ⊥ = ⊥

section

/-- `TopHomClass F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `TopHom`. -/
class TopHomClass (F : Type*) (α β : outParam Type*) [Top α] [Top β] [FunLike F α β] :
    Prop where
  /-- A `TopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/-- `BotHomClass F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `BotHom`. -/
class BotHomClass (F : Type*) (α β : outParam Type*) [Bot α] [Bot β] [FunLike F α β] :
    Prop where
  /-- A `BotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/-- `BoundedOrderHomClass F α β` states that `F` is a type of bounded order morphisms.

You should extend this class when you extend `BoundedOrderHom`. -/
class BoundedOrderHomClass (F α β : Type*) [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [FunLike F α β] : Prop
  extends RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
  /-- Morphisms preserve the top element. The preferred spelling is `_root_.map_top`. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- Morphisms preserve the bottom element. The preferred spelling is `_root_.map_bot`. -/
  map_bot (f : F) : f ⊥ = ⊥

end

export TopHomClass (map_top)

export BotHomClass (map_bot)

attribute [simp] map_top map_bot

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
instance (priority := 100) BoundedOrderHomClass.toTopHomClass [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] : TopHomClass F α β :=
  { ‹BoundedOrderHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedOrderHomClass.toBotHomClass [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] : BotHomClass F α β :=
  { ‹BoundedOrderHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toTopHomClass [LE α] [OrderTop α]
    [PartialOrder β] [OrderTop β] [OrderIsoClass F α β] : TopHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_top := fun f => top_le_iff.1 <| (map_inv_le_iff f).1 le_top }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBotHomClass [LE α] [OrderBot α]
    [PartialOrder β] [OrderBot β] [OrderIsoClass F α β] : BotHomClass F α β :=
  { map_bot := fun f => le_bot_iff.1 <| (le_map_inv_iff f).1 bot_le }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedOrderHomClass [LE α] [BoundedOrder α]
    [PartialOrder β] [BoundedOrder β] [OrderIsoClass F α β] : BoundedOrderHomClass F α β :=
  { show OrderHomClass F α β from inferInstance, OrderIsoClass.toTopHomClass,
    OrderIsoClass.toBotHomClass with }

@[simp]
theorem map_eq_top_iff [LE α] [OrderTop α] [PartialOrder β] [OrderTop β] [OrderIsoClass F α β]
    (f : F) {a : α} : f a = ⊤ ↔ a = ⊤ := by
  rw [← map_top f, (EquivLike.injective f).eq_iff]

@[simp]
theorem map_eq_bot_iff [LE α] [OrderBot α] [PartialOrder β] [OrderBot β] [OrderIsoClass F α β]
    (f : F) {a : α} : f a = ⊥ ↔ a = ⊥ := by
  rw [← map_bot f, (EquivLike.injective f).eq_iff]

end Equiv

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `TopHomClass F α β` into an actual
`TopHom`. This is declared as the default coercion from `F` to `TopHom α β`. -/
@[coe]
def TopHomClass.toTopHom [Top α] [Top β] [TopHomClass F α β] (f : F) : TopHom α β :=
  ⟨f, map_top f⟩

instance [Top α] [Top β] [TopHomClass F α β] : CoeTC F (TopHom α β) :=
  ⟨TopHomClass.toTopHom⟩

/-- Turn an element of a type `F` satisfying `BotHomClass F α β` into an actual
`BotHom`. This is declared as the default coercion from `F` to `BotHom α β`. -/
@[coe]
def BotHomClass.toBotHom [Bot α] [Bot β] [BotHomClass F α β] (f : F) : BotHom α β :=
  ⟨f, map_bot f⟩

instance [Bot α] [Bot β] [BotHomClass F α β] : CoeTC F (BotHom α β) :=
  ⟨BotHomClass.toBotHom⟩

/-- Turn an element of a type `F` satisfying `BoundedOrderHomClass F α β` into an actual
`BoundedOrderHom`. This is declared as the default coercion from `F` to `BoundedOrderHom α β`. -/
@[coe]
def BoundedOrderHomClass.toBoundedOrderHom [Preorder α] [Preorder β] [BoundedOrder α]
    [BoundedOrder β] [BoundedOrderHomClass F α β] (f : F) : BoundedOrderHom α β :=
  { (f : α →o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }

instance [Preorder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] :
    CoeTC F (BoundedOrderHom α β) :=
  ⟨BoundedOrderHomClass.toBoundedOrderHom⟩

/-! ### Top homomorphisms -/


namespace TopHom

variable [Top α]

section Top

variable [Top β] [Top γ] [Top δ]

instance : FunLike (TopHom α β) α β where
  coe := TopHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : TopHomClass (TopHom α β) α β where
  map_top := TopHom.map_top'

-- this must come after the coe_to_fun definition
initialize_simps_projections TopHom (toFun → apply)

@[ext]
theorem ext {f g : TopHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `TopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : TopHom α β) (f' : α → β) (h : f' = f) :
    TopHom α β where
  toFun := f'
  map_top' := h.symm ▸ f.map_top'

@[simp]
theorem coe_copy (f : TopHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : TopHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

instance : Inhabited (TopHom α β) :=
  ⟨⟨fun _ => ⊤, rfl⟩⟩

variable (α)

/-- `id` as a `TopHom`. -/
protected def id : TopHom α α :=
  ⟨id, rfl⟩

@[simp, norm_cast]
theorem coe_id : ⇑(TopHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : TopHom.id α a = a :=
  rfl

/-- Composition of `TopHom`s as a `TopHom`. -/
def comp (f : TopHom β γ) (g : TopHom α β) :
    TopHom α γ where
  toFun := f ∘ g
  map_top' := by rw [comp_apply, map_top, map_top]

@[simp]
theorem coe_comp (f : TopHom β γ) (g : TopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : TopHom α β) : f.comp (TopHom.id α) = f :=
  TopHom.ext fun _ => rfl

@[simp]
theorem id_comp (f : TopHom α β) : (TopHom.id β).comp f = f :=
  TopHom.ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => TopHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun g => comp g f)⟩

@[simp]
theorem cancel_left {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => TopHom.ext fun a => hg <| by rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

end Top

instance instLE [LE β] [Top β] : LE (TopHom α β) where
  le f g := (f : α → β) ≤ g

instance [Preorder β] [Top β] : Preorder (TopHom α β) :=
  Preorder.lift (DFunLike.coe : TopHom α β → α → β)

instance [PartialOrder β] [Top β] : PartialOrder (TopHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

section OrderTop

variable [LE β] [OrderTop β]

instance : OrderTop (TopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top := fun _ => @le_top (α → β) _ _ _

@[simp]
theorem coe_top : ⇑(⊤ : TopHom α β) = ⊤ :=
  rfl

@[simp]
theorem top_apply (a : α) : (⊤ : TopHom α β) a = ⊤ :=
  rfl

end OrderTop

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] (f g : TopHom α β)

instance : Min (TopHom α β) :=
  ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

instance : PartialOrder (TopHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

instance : SemilatticeInf (TopHom α β) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[simp]
theorem coe_inf : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderTop β] (f g : TopHom α β)

instance : Max (TopHom α β) :=
  ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

instance : SemilatticeSup (TopHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[simp]
theorem coe_sup : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderTop β] : Lattice (TopHom α β) where

instance [DistribLattice β] [OrderTop β] : DistribLattice (TopHom α β) :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end TopHom

/-! ### Bot homomorphisms -/


namespace BotHom

variable [Bot α]

section Bot

variable [Bot β] [Bot γ] [Bot δ]

instance : FunLike (BotHom α β) α β where
  coe := BotHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : BotHomClass (BotHom α β) α β where
  map_bot := BotHom.map_bot'

-- this must come after the coe_to_fun definition
initialize_simps_projections BotHom (toFun → apply)

@[ext]
theorem ext {f g : BotHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : BotHom α β) (f' : α → β) (h : f' = f) :
    BotHom α β where
  toFun := f'
  map_bot' := h.symm ▸ f.map_bot'

@[simp]
theorem coe_copy (f : BotHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : BotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

instance : Inhabited (BotHom α β) :=
  ⟨⟨fun _ => ⊥, rfl⟩⟩

variable (α)

/-- `id` as a `BotHom`. -/
protected def id : BotHom α α :=
  ⟨id, rfl⟩

@[simp, norm_cast]
theorem coe_id : ⇑(BotHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BotHom.id α a = a :=
  rfl

/-- Composition of `BotHom`s as a `BotHom`. -/
def comp (f : BotHom β γ) (g : BotHom α β) :
    BotHom α γ where
  toFun := f ∘ g
  map_bot' := by rw [comp_apply, map_bot, map_bot]

@[simp]
theorem coe_comp (f : BotHom β γ) (g : BotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BotHom β γ) (g : BotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : BotHom γ δ) (g : BotHom β γ) (h : BotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BotHom α β) : f.comp (BotHom.id α) = f :=
  BotHom.ext fun _ => rfl

@[simp]
theorem id_comp (f : BotHom α β) : (BotHom.id β).comp f = f :=
  BotHom.ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : BotHom β γ} {f : BotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BotHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]
theorem cancel_left {g : BotHom β γ} {f₁ f₂ : BotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => BotHom.ext fun a => hg <| by rw [← BotHom.comp_apply, h, BotHom.comp_apply],
    congr_arg _⟩

end Bot

instance instLE [LE β] [Bot β] : LE (BotHom α β) where
  le f g := (f : α → β) ≤ g

instance [Preorder β] [Bot β] : Preorder (BotHom α β) :=
  Preorder.lift (DFunLike.coe : BotHom α β → α → β)

instance [PartialOrder β] [Bot β] : PartialOrder (BotHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

section OrderBot

variable [LE β] [OrderBot β]

instance : OrderBot (BotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le := fun _ => @bot_le (α → β) _ _ _

@[simp]
theorem coe_bot : ⇑(⊥ : BotHom α β) = ⊥ :=
  rfl

@[simp]
theorem bot_apply (a : α) : (⊥ : BotHom α β) a = ⊥ :=
  rfl

end OrderBot

section SemilatticeInf

variable [SemilatticeInf β] [OrderBot β] (f g : BotHom α β)

instance : Min (BotHom α β) :=
  ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_bot, map_bot, inf_bot_eq]⟩⟩

instance : PartialOrder (BotHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

instance : SemilatticeInf (BotHom α β) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[simp]
theorem coe_inf : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] (f g : BotHom α β)

instance : Max (BotHom α β) :=
  ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_bot, map_bot, sup_bot_eq]⟩⟩

instance : SemilatticeSup (BotHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[simp]
theorem coe_sup : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderBot β] : Lattice (BotHom α β) where

instance [DistribLattice β] [OrderBot β] : DistribLattice (BotHom α β) :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end BotHom

/-! ### Bounded order homomorphisms -/

-- TODO: remove this configuration and use the default configuration.
initialize_simps_projections BoundedOrderHom (+toOrderHom, -toFun)

namespace BoundedOrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedOrderHom` as a `TopHom`. -/
def toTopHom (f : BoundedOrderHom α β) : TopHom α β :=
  { f with }

/-- Reinterpret a `BoundedOrderHom` as a `BotHom`. -/
def toBotHom (f : BoundedOrderHom α β) : BotHom α β :=
  { f with }

instance : FunLike (BoundedOrderHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance : BoundedOrderHomClass (BoundedOrderHom α β) α β where
  map_rel f := @(f.monotone')
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]
theorem ext {f g : BoundedOrderHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BoundedOrderHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : BoundedOrderHom α β :=
  { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

@[simp]
theorem coe_copy (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `BoundedOrderHom`. -/
protected def id : BoundedOrderHom α α :=
  { OrderHom.id, TopHom.id α, BotHom.id α with }

instance : Inhabited (BoundedOrderHom α α) :=
  ⟨BoundedOrderHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(BoundedOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedOrderHom.id α a = a :=
  rfl

/-- Composition of `BoundedOrderHom`s as a `BoundedOrderHom`. -/
def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
  { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]
theorem coe_comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem coe_comp_orderHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : OrderHom α γ) = (f : OrderHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_topHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : TopHom α γ) = (f : TopHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_botHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : BotHom α γ) = (f : BotHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : BoundedOrderHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BoundedOrderHom α β) : f.comp (BoundedOrderHom.id α) = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
theorem id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedOrderHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
   congr_arg (fun g => comp g f)⟩

@[simp]
theorem cancel_left {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    BoundedOrderHom.ext fun a =>
      hg <| by rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

end BoundedOrderHom

/-! ### Dual homs -/


namespace TopHom

variable [LE α] [OrderTop α] [LE β] [OrderTop β] [LE γ] [OrderTop γ]

/-- Reinterpret a top homomorphism as a bot homomorphism between the dual lattices. -/
@[simps]
protected def dual :
    TopHom α β ≃ BotHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_top'⟩
  invFun f := ⟨f, f.map_bot'⟩

@[simp]
theorem dual_id : TopHom.dual (TopHom.id α) = BotHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : TopHom β γ) (f : TopHom α β) :
    TopHom.dual (g.comp f) = g.dual.comp (TopHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : TopHom.dual.symm (BotHom.id _) = TopHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BotHom βᵒᵈ γᵒᵈ) (f : BotHom αᵒᵈ βᵒᵈ) :
    TopHom.dual.symm (g.comp f) = (TopHom.dual.symm g).comp (TopHom.dual.symm f) :=
  rfl

end TopHom

namespace BotHom

variable [LE α] [OrderBot α] [LE β] [OrderBot β] [LE γ] [OrderBot γ]

/-- Reinterpret a bot homomorphism as a top homomorphism between the dual lattices. -/
@[simps]
protected def dual :
    BotHom α β ≃ TopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_bot'⟩
  invFun f := ⟨f, f.map_top'⟩

@[simp]
theorem dual_id : BotHom.dual (BotHom.id α) = TopHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BotHom β γ) (f : BotHom α β) :
    BotHom.dual (g.comp f) = g.dual.comp (BotHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : BotHom.dual.symm (TopHom.id _) = BotHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : TopHom βᵒᵈ γᵒᵈ) (f : TopHom αᵒᵈ βᵒᵈ) :
    BotHom.dual.symm (g.comp f) = (BotHom.dual.symm g).comp (BotHom.dual.symm f) :=
  rfl

end BotHom

namespace BoundedOrderHom

variable [Preorder α] [BoundedOrder α] [Preorder β] [BoundedOrder β] [Preorder γ] [BoundedOrder γ]

/-- Reinterpret a bounded order homomorphism as a bounded order homomorphism between the dual
orders. -/
@[simps]
protected def dual :
    BoundedOrderHom α β ≃
      BoundedOrderHom αᵒᵈ
        βᵒᵈ where
  toFun f := ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩

@[simp]
theorem dual_id : (BoundedOrderHom.id α).dual = BoundedOrderHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedOrderHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ) :
    BoundedOrderHom.dual.symm (g.comp f) =
      (BoundedOrderHom.dual.symm g).comp (BoundedOrderHom.dual.symm f) :=
  rfl

end BoundedOrderHom
