/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.WithBot

/-!
# Adjoining `⊤` and `⊥` to order maps and lattice homomorphisms

This file defines ways to adjoin `⊤` or `⊥` or both to order maps (homomorphisms, embeddings and
isomorphisms) and lattice homomorphisms, and properties about the results.

Some definitions cause a possibly unbounded lattice homomorphism to become bounded,
so they change the type of the homomorphism.
-/


variable {α β γ : Type*}

namespace WithTop

open OrderDual

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual.
This is the order iso form of `WithTop.ofDual`, as proven by `coe_toDualBotEquiv`. -/
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _

@[simp]
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl

@[simp]
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl

@[simp]
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl

@[simp]
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl

theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl

/-- Embedding into `WithTop α`. -/
@[simps]
def _root_.Function.Embedding.coeWithTop : α ↪ WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective

/-- The coercion `α → WithTop α` bundled as monotone map. -/
@[simps -fullyApplied]
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

/-- Any `OrderTop` is equivalent to `WithTop` of the subtype excluding `⊤`.

See also `Equiv.optionSubtypeNe`. -/
def subtypeOrderIso [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))] :
    WithTop {a : α // a ≠ ⊤} ≃o α where
  toFun a := (a.map (↑)).untopD ⊤
  invFun a := if h : a = ⊤ then ⊤ else .some ⟨a, h⟩
  left_inv
  | .some ⟨a, h⟩ => by simp [h]
  | ⊤ => by simp
  right_inv a := by dsimp only; split_ifs <;> simp [*]
  map_rel_iff' {a b} := match a, b with
  | .some a, .some b => by simp
  | ⊤, .some ⟨b, h⟩ => by simp [h]
  | a, ⊤ => by simp

@[simp]
theorem subtypeOrderIso_apply_coe [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    (a : {a : α // a ≠ ⊤}) :
  subtypeOrderIso (a : WithTop {a : α // a ≠ ⊤}) = a := rfl

theorem subtypeOrderIso_symm_apply [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    {a : α} (h : a ≠ ⊤) :
    (subtypeOrderIso).symm a = (⟨a, h⟩ : {a : α // a ≠ ⊤}) := by
  rw [OrderIso.symm_apply_eq]
  rfl

end WithTop

namespace WithBot

open OrderDual

/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual.
This is the order iso form of `WithBot.ofDual`, as proven by `coe_toDualTopEquiv`. -/
protected def toDualTopEquiv [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _

@[simp]
theorem toDualTopEquiv_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv ↑(toDual a) = toDual (a : WithTop α) :=
  rfl

@[simp]
theorem toDualTopEquiv_symm_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv.symm (toDual (a : WithTop α)) = ↑(toDual a) :=
  rfl

@[simp]
theorem toDualTopEquiv_bot [LE α] : WithBot.toDualTopEquiv (⊥ : WithBot αᵒᵈ) = ⊥ :=
  rfl

@[simp]
theorem toDualTopEquiv_symm_bot [LE α] : WithBot.toDualTopEquiv.symm (⊥ : (WithTop α)ᵒᵈ) = ⊥ :=
  rfl

theorem coe_toDualTopEquiv_eq [LE α] :
    (WithBot.toDualTopEquiv : WithBot αᵒᵈ → (WithTop α)ᵒᵈ) = toDual ∘ WithBot.ofDual :=
  funext fun _ => rfl

/-- Embedding into `WithBot α`. -/
@[simps]
def _root_.Function.Embedding.coeWithBot : α ↪ WithBot α where
  toFun := (↑)
  inj' := WithBot.coe_injective

/-- The coercion `α → WithBot α` bundled as monotone map. -/
@[simps -fullyApplied]
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithBot α where
  toFun := (↑)
  inj' := WithBot.coe_injective
  map_rel_iff' := WithBot.coe_le_coe

/-- Any `OrderBot` is equivalent to `WithBot` of the subtype excluding `⊥`.

See also `Equiv.optionSubtypeNe`. -/
def subtypeOrderIso [PartialOrder α] [OrderBot α] [DecidablePred (· = (⊥ : α))] :
    WithBot {a : α // a ≠ ⊥} ≃o α := (WithTop.subtypeOrderIso (α := αᵒᵈ)).dual

@[simp]
theorem subtypeOrderIso_apply_coe [PartialOrder α] [OrderBot α] [DecidablePred (· = (⊥ : α))]
    (a : {a : α // a ≠ ⊥}) :
  subtypeOrderIso (a : WithTop {a : α // a ≠ ⊥}) = a := rfl

theorem subtypeOrderIso_symm_apply [PartialOrder α] [OrderBot α] [DecidablePred (· = (⊥ : α))]
    {a : α} (h : a ≠ ⊥) :
    (subtypeOrderIso).symm a = (⟨a, h⟩ : {a : α // a ≠ ⊥}) := by
  rw [OrderIso.symm_apply_eq]
  rfl

end WithBot

namespace OrderHom

variable [Preorder α] [Preorder β]

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithBot α →o WithBot β`. -/
@[simps -fullyApplied]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithTop α →o WithTop β`. -/
@[simps -fullyApplied]
protected def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.withTop_map⟩

end OrderHom

namespace OrderEmbedding

variable [Preorder α] [Preorder β]

/-- A version of `WithBot.map` for order embeddings. -/
@[simps -fullyApplied]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β where
  toFun := WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff

/-- A version of `WithTop.map` for order embeddings. -/
@[simps -fullyApplied]
protected def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.withBotMap.dual with toFun := WithTop.map f }

@[deprecated (since := "2025-08-21")] protected alias withBotCoe := WithBot.coeOrderHom
@[deprecated (since := "2025-08-21")] alias withBotCoe_apply := WithBot.coeOrderHom_apply
@[deprecated (since := "2025-08-21")] protected alias withTopCoe := WithTop.coeOrderHom
@[deprecated (since := "2025-08-21")] alias withTopCoe_apply := WithTop.coeOrderHom_apply

end OrderEmbedding

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `Equiv.optionCongr` for `WithTop`. -/
@[simps -fullyApplied]
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β where
  toFun := WithTop.map e
  __ := e.toOrderEmbedding.withTopMap
  __ := e.toEquiv.withTopCongr

@[simp]
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withTopCongr_refl

@[simp]
theorem withTopCongr_symm (e : α ≃o β) : e.symm.withTopCongr = e.withTopCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withTopCongr_symm

@[simp]
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withTopCongr = e₁.withTopCongr.trans e₂.withTopCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.withTopCongr_trans e₂.toEquiv

/-- A version of `Equiv.optionCongr` for `WithBot`. -/
@[simps -fullyApplied]
def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β where
  toFun := WithBot.map e
  __ := e.toOrderEmbedding.withBotMap
  __ := e.toEquiv.withBotCongr

@[simp]
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[simp]
theorem withBotCongr_symm (e : α ≃o β) : e.symm.withBotCongr = e.withBotCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[simp]
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.withBotCongr_trans e₂.toEquiv

end OrderIso

namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[simp]
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective WithTop.map_id

@[simp]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := WithBot.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[simp]
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective WithBot.map_id

@[simp]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| WithBot.map_comp_map _ _

/-- Adjoins a `⊤` to the codomain of a `SupHom`. -/
@[simps]
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

/-- Adjoins a `⊥` to the domain of a `SupHom`. -/
@[simps]
def withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_sup_eq _).symm
    | ⊥, (b : α) => (bot_sup_eq _).symm
    | (a : α), ⊥ => (sup_bot_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl

end SupHom

namespace InfHom

variable [SemilatticeInf α] [SemilatticeInf β] [SemilatticeInf γ]

/-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withTop (f : InfHom α β) : InfTopHom (WithTop α) (WithTop β) where
  toFun := WithTop.map f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
  map_top' := rfl

@[simp]
theorem withTop_id : (InfHom.id α).withTop = InfTopHom.id _ := DFunLike.coe_injective WithTop.map_id

@[simp]
theorem withTop_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withBot (f : InfHom α β) : InfHom (WithBot α) (WithBot β) where
  toFun := WithBot.map f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)

@[simp]
theorem withBot_id : (InfHom.id α).withBot = InfHom.id _ := DFunLike.coe_injective WithBot.map_id

@[simp]
theorem withBot_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| WithBot.map_comp_map _ _

/-- Adjoins a `⊤` to the codomain of an `InfHom`. -/
@[simps]
def withTop' [OrderTop β] (f : InfHom α β) : InfTopHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => (top_inf_eq _).symm
    | ⊤, (b : α) => (top_inf_eq _).symm
    | (a : α), ⊤ => (inf_top_eq _).symm
    | (a : α), (b : α) => f.map_inf' _ _
  map_top' := rfl

/-- Adjoins a `⊥` to the codomain of an `InfHom`. -/
@[simps]
def withBot' [OrderBot β] (f : InfHom α β) : InfHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_inf_eq _).symm
    | ⊥, (b : α) => (bot_inf_eq _).symm
    | (a : α), ⊥ => (inf_bot_eq _).symm
    | (a : α), (b : α) => f.map_inf' _ _

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Adjoins a `⊤` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[simp]
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withBot (f : LatticeHom α β) : ⇑f.withBot = Option.map f := rfl

lemma withBot_apply (f : LatticeHom α β) (a : WithBot α) : f.withBot a = a.map f := rfl

@[simp]
theorem withBot_id : (LatticeHom.id α).withBot = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTopWithBot (f : LatticeHom α β) : ⇑f.withTopWithBot = Option.map (Option.map f) := rfl

lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (Option.map f) := rfl

@[simp]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  DFunLike.coe_injective <| by
    refine (congr_arg Option.map ?_).trans Option.map_id
    rw [withBot_id]
    rfl

@[simp]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

/-- Adjoins a `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }

/-- Adjoins a `⊤` and `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

end LatticeHom
