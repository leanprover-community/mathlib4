/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.WithBot

/-!
# Adjoining `⊤` and `⊥` to order maps and lattice homomorphisms

This file defines ways to adjoin `⊤` or `⊥` or both to order maps (homomorphisms, embeddings and
isomorphisms) and lattice homomorphisms, and properties about the results.

Some definitions cause a possibly unbounded lattice homomorphism to become bounded,
so they change the type of the homomorphism.
-/

@[expose] public section


variable {α β γ : Type*}

namespace WithTop

open OrderDual

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual.
This is the order iso form of `WithTop.ofDual`, as proven by `coe_toDualBotEquiv`. -/
@[to_dual
/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual.
This is the order iso form of `WithBot.ofDual`, as proven by `coe_toDualTopEquiv`. -/]
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _

@[to_dual (attr := simp)]
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl

@[to_dual (attr := simp)]
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl

@[to_dual]
theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl

@[deprecated (since := "2026-03-27")]
alias _root_.WithBot.coe_toDualTopEquiv_eq := WithBot.coe_toDualTopEquiv

/-- Embedding into `WithTop α`. -/
@[to_dual (attr := simps) /-- Embedding into `WithBot α`. -/]
def _root_.Function.Embedding.coeWithTop : α ↪ WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective

/-- The coercion `α → WithTop α` bundled as monotone map. -/
@[to_dual (attr := simps -fullyApplied)
/-- The coercion `α → WithBot α` bundled as monotone map. -/]
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

/-- Any `OrderTop` is equivalent to `WithTop` of the subtype excluding `⊤`.

See also `Equiv.optionSubtypeNe`. -/
@[to_dual
/-- Any `OrderBot` is equivalent to `WithBot` of the subtype excluding `⊥`.

See also `Equiv.optionSubtypeNe`. -/]
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

@[to_dual (attr := simp)]
theorem subtypeOrderIso_apply_coe [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    (a : {a : α // a ≠ ⊤}) :
  subtypeOrderIso (a : WithTop {a : α // a ≠ ⊤}) = a := rfl

@[to_dual]
theorem subtypeOrderIso_symm_apply [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    {a : α} (h : a ≠ ⊤) :
    subtypeOrderIso.symm a = (⟨a, h⟩ : {a : α // a ≠ ⊤}) := by
  rw [OrderIso.symm_apply_eq]
  rfl

end WithTop

namespace OrderHom

variable [Preorder α] [Preorder β]

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithBot α →o WithBot β`. -/
@[to_dual (attr := simps -fullyApplied)
/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithTop α →o WithTop β`. -/]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩

end OrderHom

namespace OrderEmbedding

variable [Preorder α] [Preorder β]

/-- A version of `WithBot.map` for order embeddings. -/
@[to_dual (attr := simps -fullyApplied) /-- A version of `WithTop.map` for order embeddings. -/]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β where
  toFun := WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff

end OrderEmbedding

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `Equiv.optionCongr` for `WithTop`. -/
@[to_dual (attr := simps -fullyApplied) /-- A version of `Equiv.optionCongr` for `WithBot`. -/]
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

@[to_dual existing, simp]
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[to_dual existing, simp]
theorem withBotCongr_symm (e : α ≃o β) : e.symm.withBotCongr = e.withBotCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[to_dual existing, simp]
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.withBotCongr_trans e₂.toEquiv

end OrderIso

namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[to_dual (attr := simp)]
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := WithBot.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[to_dual (attr := simp)]
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective WithBot.map_id

@[to_dual (attr := simp)]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| WithBot.map_comp_map _ _

/-- Adjoins a `⊤` to the domain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain of an `InfHom`. -/]
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

/-- Adjoins a `⊥` to the domain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊤` to the domain of an `InfHom`. -/]
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

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Adjoins a `⊤` to the domain and codomain of a `LatticeHom`. -/
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual existing]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

@[to_dual (attr := simp)]
lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[to_dual (attr := simp)]
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual /-- Adjoins a `⊥` and `⊤` to the domain and codomain of a `LatticeHom`. -/]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
lemma coe_withTopWithBot (f : LatticeHom α β) :
    ⇑f.withTopWithBot = WithTop.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  DFunLike.coe_injective <| by simp [WithTop.map_id, WithBot.map_id]

@[to_dual (attr := simp)]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

/-- Adjoins a `⊤` to the domain of a `LatticeHom`. -/
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }

/-- Adjoins a `⊥` to the domain of a `LatticeHom`. -/
@[to_dual existing (attr := simps!)]
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }

/-- Adjoins a `⊤` and `⊥` to the domain of a `LatticeHom`. -/
@[to_dual (attr := simps!) /-- Adjoins a `⊥` and `⊤` to the domain of a `LatticeHom`. -/]
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

end LatticeHom
