/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.RelIso.Basic
import Mathlib.Logic.Embedding.Set
import Mathlib.Logic.Equiv.Set

/-!
# Interactions between relation homomorphisms and sets

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/


open Function

universe u v w

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

namespace RelHomClass

variable {F : Type*}

theorem map_inf [SemilatticeInf α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· < ·) (· < ·)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun _ _ => map_rel a).map_inf m n

theorem map_sup [SemilatticeSup α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· > ·) (· > ·)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _

end RelHomClass

namespace RelIso

@[simp]
theorem range_eq (e : r ≃r s) : Set.range e = Set.univ :=
  e.surjective.range_eq

end RelIso

/-- `Subrel r p` is the inherited relation on a subset. -/
def Subrel (r : α → α → Prop) (p : Set α) : p → p → Prop :=
  (Subtype.val : p → α) ⁻¹'o r

@[simp]
theorem subrel_val (r : α → α → Prop) (p : Set α) {a b} : Subrel r p a b ↔ r a.1 b.1 :=
  Iff.rfl

namespace Subrel

/-- The relation embedding from the inherited relation on a subset. -/
protected def relEmbedding (r : α → α → Prop) (p : Set α) : Subrel r p ↪r r :=
  ⟨Embedding.subtype _, Iff.rfl⟩

@[simp]
theorem relEmbedding_apply (r : α → α → Prop) (p a) : Subrel.relEmbedding r p a = a.1 :=
  rfl

/-- A set inclusion as a relation embedding. -/
protected def inclusionEmbedding (r : α → α → Prop) {p q : Set α} (h : p ⊆ q) :
    Subrel r p ↪r Subrel r q where
  toFun := Set.inclusion h
  inj' _ _ h := (Set.inclusion_inj _).mp h
  map_rel_iff' := Iff.rfl

@[simp]
theorem coe_inclusionEmbedding (r : α → α → Prop) {p q : Set α} (h : p ⊆ q) :
    (Subrel.inclusionEmbedding r h : p → q) = Set.inclusion h :=
  rfl

instance (r : α → α → Prop) [IsWellOrder α r] (p : Set α) : IsWellOrder p (Subrel r p) :=
  RelEmbedding.isWellOrder (Subrel.relEmbedding r p)

-- TODO: this instance is needed as `simp` automatically simplifies `↑{a // p a}` as `{a | p a}`.
--
-- Should `Subrel` be redefined in terms of `p : α → Prop` instead of `p : Set α` to avoid
-- this issue?
instance (r : α → α → Prop) (p : α → Prop) [IsWellOrder α r] :
    IsWellOrder {a // p a} (Subrel r {a | p a}) :=
  instIsWellOrderElem _ _

instance (r : α → α → Prop) [IsRefl α r] (p : Set α) : IsRefl p (Subrel r p) :=
  ⟨fun x => @IsRefl.refl α r _ x⟩

instance (r : α → α → Prop) [IsSymm α r] (p : Set α) : IsSymm p (Subrel r p) :=
  ⟨fun x y => @IsSymm.symm α r _ x y⟩

instance (r : α → α → Prop) [IsAsymm α r] (p : Set α) : IsAsymm p (Subrel r p) :=
  ⟨fun x y => @IsAsymm.asymm α r _ x y⟩

instance (r : α → α → Prop) [IsTrans α r] (p : Set α) : IsTrans p (Subrel r p) :=
  ⟨fun x y z => @IsTrans.trans α r _ x y z⟩

instance (r : α → α → Prop) [IsIrrefl α r] (p : Set α) : IsIrrefl p (Subrel r p) :=
  ⟨fun x => @IsIrrefl.irrefl α r _ x⟩

end Subrel

/-- Restrict the codomain of a relation embedding. -/
def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r Subrel s p :=
  ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩

@[simp]
theorem RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) :
    RelEmbedding.codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

section image

theorem RelIso.image_eq_preimage_symm (e : r ≃r s) (t : Set α) : e '' t = e.symm ⁻¹' t :=
  e.toEquiv.image_eq_preimage t

theorem RelIso.preimage_eq_image_symm (e : r ≃r s) (t : Set β) : e ⁻¹' t = e.symm '' t := by
  rw [e.symm.image_eq_preimage_symm]; rfl

end image

theorem Acc.of_subrel {r : α → α → Prop} [IsTrans α r] {b : α} (a : { a // r a b })
    (h : Acc (Subrel r { a | r a b }) a) : Acc r a.1 :=
  h.recOn fun a _ IH ↦ ⟨_, fun _ hb ↦ IH ⟨_, _root_.trans hb a.2⟩ hb⟩

/-- A relation `r` is well-founded iff every downward-interval `{ a | r a b }` of it is
well-founded. -/
theorem wellFounded_iff_wellFounded_subrel {r : α → α → Prop} [IsTrans α r] :
    WellFounded r ↔ ∀ b, WellFounded (Subrel r { a | r a b }) where
  mp h _ := InvImage.wf Subtype.val h
  mpr h := ⟨fun a ↦ ⟨_, fun b hr ↦ ((h a).apply _).of_subrel ⟨b, hr⟩⟩⟩
