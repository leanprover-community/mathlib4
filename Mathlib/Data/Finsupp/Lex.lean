/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/


variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

/-- `Finsupp.Lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `Lex (α →₀ N)` has an order given by `Finsupp.Lex (· < ·) (· < ·)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r s x y

theorem _root_.Pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r s a b = Finsupp.Lex r s a b :=
  rfl

theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  .rfl

theorem lex_eq_invImage_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
    Finsupp.Lex r s = InvImage (DFinsupp.Lex r fun _ ↦ s) toDFinsupp :=
  rfl

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

instance [LT α] [LT N] : LT (Colex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· > ·) (· < ·) (ofColex f) (ofColex g)⟩

theorem lex_lt_iff [LT α] [LT N] {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i :=
  .rfl

theorem colex_lt_iff [LT α] [LT N] {a b : Colex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, i < j → a j = b j) ∧ a i < b i :=
  .rfl

theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)

theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (· < ·) x y :=
  DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)

theorem lex_iff_of_unique [Unique α] [LT N] {r} [IsIrrefl α r] {x y : α →₀ N} :
    Finsupp.Lex r (· < ·) x y ↔ x default < y default :=
  Pi.lex_iff_of_unique

theorem lex_lt_iff_of_unique [Unique α] [LT N] [Preorder α] {x y : Lex (α →₀ N)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

variable [LinearOrder α]

instance Lex.isStrictOrder [PartialOrder N] :
    IsStrictOrder (Lex (α →₀ N)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (α → N)) _
  trans _ _ _ := lt_trans (α := Lex (α → N))

/-- The partial order on `Finsupp`s obtained by the lexicographic ordering.
See `Finsupp.Lex.linearOrder` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α →₀ N) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

/-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le := (· ≤ ·)
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective

theorem lex_le_iff_of_unique [Unique α] [PartialOrder N] {x y : Lex (α →₀ N)} :
    x ≤ y ↔ x default ≤ y default := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lex_lt_iff_of_unique, ← ofLex.apply_eq_iff_eq,
    DFunLike.ext_iff, Unique.forall_iff]

theorem Lex.single_strictAnti : StrictAnti fun (a : α) ↦ toLex (single a 1) := by
  intro a b h
  simp only [LT.lt, Finsupp.lex_def]
  simp only [ofLex_toLex, Nat.lt_eq]
  use a
  constructor
  · intro d hd
    simp only [Finsupp.single_eq_of_ne hd.ne, Finsupp.single_eq_of_ne (hd.trans h).ne]
  · simp [h.ne']

theorem Lex.single_lt_iff {a b : α} : toLex (single b 1) < toLex (single a 1) ↔ a < b :=
  Lex.single_strictAnti.lt_iff_gt

theorem Lex.single_le_iff {a b : α} : toLex (single b 1) ≤ toLex (single a 1) ↔ a ≤ b :=
  Lex.single_strictAnti.le_iff_ge

theorem Lex.single_antitone : Antitone fun (a : α) ↦ toLex (single a 1) :=
  Lex.single_strictAnti.antitone

variable [PartialOrder N]

theorem toLex_monotone : Monotone (@toLex (α →₀ N)) :=
  fun a b h ↦ DFinsupp.toLex_monotone (id h : ∀ i, (toDFinsupp a) i ≤ (toDFinsupp b) i)

@[deprecated lex_lt_iff (since := "2025-10-12")]
theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b :=
  fun h1 h2 ↦ ⟨i, h1, h2⟩

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`.  This is actually necessary: addition on `Lex (α →₀ N)` may fail to
be monotone, when it is "just" monotone on `N`.

See `Counterexamples/ZeroDivisorsInAddMonoidAlgebras.lean` for a counterexample. -/


section Left

variable [AddLeftStrictMono N]

instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (α →₀ N)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), add_lt_add_left ha _⟩⟩

instance Lex.addLeftMono : AddLeftMono (Lex (α →₀ N)) :=
  addLeftMono_of_addLeftStrictMono _

end Left

section Right

variable [AddRightStrictMono N]

instance Lex.addRightStrictMono : AddRightStrictMono (Lex (α →₀ N)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦
    ⟨a, fun j ja ↦ congr_arg (· + f j) (lta j ja), add_lt_add_right ha _⟩⟩

instance Lex.addRightMono : AddRightMono (Lex (α →₀ N)) :=
  addRightMono_of_addRightStrictMono _

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder α]

instance Lex.orderBot [AddCommMonoid N] [PartialOrder N] [CanonicallyOrderedAdd N] :
    OrderBot (Lex (α →₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le

instance Lex.isOrderedCancelAddMonoid
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (α → N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α → N))

end OrderedAddMonoid

end Finsupp
