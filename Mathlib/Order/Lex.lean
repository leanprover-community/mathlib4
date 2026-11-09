/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Lexicographic and colexicographic order

This file provides two one-field structures for order theory:

* `Lex α`: One-field structure around `α` to equip it with its lexicographic order.
  The precise meaning depends on the type we take the lex of.
  Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: One-field structure around `α` to equip it with its colexicographic order.
  The precise meaning depends on the type we take the colex of.
  Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## See also

This file is similar to `Mathlib.Algebra.Group.TypeTags.Basic`.
-/

@[expose] public section

assert_not_exists OrderDual

variable {α : Type*}

/-! ### Lexicographic order -/

/-- A one-field structure equipping a type with its lexicographic order. -/
@[ext]
structure Lex (α : Type*) where
  /-- `toLex` is the identity function to the `Lex` of a type. -/
  toLex ::
  /-- `ofLex` is the identity function from the `Lex` of a type. -/
  ofLex : α
deriving Nonempty, Inhabited, DecidableEq

/-- The natural equivalence between `Lex α` and `α`. -/
@[simps]
def ofLexEquiv : Lex α ≃ α where
  toFun := Lex.ofLex
  invFun := Lex.toLex

@[simp] theorem toLex_ofLex (a : Lex α) : .toLex a.ofLex = a := rfl
@[simp] theorem ofLex_toLex (a : α) : (Lex.toLex a).ofLex = a := rfl

theorem toLex_inj {a b : α} : Lex.toLex a = Lex.toLex b ↔ a = b := by simp
theorem ofLex_inj {a b : Lex α} : a.ofLex = b.ofLex ↔ a = b := Lex.ext_iff.symm

lemma toLex_bijective : Lex.toLex (α := α).Bijective := ofLexEquiv.symm.bijective
lemma ofLex_bijective : Lex.ofLex (α := α).Bijective := ofLexEquiv.bijective
lemma toLex_injective : Lex.toLex (α := α).Injective := ofLexEquiv.symm.injective
lemma ofLex_injective : Lex.ofLex (α := α).Injective := ofLexEquiv.injective
lemma toLex_surjective : Lex.toLex (α := α).Surjective := ofLexEquiv.symm.surjective
lemma ofLex_surjective : Lex.ofLex (α := α).Surjective := ofLexEquiv.surjective

instance (α : Type*) [BEq α] : BEq (Lex α) where
  beq a b := a.ofLex == b.ofLex

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Lex α) where
  rfl {a} := by
    change (a.ofLex == a.ofLex) = _
    simp
  eq_of_beq {a b} e := by
    change (a.ofLex == b.ofLex) at e
    simpa [ofLex_inj] using e

instance (α : Type*) [Nontrivial α] : Nontrivial (Lex α) := ofLex_surjective.nontrivial
instance (α : Type*) [Unique α] : Unique (Lex α) := ofLex_injective.unique

instance {α β} [H : CoeFun α fun _ ↦ β] : CoeFun (Lex α) fun _ ↦ β where
  coe f := H.coe (Lex.ofLex f)

@[simp] lemma Lex.forall {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) :=
  toLex_surjective.forall
@[simp] lemma Lex.exists {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) :=
  toLex_surjective.exists

/-! ### Colexicographic order -/

/-- A one-field structure equipping a type with its colexicographic order. -/
@[ext]
structure Colex (α : Type*) where
  /-- `toColex` is the identity function to the `Colex` of a type. -/
  toColex ::
  /-- `ofColex` is the identity function from the `Colex` of a type. -/
  ofColex : α
deriving Nonempty, Inhabited, DecidableEq

/-- The natural equivalence between `Colex α` and `α`. -/
@[simps]
def ofColexEquiv : Colex α ≃ α where
  toFun := Colex.ofColex
  invFun := Colex.toColex

@[simp] theorem toColex_ofColex (a : Colex α) : .toColex a.ofColex = a := rfl
@[simp] theorem ofColex_toColex (a : α) : (Colex.toColex a).ofColex = a := rfl

theorem toColex_inj {a b : α} : Colex.toColex a = Colex.toColex b ↔ a = b := by simp
theorem ofColex_inj {a b : Colex α} : a.ofColex = b.ofColex ↔ a = b := Colex.ext_iff.symm

lemma toColex_bijective : Colex.toColex (α := α).Bijective := ofColexEquiv.symm.bijective
lemma ofColex_bijective : Colex.ofColex (α := α).Bijective := ofColexEquiv.bijective
lemma toColex_injective : Colex.toColex (α := α).Injective := ofColexEquiv.symm.injective
lemma ofColex_injective : Colex.ofColex (α := α).Injective := ofColexEquiv.injective
lemma toColex_surjective : Colex.toColex (α := α).Surjective := ofColexEquiv.symm.surjective
lemma ofColex_surjective : Colex.ofColex (α := α).Surjective := ofColexEquiv.surjective

instance (α : Type*) [BEq α] : BEq (Colex α) where
  beq a b := a.ofColex == b.ofColex

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Colex α) where
  rfl {a} := by
    change (a.ofColex == a.ofColex) = _
    simp
  eq_of_beq {a b} e := by
    change (a.ofColex == b.ofColex) at e
    simpa [ofColex_inj] using e

instance (α : Type*) [Nontrivial α] : Nontrivial (Colex α) := ofColex_surjective.nontrivial
instance (α : Type*) [Unique α] : Unique (Colex α) := ofColex_injective.unique

instance {α β} [H : CoeFun α fun _ ↦ β] : CoeFun (Colex α) fun _ ↦ β where
  coe f := H.coe (Colex.ofColex f)

@[simp] lemma Colex.forall {p : Colex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toColex a) :=
  toColex_surjective.forall
@[simp] lemma Colex.exists {p : Colex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toColex a) :=
  toColex_surjective.exists

@[deprecated "type changed" (since := "2026-11-08")] alias toLex_symm_eq := ofLex_toLex
@[deprecated (since := "2026-11-08")] alias ofLex_symm_eq := toLex_ofLex
@[deprecated (since := "2026-11-08")] alias toColex_symm_eq := ofColex_toColex
@[deprecated (since := "2026-11-08")] alias ofColex_symm_eq := toColex_ofColex
