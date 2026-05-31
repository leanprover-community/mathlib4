/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Type synonyms

This file provides two type synonyms for order theory:

* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: Type synonym of `α` to equip it with its colexicographic order. The precise meaning
  depends on the type we take the colex of. Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:

* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.
* `Colex`: `toColex : α → Colex α` and `ofColex : Colex α → α`.

## See also

This file is similar to `Mathlib.Algebra.Group.TypeTags.Basic`.
-/

@[expose] public section

assert_not_exists OrderDual

variable {α : Type*}

/-! ### Lexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type*) :=
  α

/-- `toLex` is the identity function to the `Lex` of a type. -/
@[match_pattern]
def toLex : α ≃ Lex α :=
  Equiv.refl _

/-- `ofLex` is the identity function from the `Lex` of a type. -/
@[match_pattern]
def ofLex : Lex α ≃ α :=
  Equiv.refl _

@[simp]
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl

theorem toLex_inj {a b : α} : toLex a = toLex b ↔ a = b := by simp

theorem ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b := by simp

instance (α : Type*) [BEq α] : BEq (Lex α) where
  beq a b := ofLex a == ofLex b

instance (α : Type*) [BEq α] [h : LawfulBEq α] : LawfulBEq (Lex α) := h
instance (α : Type*) [h : DecidableEq α] : DecidableEq (Lex α) := h

instance (α : Type*) [h : Inhabited α] : Inhabited (Lex α) := h
instance (α : Type*) [h : Nonempty α] : Nonempty (Lex α) := h
instance (α : Type*) [h : Nontrivial α] : Nontrivial (Lex α) := h
instance (α : Type*) [h : Unique α] : Unique (Lex α) := h

instance {α γ} [H : CoeFun α γ] : CoeFun (Lex α) γ where
  coe f := H.coe (ofLex f)

/-- A recursor for `Lex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Lex.rec {β : Lex α → Sort*} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)

@[simp] lemma Lex.forall {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) := Iff.rfl
@[simp] lemma Lex.exists {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) := Iff.rfl

/-! ### Colexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
def Colex (α : Type*) :=
  α

/-- `toColex` is the identity function to the `Colex` of a type. -/
@[match_pattern]
def toColex : α ≃ Colex α :=
  Equiv.refl _

/-- `ofColex` is the identity function from the `Colex` of a type. -/
@[match_pattern]
def ofColex : Colex α ≃ α :=
  Equiv.refl _

@[simp]
theorem toColex_symm_eq : (@toColex α).symm = ofColex :=
  rfl

@[simp]
theorem ofColex_symm_eq : (@ofColex α).symm = toColex :=
  rfl

@[simp]
theorem toColex_ofColex (a : Colex α) : toColex (ofColex a) = a :=
  rfl

@[simp]
theorem ofColex_toColex (a : α) : ofColex (toColex a) = a :=
  rfl

theorem toColex_inj {a b : α} : toColex a = toColex b ↔ a = b := by simp

theorem ofColex_inj {a b : Colex α} : ofColex a = ofColex b ↔ a = b := by simp

instance (α : Type*) [BEq α] : BEq (Colex α) where
  beq a b := ofColex a == ofColex b

instance (α : Type*) [BEq α] [h : LawfulBEq α] : LawfulBEq (Colex α) := h
instance (α : Type*) [h : DecidableEq α] : DecidableEq (Colex α) := h

instance (α : Type*) [h : Inhabited α] : Inhabited (Colex α) := h
instance (α : Type*) [h : Nonempty α] : Nonempty (Colex α) := h
instance (α : Type*) [h : Nontrivial α] : Nontrivial (Colex α) := h
instance (α : Type*) [h : Unique α] : Unique (Colex α) := h

instance {α γ} [H : CoeFun α γ] : CoeFun (Colex α) γ where
  coe f := H.coe (ofColex f)

/-- A recursor for `Colex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Colex.rec {β : Colex α → Sort*} (h : ∀ a, β (toColex a)) : ∀ a, β a :=
  fun a => h (ofColex a)

@[simp] lemma Colex.forall {p : Colex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toColex a) := Iff.rfl
@[simp] lemma Colex.exists {p : Colex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toColex a) := Iff.rfl
