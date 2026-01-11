/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Order.Basic

/-!
# Type synonyms

This file provides three type synonyms for order theory:

* `OrderDual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: Type synonym of `α` to equip it with its colexicographic order. The precise meaning
  depends on the type we take the colex of. Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:

* `OrderDual`: `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.
* `Colex`: `toColex : α → Colex α` and `ofColex : Colex α → α`.

## See also

This file is similar to `Algebra.Group.TypeTags`.
-/

@[expose] public section


variable {α : Type*}

/-! ### Order dual -/


namespace OrderDual

instance [h : Nontrivial α] : Nontrivial αᵒᵈ := h
instance [h : Unique α] : Unique αᵒᵈ := h

/-- `toDual` is the identity function to the `OrderDual` of a linear order. -/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _

/-- `ofDual` is the identity function from the `OrderDual` of a linear order. -/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _

@[simp] theorem toDual_symm_eq : (@toDual α).symm = ofDual := rfl
@[simp] theorem ofDual_symm_eq : (@ofDual α).symm = toDual := rfl
@[simp] theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a := rfl
@[simp] theorem ofDual_toDual (a : α) : ofDual (toDual a) = a := rfl

@[simp] theorem toDual_trans_ofDual : (toDual (α := α)).trans ofDual = Equiv.refl _ := rfl
@[simp] theorem ofDual_trans_toDual : (ofDual (α := α)).trans toDual = Equiv.refl _ := rfl
@[simp] theorem toDual_comp_ofDual : (toDual (α := α)) ∘ ofDual = id := rfl
@[simp] theorem ofDual_comp_toDual : (ofDual (α := α)) ∘ toDual = id := rfl

theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b := by simp
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b := by simp

@[ext] lemma ext {a b : αᵒᵈ} (h : ofDual a = ofDual b) : a = b := h

@[to_dual self, simp]
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a := .rfl

@[to_dual self, simp]
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a := .rfl

@[to_dual toDual_le]
theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a := .rfl

@[to_dual toDual_lt]
theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a := .rfl

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
protected def rec {motive : αᵒᵈ → Sort*} (toDual : ∀ a : α, motive (toDual a)) :
    ∀ a : αᵒᵈ, motive a := toDual

@[simp] protected theorem «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) := .rfl
@[simp] protected theorem «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) := .rfl

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

end OrderDual

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
