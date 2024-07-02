/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Order.Basic

#align_import order.synonym from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Type synonyms

This file provides two type synonyms for order theory:
* `OrderDual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:
* `OrderDual`: `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.

## See also

This file is similar to `Algebra.Group.TypeTags`.
-/


variable {α β γ : Type*}

/-! ### Order dual -/


namespace OrderDual

instance [h : Nontrivial α] : Nontrivial αᵒᵈ :=
  h

/-- `toDual` is the identity function to the `OrderDual` of a linear order.  -/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _
#align order_dual.to_dual OrderDual.toDual

/-- `ofDual` is the identity function from the `OrderDual` of a linear order.  -/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _
#align order_dual.of_dual OrderDual.ofDual

@[simp]
theorem toDual_symm_eq : (@toDual α).symm = ofDual := rfl
#align order_dual.to_dual_symm_eq OrderDual.toDual_symm_eq

@[simp]
theorem ofDual_symm_eq : (@ofDual α).symm = toDual := rfl
#align order_dual.of_dual_symm_eq OrderDual.ofDual_symm_eq

@[simp]
theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a :=
  rfl
#align order_dual.to_dual_of_dual OrderDual.toDual_ofDual

@[simp]
theorem ofDual_toDual (a : α) : ofDual (toDual a) = a :=
  rfl
#align order_dual.of_dual_to_dual OrderDual.ofDual_toDual

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b :=
  Iff.rfl
#align order_dual.to_dual_inj OrderDual.toDual_inj

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b :=
  Iff.rfl
#align order_dual.of_dual_inj OrderDual.ofDual_inj

@[simp]
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le_to_dual OrderDual.toDual_le_toDual

@[simp]
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl
#align order_dual.to_dual_lt_to_dual OrderDual.toDual_lt_toDual

@[simp]
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.of_dual_le_of_dual OrderDual.ofDual_le_ofDual

@[simp]
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl
#align order_dual.of_dual_lt_of_dual OrderDual.ofDual_lt_ofDual

theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a :=
  Iff.rfl
#align order_dual.le_to_dual OrderDual.le_toDual

theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a :=
  Iff.rfl
#align order_dual.lt_to_dual OrderDual.lt_toDual

theorem toDual_le [LE α] {a : α} {b : αᵒᵈ} : toDual a ≤ b ↔ ofDual b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le OrderDual.toDual_le

theorem toDual_lt [LT α] {a : α} {b : αᵒᵈ} : toDual a < b ↔ ofDual b < a :=
  Iff.rfl
#align order_dual.to_dual_lt OrderDual.toDual_lt

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
protected def rec {C : αᵒᵈ → Sort*} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂
#align order_dual.rec OrderDual.rec

@[simp]
protected theorem «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl
#align order_dual.forall OrderDual.forall

@[simp]
protected theorem «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl
#align order_dual.exists OrderDual.exists

alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual

alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual

alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
#align has_le.le.of_dual LE.le.ofDual

alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual
#align has_lt.lt.of_dual LT.lt.ofDual

end OrderDual

/-! ### Lexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type*) :=
  α
#align lex Lex

/-- `toLex` is the identity function to the `Lex` of a type.  -/
@[match_pattern]
def toLex : α ≃ Lex α :=
  Equiv.refl _
#align to_lex toLex

/-- `ofLex` is the identity function from the `Lex` of a type.  -/
@[match_pattern]
def ofLex : Lex α ≃ α :=
  Equiv.refl _
#align of_lex ofLex

@[simp]
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl
#align to_lex_symm_eq toLex_symm_eq

@[simp]
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl
#align of_lex_symm_eq ofLex_symm_eq

@[simp]
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl
#align to_lex_of_lex toLex_ofLex

@[simp]
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl
#align of_lex_to_lex ofLex_toLex

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem toLex_inj {a b : α} : toLex a = toLex b ↔ a = b :=
  Iff.rfl
#align to_lex_inj toLex_inj

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b :=
  Iff.rfl
#align of_lex_inj ofLex_inj

/-- A recursor for `Lex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Lex.rec {β : Lex α → Sort*} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)
#align lex.rec Lex.rec

@[simp] lemma Lex.forall {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) := Iff.rfl
@[simp] lemma Lex.exists {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) := Iff.rfl
