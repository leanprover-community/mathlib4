/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Simps.NotationClass
import Mathlib.Tactic.ToAdditive

/-!
# Notation classes for lattice operations

In this file we introduce typeclasses and definitions for lattice operations.

## Main definitions

* the `⊔` notation is used for `Max` since November 2024
* the `⊓` notation is used for `Min` since November 2024
* `HasCompl`: type class for the `ᶜ` notation
* `Top`: type class for the `⊤` notation
* `Bot`: type class for the `⊥` notation

## Notations

* `x ⊔ y`: lattice join operation;
* `x ⊓ y`: lattice meet operation;
* `xᶜ`: complement in a lattice;

-/

/-- Set / lattice complement -/
@[notation_class]
class HasCompl (α : Type*) where
  /-- Set / lattice complement -/
  compl : α → α

export HasCompl (compl)

@[inherit_doc]
postfix:1024 "ᶜ" => compl

/-! ### `Sup` and `Inf` -/

/-- Typeclass for the `⊔` (`\lub`) notation -/
@[deprecated Max (since := "2024-11-06"), notation_class, ext]
class Sup (α : Type*) where
  /-- Least upper bound (`\lub` notation) -/
  sup : α → α → α

/-- Typeclass for the `⊓` (`\glb`) notation -/
@[deprecated Min (since := "2024-11-06"), notation_class, ext]
class Inf (α : Type*) where
  /-- Greatest lower bound (`\glb` notation) -/
  inf : α → α → α

attribute [ext] Min Max

@[inherit_doc]
infixl:68 " ⊔ " => Max.max

@[inherit_doc]
infixl:69 " ⊓ " => Min.min

/-- Syntax typeclass for Heyting implication `⇨`. -/
@[notation_class]
class HImp (α : Type*) where
  /-- Heyting implication `⇨` -/
  himp : α → α → α

attribute [order_dual existing (reorder := 3 4) HImp.himp] HImp.himp

attribute [order_dual existing (reorder := 3 4) SDiff.sdiff] SDiff.sdiff

/-- Syntax typeclass for Heyting negation `￢`.

The difference between `HasCompl` and `HNot` is that the former belongs to Heyting algebras,
while the latter belongs to co-Heyting algebras. They are both pseudo-complements, but `compl`
underestimates while `HNot` overestimates. In boolean algebras, they are equal.
See `hnot_eq_compl`.
-/
@[notation_class]
class HNot (α : Type*) where
  /-- Heyting negation `￢` -/
  hnot : α → α

export HImp (himp)
export SDiff (sdiff)
export HNot (hnot)

/-- Heyting implication -/
infixr:60 " ⇨ " => himp

/-- Heyting negation -/
prefix:72 "￢" => hnot


/-- Typeclass for the `⊤` (`\top`) notation -/
@[notation_class, ext]
class Top (α : Type*) where
  /-- The top (`⊤`, `\top`) element -/
  top : α

/-- Typeclass for the `⊥` (`\bot`) notation -/
@[notation_class, ext]
class Bot (α : Type*) where
  /-- The bot (`⊥`, `\bot`) element -/
  bot : α

attribute [order_dual existing] Top

/-- The top (`⊤`, `\top`) element -/
notation "⊤" => Top.top

/-- The bot (`⊥`, `\bot`) element -/
notation "⊥" => Bot.bot

@[order_dual]
instance (priority := 100) top_nonempty (α : Type*) [Top α] : Nonempty α :=
  ⟨⊤⟩

attribute [match_pattern] Bot.bot Top.top
