/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Simps.NotationClass
import Qq

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

@[inherit_doc Max.max]
syntax:68 (name := sup) term:68 " ⊔ " term:69 : term

@[inherit_doc Min.min]
syntax:69 (name := inf) term:69 " ⊓ " term:70 : term

macro_rules
| `($a ⊔ $b) => `(Max.max $a $b)
| `($a ⊓ $b) => `(Min.min $a $b)

section Delab

open Lean Meta PrettyPrinter Delaborator SubExpr Qq

private def hasLinearOrder (u : Level) (e : Q(Type $u)) : MetaM Bool := do
  try
    _ ← synthInstance (.app (.const `LinearOrder [u]) e)
    return true
  catch _ =>
    return false

@[delab app.Max.max]
def elabSup : Delab := do
  let_expr f@Max.max α _ _ _ := ← getExpr | failure
  if ← hasLinearOrder f.constLevels![0]! α then failure -- use the default delaborator
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ⊔ $y)

@[delab app.Min.min]
def elabInf : Delab := do
  let_expr f@Min.min α _ _ _ := ← getExpr | failure
  if ← hasLinearOrder f.constLevels![0]! α then failure -- use the default delaborator
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ⊓ $y)

end Delab

/-- Syntax typeclass for Heyting implication `⇨`. -/
@[notation_class]
class HImp (α : Type*) where
  /-- Heyting implication `⇨` -/
  himp : α → α → α

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

/-- The top (`⊤`, `\top`) element -/
notation "⊤" => Top.top

/-- The bot (`⊥`, `\bot`) element -/
notation "⊥" => Bot.bot

instance (priority := 100) top_nonempty (α : Type*) [Top α] : Nonempty α :=
  ⟨⊤⟩

instance (priority := 100) bot_nonempty (α : Type*) [Bot α] : Nonempty α :=
  ⟨⊥⟩

attribute [match_pattern] Bot.bot Top.top
