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

* `HasCompl`: type class for the `ᶜ` notation
* `Top`: type class for the `⊤` notation
* `Bot`: type class for the `⊥` notation

## Notations

* `xᶜ`: complement in a lattice;
* `x ⊔ y`: supremum/join, which is notation for `max x y`;
* `x ⊓ y`: infimum/meet, which is notation for `min x y`;

We implement a delaborator that pretty prints `max x y`/`min x y` as `x ⊔ y`/`x ⊓ y`
if and only if the order on `α` does not have a `LinearOrder α` instance (where `x y : α`).

This is so that in a lattice we can use the same underlying constants `max`/`min`
as in linear orders, while using the more idiomatic notation `x ⊔ y`/`x ⊓ y`.
Lemmas about the operators `⊔` and `⊓` should use the names `sup` and `inf` respectively.

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

/--
The supremum/join operation: `x ⊔ y`. It is notation for `max x y`
and should be used when the type is not a linear order.
-/
syntax:68 term:68 " ⊔ " term:69 : term

/--
The infimum/meet operation: `x ⊓ y`. It is notation for `min x y`
and should be used when the type is not a linear order.
-/
syntax:69 term:69 " ⊓ " term:70 : term

macro_rules
| `($a ⊔ $b) => `(Max.max $a $b)
| `($a ⊓ $b) => `(Min.min $a $b)

section Delab

open Lean Meta PrettyPrinter Delaborator SubExpr Qq

/--
Return `true` if `LinearOrder` is imported and `inst` comes from a `LinearOrder e` instance.

We use a `try catch` block to make sure there are no surprising errors during delaboration.
-/
private def hasLinearOrder (u : Level) (α : Q(Type u)) (cls linearOrder : Q(Type u → Type u))
    (toCls : Q((α : Type u) → $linearOrder α → $cls α))
    (inst : Q($cls $α)) : MetaM Bool := do
  try
    -- `isDefEq` may call type class syntesis to instantiate `mvar`, so we need the local instances
    withLocalInstances (← getLCtx).decls.toList.reduceOption do
      let mvar ← mkFreshExprMVarQ q($linearOrder $α) (kind := .synthetic)
      let inst' : Q($cls $α) := q($toCls $α $mvar)
      isDefEq inst inst'
  catch _ =>
    return false

@[delab app.Max.max]
def elabSup : Delab := do
  let_expr f@Max.max α inst _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  let linearOrder : Q(Type u → Type u) := .const `LinearOrder [u]
  let linearOrderToMax : Q((a : Type u) → $linearOrder a → Max a) := .const `LinearOrder.toMax [u]
  if ← hasLinearOrder u α q(Max.{u}) linearOrder linearOrderToMax inst then
    failure -- use the default delaborator
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ⊔ $y)

@[delab app.Min.min]
def elabInf : Delab := do
  let_expr f@Min.min α inst _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  let linearOrder : Q(Type u → Type u) := .const `LinearOrder [u]
  let linearOrderToMin : Q((a : Type u) → $linearOrder a → Min a) := .const `LinearOrder.toMin [u]
  if ← hasLinearOrder u α q(Min.{u}) linearOrder linearOrderToMin inst then
    failure -- use the default delaborator
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
