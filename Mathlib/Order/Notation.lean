/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Yaël Dillies
-/
import Qq
import Mathlib.Lean.PrettyPrinter.Delaborator
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Simps.NotationClass

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

namespace Mathlib.Meta

open Lean Meta PrettyPrinter Delaborator SubExpr Qq

-- irreducible to not confuse Qq
@[irreducible] private def linearOrderExpr (u : Level) : Q(Type u → Type u) :=
  .const `LinearOrder [u]
private def linearOrderToMax (u : Level) : Q((a : Type u) → $(linearOrderExpr u) a → Max a) :=
  .const `LinearOrder.toMax [u]
private def linearOrderToMin (u : Level) : Q((a : Type u) → $(linearOrderExpr u) a → Min a) :=
  .const `LinearOrder.toMin [u]

/--
Return `true` if `LinearOrder` is imported and `inst` comes from a `LinearOrder e` instance.

We use a `try catch` block to make sure there are no surprising errors during delaboration.
-/
private def hasLinearOrder (u : Level) (α : Q(Type u)) (cls : Q(Type u → Type u))
    (toCls : Q((α : Type u) → $(linearOrderExpr u) α → $cls α)) (inst : Q($cls $α)) :
    MetaM Bool := do
  try
    withNewMCtxDepth do
    -- `isDefEq` may call type class search to instantiate `mvar`, so we need the local instances
    -- In Lean 4.19 the pretty printer clears local instances, so we re-add them here.
    -- TODO(Jovan): remove
    withLocalInstances (← getLCtx).decls.toList.reduceOption do
      let mvar ← mkFreshExprMVarQ q($(linearOrderExpr u) $α) (kind := .synthetic)
      let inst' : Q($cls $α) := q($toCls $α $mvar)
      isDefEq inst inst'
  catch _ =>
    -- For instance, if `LinearOrder` is not yet imported.
    return false

/-- Delaborate `max x y` into `x ⊔ y` if the type is not a linear order. -/
@[delab app.Max.max]
def delabSup : Delab := do
  let_expr f@Max.max α inst _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  if ← hasLinearOrder u α q(Max) q($(linearOrderToMax u)) inst then
    failure -- use the default delaborator
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊔ $y)
  annotateGoToSyntaxDef stx

/-- Delaborate `min x y` into `x ⊓ y` if the type is not a linear order. -/
@[delab app.Min.min]
def delabInf : Delab := do
  let_expr f@Min.min α inst _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  if ← hasLinearOrder u α q(Min) q($(linearOrderToMin u)) inst then
    failure -- use the default delaborator
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊓ $y)
  annotateGoToSyntaxDef stx

end Mathlib.Meta

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
