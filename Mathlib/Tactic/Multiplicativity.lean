/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Tactic.Multiplicativity.Init

/-
# Measurability

We define the measurability tactic using aesop

-/

namespace Nat.ArithmeticFunction

/--
The `multiplicativity` attribute used to tag `IsMultiplicative` statements for the
`multiplicativity` tactic. -/
macro "multiplicativity" : attr =>
  `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `IsMultiplicative):ident]))

/--
`multiplicativity` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `multiplicativity`. -/
macro (name := multiplicativity) "multiplicativity" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { aesop $c* (options :=
  { destructProductsTransparency := .reducible, applyHypsTransparency := .default, introsTransparency? := some .reducible, terminal := false } )
  (simp_options := { enabled := false})
  (rule_sets [$(Lean.mkIdent `IsMultiplicative):ident])})

/--
`multiplicativity` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `multiplicativity`, and prints out the generated
proof term. -/
macro (name := multiplicativity?) "multiplicativity?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { show_term { multiplicativity $c* } })
