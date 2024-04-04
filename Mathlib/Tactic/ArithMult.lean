/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ArithMult.Init

/-!
# Multiplicativity

We define the arith_mult tactic using aesop

-/

namespace ArithmeticFunction

/--
The `arith_mult` attribute used to tag `IsMultiplicative` statements for the
`arith_mult` tactic. -/
macro "arith_mult" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `IsMultiplicative):ident]))

/--
`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`. -/
macro (name := arith_mult) "arith_mult" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { aesop $c* (config :=
    { destructProductsTransparency := .reducible,
      applyHypsTransparency := .default,
      introsTransparency? := some .reducible,
      enableSimp := false } )
  (rule_sets := [$(Lean.mkIdent `IsMultiplicative):ident])})

/--
`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`, and prints out the generated
proof term. -/
macro (name := arith_mult?) "arith_mult?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { show_term { arith_mult $c* } })
