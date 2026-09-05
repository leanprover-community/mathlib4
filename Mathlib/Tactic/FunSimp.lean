/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.FunSimp.Attr
public import Mathlib.Tactic.FunSimp.Simproc

/-!
# The `fun_simp` tactic

The `fun_simp` tactic rewrites using lemmas tagged with the `@[fun_simp]` attribute. Its intended
use is simplifying bundled morphisms, which are often wrappers around more basic functions.

Unlike `simp`, this tactic can automatically eta-expand expressions when necessary. For example,
assuming that a lemma `f x y = x + y` is tagged with `@[fun_simp]`, the expression `f x` is
rewritten to `fun y => x + y`. Additionally, lemmas about the equality of bundled morphisms are used
for rewriting when the morphism is coerced to a function.

This tactic is also available in `conv` mode and as a `simp` set.
-/

public meta section

open Function Lean.Parser.Tactic

namespace Mathlib.Tactic.FunSimp

/--
The `fun_simp` tactic rewrites using lemmas tagged with the `@[fun_simp]` attribute. Its intended
use is simplifying bundled morphisms, which are often wrappers around more basic functions.

Unlike `simp`, this tactic can automatically eta-expand expressions when necessary. For example,
assuming that a lemma `f x y = x + y` is tagged with `@[fun_simp]`, the expression `f x` is
rewritten to `fun y => x + y`. Additionally, lemmas about the equality of bundled morphisms are used
for rewriting when the morphism is coerced to a function.
-/
macro (name := funSimpStx) "fun_simp" loc:(location)? : tactic =>
  `(tactic| simp only [fun_simp] $[$loc]?)

@[inherit_doc funSimpStx]
macro (name := convFunSimpStx) "fun_simp" : conv =>
  `(conv| simp only [fun_simp])

attribute [fun_simp] id curry uncurry const comp HasUncurry.uncurry

end Mathlib.Tactic.FunSimp
