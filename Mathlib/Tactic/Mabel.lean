/-
Copyright (c) 2024 Sam Ezeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Ezeh
-/
import Mathlib.Tactic.NormNum
import Mathlib.Util.AtomM
import Mathlib.Tactic.Abel
import Qq

/-!
# The `mabel` tactic

Evaluate expressions in the language of multiplicative, commutative monoids and groups.

-/

set_option autoImplicit true

namespace Mathlib.Tactic.Mabel
open Lean Elab Meta Tactic Qq Expr PrettyPrinter

initialize registerTraceClass `mabel
initialize registerTraceClass `mabel.detail

lemma Additive_identity : Additive x = x := by rfl
lemma ofMul_identity (x : α) : Additive.ofMul x = x := by
  unfold Additive.ofMul
  rfl

/-- Tactic for converting equations in the language of
multiplicative, commutative monoids and groups to those in the language
of additive, commutative monoids and groups.
-/
syntax (name := to_additive) "to_additive" : tactic

/-- The `to_additive` tactic, which solves converts equations in the language of
multiplicative commutative additive groups (or monoids) to those in additive structures. -/
elab_rules : tactic | `(tactic| to_additive) => withMainContext do
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "to_additive requires an equality goal"
  let lhs ← delab e₁
  let rhs ← delab e₂
  evalTactic $ ← `(tactic|
    conv => {
      lhs
      rw [← ofMul_identity $lhs];
    } <;>
    conv => {
      rhs
      rw [ ← ofMul_identity $rhs]
    } <;>
    simp [
      ofMul_mul, ofMul_pow, ofMul_one,
      ofMul_inv, ofMul_div, ofMul_zpow,
      ofMul_eq_zero, ofMul_div
    ])


/--
Tactic for evaluating expressions in multiplicative abelian groups.

* `mabel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `mabel1` fails if the target is not an equality.

For example:
```
example [CommMonoid α] (a b : α) : a * (b * a) = a * a * b := by mabel
example [CommGroup α] (a : α) : a^(3 : ℤ) = a * a^(2 : ℤ) := by mabel
```

See also the `abel` tactic.
-/
macro (name := mabel) "mabel" : tactic =>
  `(tactic| (to_additive <;> abel))
@[inherit_doc mabel] macro "mabel1" : tactic =>
  `(tactic| (to_additive <;> abel1))
@[inherit_doc mabel] macro "mabel!" : tactic =>
  `(tactic| (to_additive <;> abel!))
@[inherit_doc mabel] macro "mabel1!" : tactic =>
  `(tactic| (to_additive <;> abel1!))
@[inherit_doc mabel] macro "mabel_nf" : tactic =>
  `(tactic| (to_additive <;> abel_nf))

/--
The tactic `mabel` evaluates expressions in multiplicative abelian groups.
This is the conv tactic version, which rewrites a target which is an abel equality to `True`.

See also the `mabel` tactic.
-/
macro (name := abelConv) "mabel" : conv =>
  `(conv| discharge => (to_additive <;> abel))
@[inherit_doc abelConv] macro "mabel!" : conv =>
  `(conv| discharge => (to_additive <;> abel!))
