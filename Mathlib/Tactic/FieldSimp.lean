/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw
-/

import Mathlib.Tactic.FieldSimp.Discharger

/-!
# `field_simp` tactic

Tactic to clear denominators in algebraic expressions, based on `simp` with a specific simpset.
-/

namespace Mathlib.Tactic.FieldSimp

open Lean Elab.Tactic Parser.Tactic Lean.Meta

initialize registerTraceClass `Tactic.field_simp

/-- The list of lemma's that aren't used in `field_simp`.

`one_div`, `mul_eq_zero` and `one_divp` are excluded because we don't want those rewrites.

The remaining constants are excluded for efficiency. These are lemmas consisting of just
`*`, `/` and `=` that are applicable in a typeclass that can't be a field. -/
def fieldSimpExcluded : List Name := [
  ``one_div, ``mul_eq_zero, ``one_divp,

  ``div_self', ``div_div_cancel, ``div_div_cancel_left,
  ``div_mul_cancel, ``div_mul_cancel_left, ``div_mul_cancel_right,
  ``mul_div_cancel, ``mul_div_cancel_left, ``mul_div_cancel_right,
  ``div_div_div_cancel_left, ``div_div_div_cancel_right,
  ``div_mul_div_cancel, ``div_mul_div_cancel', ``div_mul_mul_cancel,
  ``mul_div_div_cancel, ``mul_mul_div_cancel,

  ``div_eq_self,
  ``mul_eq_right, ``mul_eq_left, ``right_eq_mul, ``left_eq_mul,
  ``div_left_inj, ``div_right_inj, ``mul_left_inj, ``mul_right_inj]

/--
The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
iterating the following steps:

- write an inverse as a division
- in any product, move the division to the right
- if there are several divisions in a product, group them together at the end and write them as a
  single division
- reduce a sum to a common denominator

If the goal is an equality, this simpset will also clear the denominators, so that the proof
can normally be concluded by an application of `ring`.

`field_simp [hx, hy]` is a short form for
`simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, hx, hy, field_simps]`

Note that this naive algorithm will not try to detect common factors in denominators to reduce the
complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
complicated expressions in the next step.

As always with the simplifier, reduction steps will only be applied if the preconditions of the
lemmas can be checked. This means that proofs that denominators are nonzero should be included. The
fact that a product is nonzero when all factors are, and that a power of a nonzero number is
nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
should be given explicitly. If your expression is not completely reduced by the simplifier
invocation, check the denominators of the resulting expression and provide proofs that they are
nonzero to enable further progress.

To check that denominators are nonzero, `field_simp` will look for facts in the context, and
will try to apply `norm_num` to close numerical goals.

The invocation of `field_simp` removes the lemma `one_div` from the simpset, as this lemma
works against the algorithm explained above. It also removes
`mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0`, as `norm_num` can not work on disjunctions to
close goals of the form `24 ≠ 0`, and replaces it with `mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0`
creating two goals instead of a disjunction.

For example,
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring
```

Moreover, the `field_simp` tactic can also take care of inverses of units in
a general (commutative) monoid/ring and partial division `/ₚ`, see `Algebra.Group.Units`
for the definition. Analogue to the case above, the lemma `one_divp` is removed from the simpset
as this works against the algorithm. If you have objects with an `IsUnit x` instance like
`(x : R) (hx : IsUnit x)`, you should lift them with
`lift x to Rˣ using id hx; rw [IsUnit.unit_of_val_units] clear hx`
before using `field_simp`.

See also the `cancel_denoms` tactic, which tries to do a similar simplification for expressions
that have numerals in denominators.
The tactics are not related: `cancel_denoms` will only handle numeric denominators, and will try to
entirely remove (numeric) division from the expression by multiplying by a factor.
-/
syntax (name := fieldSimp) "field_simp" optConfig (discharger)? (&" only")?
  (simpArgs)? (location)? : tactic

elab_rules : tactic
| `(tactic| field_simp $cfg:optConfig $[(discharger := $dis)]? $[only%$only?]?
    $[$sa:simpArgs]? $[$loc:location]?) => withMainContext do
  let cfg ← elabSimpConfig cfg .simp
  -- The `field_simp` discharger relies on recursively calling the discharger.
  -- Prior to https://github.com/leanprover/lean4/pull/3523,
  -- the maxDischargeDepth wasn't actually being checked: now we have to set it higher.
  let cfg := { cfg with maxDischargeDepth := max cfg.maxDischargeDepth 7 }
  let loc := expandOptLocation (mkOptionalNode loc)

  let dis ← match dis with
  | none => pure discharge
  | some d => do
    let ⟨_, d⟩ ← tacticToDischarge d
    pure d

  let thms0 ← if only?.isSome then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else do
    let thms0 ← getSimpTheorems
    fieldSimpExcluded.foldlM (init := thms0) fun thms0 name => thms0.erase (.decl name)

  let some ext ← getSimpExtension? `field_simps | throwError "field_simps not found"
  let thms ← ext.getTheorems

  let ctx ← Simp.mkContext cfg
    (simpTheorems := #[thms, thms0])
    (congrTheorems := ← getSimpCongrTheorems)

  let r ← elabSimpArgs (sa.getD ⟨.missing⟩) ctx (simprocs := {}) (eraseLocal := false) .simp
  _ ← simpLocation r.ctx {} dis loc

end Mathlib.Tactic.FieldSimp

/-!
 We register `field_simp` with the `hint` tactic.
 -/
register_hint field_simp
