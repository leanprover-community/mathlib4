/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# The `convert` tactic.
-/

open Lean Meta Elab Tactic

/--
Close the goal `g` using `Eq.mp v e`,
where `v` is a metavariable asserting that the type of `g` and `e` are equal.
Then call `MVarId.congr` (also using local hypotheses and reflexivity) on `v`,
and return the resulting goals.

With `sym = true`, reverses the equality in `v`, and uses `Eq.mpr v e` instead.
With `depth = some n`, calls `MVarId.congrN` instead, with `n` as the max recursion depth.
-/
def Lean.MVarId.convert (e : Expr) (sym : Bool) (depth : Option Nat := none) (g : MVarId) :
    MetaM (List MVarId) := do
  let src ← whnfD (← inferType e)
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if sym then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if sym then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  try m.congrN (depth.getD 1000000)
  catch _ => return [m]

/--
The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine e`,
but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal. For example, in the proof state

```lean
n : ℕ,
e : prime (2 * n + 1)
⊢ prime (n + n + 1)
```

the tactic `convert e` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The `convert` tactic applies congruence lemmas eagerly before reducing,
therefore it can fail in cases where `exact` succeeds:
```lean
def p (n : ℕ) := true
example (h : p 0) : p 1 := by exact h -- succeeds
example (h : p 0) : p 1 := by convert h -- fails, with leftover goal `1 = 0`
```

If `x y : t`, and an instance `Subsingleton t` is in scope, then any goals of the form
`x = y` are solved automatically.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr'`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr' n`). In the example, `convert e using
1` would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.
-/
syntax (name := convert) "convert " "← "? term (" using " num)? : tactic

elab_rules : tactic
| `(tactic| convert $[←%$sym]? $term $[using $n]?) => withMainContext do
  let (e, gs) ← elabTermWithHoles term
    (← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))) (← getMainTag)
  liftMetaTactic fun g ↦ return (← g.convert e sym.isSome (n.map (·.getNat))) ++ gs

-- FIXME restore when `add_tactic_doc` is ported.
-- add_tactic_doc
-- { name       := "convert",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.convert],
--   tags       := ["congruence"] }

/--
`convert_to g using n` attempts to change the current goal to `g`, but unlike `change`,
it will generate equality proof obligations using `congr n` to resolve discrepancies.
`convert_to g` defaults to using `congr 1`.
`convert_to` is similar to `convert`, but `convert_to` takes a type (the desired subgoal) while
`convert` takes a proof term.
That is, `convert_to g using n` is equivalent to `convert (?_ : g) using n`.
-/
syntax (name := convertTo) "convert_to " term (" using " num)? : tactic

macro_rules
| `(tactic| convert_to $term $[using $n]?) =>
  `(tactic| convert (?_ : $term) $[using $n]?)
