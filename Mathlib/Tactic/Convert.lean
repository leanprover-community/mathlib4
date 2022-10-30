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


-- This is yoinked from core so that we can pass the `closeEasy` parameter.
/--
Applies `congr` recursively up to depth `n`.
If `closeEasy := true`, it tries to close new subgoals using `Eq.refl` and `assumption`.
-/
def Lean.MVarId.congrN' (mvarId : MVarId) (n : Nat) (closeEasy := true) : MetaM (List MVarId) := do
  if n == 1 then
    mvarId.congr closeEasy
  else
    let (_, s) ← go n mvarId |>.run #[]
    return s.toList
where
  /-- Auxiliary definition for `congrN'`. -/
  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    match n with
    | 0 => modify (·.push mvarId)
    | n+1 =>
      let some mvarIds ← observing? (m := MetaM) (mvarId.congr closeEasy)
        | modify (·.push mvarId)
      mvarIds.forM (go n)

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
  try
    m.assumption <|> (withTransparency .reducible m.refl)
    return []
  catch _ => try
    m.congrN' (depth.getD 1000) (closeEasy := true)
  catch _ => try
    m.refl
    return []
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

If `x y : t`, and an instance `subsingleton t` is in scope, then any goals of the form
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
  liftMetaTactic fun g => return (← g.convert e sym.isSome (n.map (·.getNat))) ++ gs

-- FIXME restore when `add_tactic_doc` is ported.
-- add_tactic_doc
-- { name       := "convert",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.convert],
--   tags       := ["congruence"] }
