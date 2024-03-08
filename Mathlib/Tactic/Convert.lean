/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Congr!

/-!
# The `convert` tactic.
-/

open Lean Meta Elab Tactic

/--
Close the goal `g` using `Eq.mp v e`,
where `v` is a metavariable asserting that the type of `g` and `e` are equal.
Then call `MVarId.congrN!` (also using local hypotheses and reflexivity) on `v`,
and return the resulting goals.

With `sym = true`, reverses the equality in `v`, and uses `Eq.mpr v e` instead.
With `depth = some n`, calls `MVarId.congrN! n` instead, with `n` as the max recursion depth.
-/
def Lean.MVarId.convert (e : Expr) (sym : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) (g : MVarId) :
    MetaM (List MVarId) := do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if sym then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if sym then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns

namespace Mathlib.Tactic

/--
The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine e`,
but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal using the same strategies as the `congr!` tactic.
For example, in the proof state

```lean
n : ℕ,
e : Prime (2 * n + 1)
⊢ Prime (n + n + 1)
```

the tactic `convert e using 2` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The `using 2` indicates it should iterate the congruence algorithm up to two times,
where `convert e` would use an unrestricted number of iterations and lead to two
impossible goals: `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.

A variant configuration is `convert (config := .unfoldSameFun) e`, which only equates function
applications for the same function (while doing so at the higher `default` transparency).
This gives the same goal of `⊢ n + n = 2 * n` without needing `using 2`.

The `convert` tactic applies congruence lemmas eagerly before reducing,
therefore it can fail in cases where `exact` succeeds:
```lean
def p (n : ℕ) := True
example (h : p 0) : p 1 := by exact h -- succeeds
example (h : p 0) : p 1 := by convert h -- fails, with leftover goal `1 = 0`
```
Limiting the depth of recursion can help with this. For example, `convert h using 1` will work
in this case.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr!`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr! n`). In the example, `convert e using 1`
would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.

Refer to the `congr!` tactic to understand the congruence operations. One of its many
features is that if `x y : t` and an instance `Subsingleton t` is in scope,
then any goals of the form `x = y` are solved automatically.

Like `congr!`, `convert` takes an optional `with` clause of `rintro` patterns,
for example `convert e using n with x y z`.

The `convert` tactic also takes a configuration option, for example
```lean
convert (config := {transparency := .default}) h
```
These are passed to `congr!`. See `Congr!.Config` for options.
-/
syntax (name := convert) "convert" (Parser.Tactic.config)? " ←"? ppSpace term (" using " num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic

elab_rules : tactic
| `(tactic| convert $[$cfg:config]? $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← Congr!.elabConfig (mkOptionalNode cfg)
    let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ←
      withCollectingNewGoalsFrom (allowNaturalHoles := true) (tagSuffix := `convert) do
        -- Allow typeclass inference failures since these will be inferred by unification
        -- or else become new goals
        withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
          let t ← elabTermEnsuringType (mayPostpone := true) term expectedType
          -- Process everything so that tactics get run, but again allow TC failures
          Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
          -- Use a type hint to ensure we collect goals from the type too
          mkExpectedTypeHint t (← inferType t)
    liftMetaTactic fun g ↦
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs

-- FIXME restore when `add_tactic_doc` is ported.
-- add_tactic_doc
-- { name       := "convert",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.convert],
--   tags       := ["congruence"] }

/--
`convert_to g using n` attempts to change the current goal to `g`, but unlike `change`,
it will generate equality proof obligations using `congr! n` to resolve discrepancies.
`convert_to g` defaults to using `congr! 1`.
`convert_to` is similar to `convert`, but `convert_to` takes a type (the desired subgoal) while
`convert` takes a proof term.
That is, `convert_to g using n` is equivalent to `convert (?_ : g) using n`.

The syntax for `convert_to` is the same as for `convert`, and it has variations such as
`convert_to ← g` and `convert_to (config := {transparency := .default}) g`.
-/
syntax (name := convertTo) "convert_to" (Parser.Tactic.config)? " ←"? ppSpace term (" using " num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic

macro_rules
| `(tactic| convert_to $[$cfg]? $[←%$sym]? $term $[with $ps?*]?) =>
  `(tactic| convert $[$cfg]? $[←%$sym]? (?_ : $term) using 1 $[with $ps?*]?)
| `(tactic| convert_to $[$cfg]? $[←%$sym]? $term using $n $[with $ps?*]?) =>
  `(tactic| convert $[$cfg]? $[←%$sym]? (?_ : $term) using $n $[with $ps?*]?)

/--
`ac_change g using n` is `convert_to g using n` followed by `ac_rfl`. It is useful for
rearranging/reassociating e.g. sums:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```
-/
syntax (name := acChange) "ac_change " term (" using " num)? : tactic

macro_rules
| `(tactic| ac_change $t $[using $n]?) => `(tactic| convert_to $t:term $[using $n]? <;> try ac_rfl)

end Mathlib.Tactic
