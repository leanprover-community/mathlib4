/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Damiano Testa
-/
import Std.Data.List.Basic

/-!
#  `extract_goal`: Format the current goal as a stand-alone example

Useful for testing tactics or creating
[minimal working examples](https://leanprover-community.github.io/mwe.html).

```lean
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal

/-
example (i j k : ℕ)
    (h₀ : i ≤ j)
    (h₁ : j ≤ k) :
    i ≤ k := by
  sorry
-/
```

* TODO: Deal with `let`
* TODO: Add functionality to produce a named `theorem` via `extract_goal thmName`
* TODO: Add tactic code actions?

Check that these issues are resolved:
* Deal with universes -- fixed?  Not much to do, it seems.
* Deal with named instances -- fixed?
-/

/-- Translate a `BinderInfo` into the appropriate left-right pair of parentheses. -/
def Lean.BinderInfo.toParens : BinderInfo → String × String
  | .default =>        ("(", ")")
  | .implicit =>       ("{", "}")
  | .strictImplicit => ("⦃", "⦄")
  | .instImplicit =>   ("[", "]")

open Lean LocalDecl Elab Meta Tactic BinderInfo

/-- `oneBlock L` assumes that `L` is a list of `LocalDecl` that all have the same
binder type (i.e. (strict) implicit, explicit, instance) and all have the same
type and returns the Format for printing it.
Example: `oneBlock [x,y,z] = {x y z : ℕ}`.
-/
def Lean.LocalDecl.oneBlock : List LocalDecl → MetaM Format
  | []    => pure ""
  | ls@(d::_) =>
    let (bi, type) := (d.binderInfo, d.type)
    let (l,r) := bi.toParens
    let comp := ls.map ((toString ∘ LocalDecl.userName) ·)
    let new := comp.map fun x =>
      let xspl := x.splitOn "."
      if bi != instImplicit && xspl.contains "_hyg" then xspl[0]! ++ "_hyg" else x
    let middle := " ".intercalate new
    let middle := if bi == instImplicit && (middle.splitOn ".").contains "_hyg" then ""
                  else (middle ++ " : ")
    do pure (l ++ middle ++ (← ppExpr type) ++ r )

/--
`extract_goal` formats the current goal as a stand-alone example.

It tries to produce an output that can be copy-pasted and just work.
It renames a "hygienic" variable `n✝` to `n_hyg`.
-/
elab (name := extractGoal) name:"extract_goal" : tactic => do (← getMainGoal).withContext do
  let dc := (← getLCtx).decls.toList.reduceOption.drop 1
  let gps := dc.groupBy (fun x y => x.binderInfo == y.binderInfo ∧ x.type == y.type)
  let fmts := ← gps.mapM (oneBlock ·)
  let ind : Format := "\n    "
  let fmts := fmts.intersperse ind
  let tgt := ← getMainTarget
  -- a miserable hack to replace the hygienic dagger `✝` with `_hyg` so that it can be pasted.
  let targ := (← ppExpr tgt).pretty.replace "✝" "_hyg"
  let bod := f!"example " ++ (fmts.foldr (fun x y => f!"{x}" ++ y) f!" :") ++ ind ++ targ
  logInfoAt name (bod ++ f!" := by\n  sorry")
