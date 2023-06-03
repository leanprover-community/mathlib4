/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Damiano Testa
-/
import Mathlib.Lean.Expr.Basic

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
* Deal with universes of auto-implicit Sorts -- fixed?
* Deal with named instances -- fixed?
-/

open Lean LocalDecl Elab Meta Tactic BinderInfo

/--  `qToUnder S T?` takes as input a string `S` and, optionally, another string `T?`.
It returns
* `Type T?` if `S` begins with `S = Type ?u.`;
* `Sort T?` if `S` begins with `S = Sort ?u.`;
otherwise, it leave `S` unchanged.  If the optional string `T?` is not given, it uses `T? := "_"`.
-/
def qToUnder (S : String) (T : String := "_") : String :=
if      "Type ?u.".isPrefixOf S then "Type " ++ T
else if "Sort ?u.".isPrefixOf S then "Sort " ++ T
else S

/-- `oneBlock L` assumes that `L` is a list of `LocalDecl` that all have the same
binder type (i.e. (strict) implicit, explicit, instance) and all have the same
type and returns the Format for printing it.
Example: `oneBlock [x,y,z] = {x y z : ℕ}`.
-/
def Lean.LocalDecl.oneBlock : List LocalDecl → MetaM Format
  | []    => pure ""
  | ls@(d::_) => do
    let (bi, type) := (d.binderInfo, d.type)
    let (l,r) := bi.brackets
    let comp := ls.map ((toString ∘ LocalDecl.userName) ·)
    let new := comp.map fun x =>
      let xspl := x.splitOn "."
      if bi != instImplicit && xspl.contains "_hyg" then xspl[0]! ++ "_hyg" else x
    let middle := " ".intercalate new
    let ppt := (← ppExpr type).pretty
    let pptype := if type.isSort then qToUnder ppt ("univ_" ++ new.getD 0 "bug!") else ppt
    let middle := if bi == instImplicit && (middle.splitOn ".").contains "_hyg" then ""
                  else (middle ++ " : ")
    -- is it possible to get the pretty-printed type, without going via `MetaM`?
    pure (l ++ middle ++ pptype ++ r )

def Lean.MetavarDecl.formatMVarDecls (decl : MetavarDecl) : MetaM Format := do
  let dcls := decl.lctx.decls.toList.reduceOption.drop 1
  let dgps := dcls.groupBy (fun x y => x.binderInfo == y.binderInfo ∧ x.type == y.type)
  let fmts := ← dgps.mapM (oneBlock ·)
  let indt := f!"\n    "
  let fmts := fmts.intersperse indt
  let coln := if (fmts.length = 0) then f!":" else f!" :"
  let finf := (fmts.foldr (· ++ ·) coln) ++ indt ++ (← ppExpr decl.type)
  -- a miserable hack to replace the hygienic dagger `✝` with `_hyg` so that it can be pasted.
  return (finf.pretty.replace "✝" "_hyg") ++ f!" := by\n  sorry"

/--
`extract_goal` formats the current goal as a stand-alone example.

It tries to produce an output that can be copy-pasted and just work.
It renames a "hygienic" variable `n✝` to `n_hyg`.
-/
elab (name := extractGoal) name:"extract_goal" : tactic => withMainContext do
  logInfoAt name (f!"example " ++ (← (← getMainDecl).formatMVarDecls))
