/-
Copyright (c) 2025 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Util.Superscript

/-! # Truncated simplex category notation

We define the notation `⦋m⦌ₙ` for the `m`-dimensional simplex in the
`n`-truncated simplex category. The truncation proof `p : m ≤ n` can also be
provided using the syntax `⦋m, p⦌ₙ`. This notation is available with
`open SimplexCategory.Truncated`.
-/

namespace SimplexCategory.Truncated

open CategoryTheory
open Mathlib.Tactic (subscriptTerm)

/-- A quick attempt to prove that `⦋m⦌` is `n`-truncated (`⦋m⦌.len ≤ n`). -/
scoped macro "trunc" : tactic =>
  `(tactic| dsimp only [SimplexCategory.len_mk] <;> omega)

/-- For `m ≤ n`, `⦋m⦌ₙ` is the `m`-dimensional simplex in `Truncated n`. The
proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term
scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, by first | trunc |
      fail "Failed to prove truncation property. Try writing `⦋m, by ...⦌ₙ`."⟩ :
      SimplexCategory.Truncated $n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

section Delab
open Mathlib.Tactic.Superscript (Mapping)
open Lean PrettyPrinter.Delaborator SubExpr

/-- Checks that the provided expression can be subscripted. -/
private partial def subscriptable (e : Expr) : DelabM Unit := do
  -- Any number or free variable with a subscriptable name is subscriptable.
  if (← name e).any isSubscriptable || (← delab) matches `($_:num) then return
  -- Addition and subtraction are subscriptable if their operands are.
  guard <| e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6
  let #[_, _, _, _, x, y] := e.getAppArgs | failure
  let _ ← withNaryArg 4 <| subscriptable x
  let _ ← withAppArg <| subscriptable y
where
  -- Return the user-facing name of any constant or free variable.
  name : Expr → MetaM (Option Name)
    | Expr.const name _ => pure name
    | Expr.fvar name => name.getUserName
    | _ => pure none
  -- Return `true` if every character in `s` can be subscripted.
  isSubscriptable (s : Name) : Bool :=
    s.toString.toList.all Mapping.subscript.toSpecial.contains

/-- Checks that the provided expression can be subscripted before delaborating. -/
def Meta.subscript (e : Expr) : Delab := subscriptable e >>= fun () ↦ delab

/-- Delaborator for the notation `⦋m⦌ₙ`. -/
@[app_delab FullSubcategory.mk]
def delabMkNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
    let #[cat, .lam x _ body _, simplex, _] := (← getExpr).getAppArgs | failure
    -- check that this is a `FullSubcategory` of `SimplexCategory`
    guard <| cat.isConstOf ``SimplexCategory
    guard <| simplex.isAppOfArity ``SimplexCategory.mk 1
    -- check that the predicate matches `fun x ↦ x.len ≤ n`
    let_expr LE.le _ _ lhs rhs := body | failure
    let_expr SimplexCategory.len simplex := lhs | failure
    guard <| simplex == .bvar 0
    -- if `pp.proofs` is set to `true`, include the proof `p : m ≤ n`
    let n ← withNaryArg 1 <| withBindingBody x <| withAppArg <| Meta.subscript rhs
    let m ← withNaryArg 2 <| withAppArg delab
    if (← getPPOption getPPProofs) then
      let p ← withAppArg delab
      `(⦋$m, $p⦌$n)
    else `(⦋$m⦌$n)

end Delab
end SimplexCategory.Truncated
