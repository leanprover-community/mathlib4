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

open Mathlib.Tactic (subscriptTerm delabSubscript)

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

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for the notation `⦋m⦌ₙ`. -/
@[app_delab CategoryTheory.FullSubcategory.mk]
def delabMkNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
    let #[cat, .lam x _ body _, simplex, _] := (← getExpr).getAppArgs | failure
    -- check that this is a `FullSubcategory` of `SimplexCategory`
    guard <| cat.isConstOf ``SimplexCategory
    guard <| simplex.isAppOfArity ``SimplexCategory.mk 1
    -- check that the predicate matches `fun x ↦ x.len ≤ n`
    let_expr LE.le _ _ lhs _ := body | failure
    let_expr SimplexCategory.len simplex := lhs | failure
    guard <| simplex == .bvar 0
    -- if `pp.proofs` is set to `true`, include the proof `p : m ≤ n`
    let n ← withNaryArg 1 <| withBindingBody x <| withAppArg <| delabSubscript
    let m ← withNaryArg 2 <| withAppArg delab
    if (← getPPOption getPPProofs) then
      let p ← withAppArg delab
      `(⦋$m, $p⦌$n)
    else `(⦋$m⦌$n)

end SimplexCategory.Truncated
