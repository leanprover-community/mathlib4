/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Algebra.Equiv
import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Notation for Galois group

The Galois group `Gal(L/K)` is implemented via `L ≃ₐ[K] L` in mathlib.
We provide such a notation in this file.

Although this notation works for all automorphism groups of algebras, we should only use this
notation when `L/K` is an extension of fields.
-/

section Notation

/--
Notation for `Gal(L/K) := L ≃ₐ[K] L`.

`L ≃ₐ[K] L` will pretty-print as `Gal(L/K)` when `L` and `K` are both fields.

Although this notation works for all automorphism groups of algebras, we should only use this
notation when `L/K` is an extension of fields.
-/
/- We use a precedence of 100 here to avoid `L` capturing `/` as the infix notation for division,
which has precedence 70. -/
macro "Gal(" L:term:100 "/" K:term ")" : term => `($L ≃ₐ[$K] $L)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for the `Gal(L/K)` notation. -/
@[app_delab AlgEquiv]
partial def delabGal : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  -- After Lean 4.19 the pretty printer clears local instances, so we re-add them here.
  -- TODO: remove this once the behavior changes.
  -- See [Zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Bug.3F.20Local.20instances.20not.20populated.20during.20delaboration/with/544850819).
  Meta.withLocalInstances (← getLCtx).decls.toList.reduceOption do
  guard <| (← getExpr).isAppOfArity ``AlgEquiv 8
  let [u, v, _] := (← getExpr).getAppFn'.constLevels! | failure
  let #[R, A, B, _, _, _, _, _] := (← getExpr).getAppArgs | failure
  guard (A == B) -- We require that A = B syntactically, not merely defeq.
  let some _ ← Meta.synthInstance? (.app (.const ``Field [u]) R) | failure
  let some _ ← Meta.synthInstance? (.app (.const ``Field [v]) A) | failure
  `(Gal($(← withNaryArg 1 <| delab)/$(← withNaryArg 0 <| delab)))

end Notation
