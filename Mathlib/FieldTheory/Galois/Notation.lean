/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Algebra.Equiv
import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Notation for galois group

The galois group `Gal(L/K)` is implemented via `L ≃ₐ[K] L` in mathlib.
We provide such a notation in this file.

Although this notation works for all automorphism groups of algebras, we should only use this
notation when `L/K` is an extension of fields.
-/

section Notation

notation "Gal(" L:100 "/" K ")" => L ≃ₐ[K] L

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for the `Gal(L/K)` notation. -/
@[app_delab AlgEquiv]
partial def delabGal : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``AlgEquiv 8
  let [u, v, _] := (← getExpr).getAppFn'.constLevels! | failure
  let #[R, A, B, _, _, _, _, _] := (← getExpr).getAppArgs | failure
  guard (A == B) -- We require that A = B syntatically, not merely defeq.
  let some _ ← Meta.synthInstance? (.app (.const ``Field [u]) R) | failure
  let some _ ← Meta.synthInstance? (.app (.const ``Field [v]) A) | failure
  `(Gal($(← withNaryArg 1 <| delab)/$(← withNaryArg 0 <| delab)))

end Notation
