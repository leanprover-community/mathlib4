/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Lean.Meta

/-!
# Additions to `Lean.Meta.CongrTheorems`
-/

namespace Lean.Meta

/-- Generates a congruence lemma for a function `f` for `numArgs` of its arguments.
The only `Lean.Meta.CongrArgKind` kinds that appear in such a lemma
are `.eq`, `.heq`, and `.subsingletonInst`.
The resulting lemma proves either an `Eq` or a `HEq` depending on whether the types
of the LHS and RHS are equal or not.

This function is a wrapper around `Lean.Meta.mkHCongrWithArity`.
It transforms the resulting congruence lemma by trying to automatically prove hypotheses
using subsingleton lemmas, and if they are so provable they are recorded with `.subsingletonInst`.
Note that this is slightly abusing `.subsingletonInst` since
(1) the argument might not be for a `Decidable` instance and
(2) the argument might not even be an instance. -/
def mkHCongrWithArity' (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let thm ← mkHCongrWithArity f numArgs
  process thm thm.type thm.argKinds.toList #[] #[] #[]
where
  /-- Process the congruence theorem by trying to pre-prove arguments using `prove`. -/
  process (cthm : CongrTheorem) (type : Expr) (argKinds : List CongrArgKind)
      (argKinds' : Array CongrArgKind) (params args : Array Expr) : MetaM CongrTheorem := do
    match argKinds with
    | [] =>
      if params.size == args.size then
        return cthm
      else
        let pf' ← mkLambdaFVars params (mkAppN cthm.proof args)
        return {proof := pf', type := ← inferType pf', argKinds := argKinds'}
    | argKind :: argKinds =>
      match argKind with
      | .eq | .heq =>
        forallBoundedTelescope type (some 3) fun params' type' => do
          let #[x, y, eq] := params' | unreachable!
          -- See if we can prove `eq` from previous parameters.
          let g := (← mkFreshExprMVar (← inferType eq)).mvarId!
          let g ← g.clear eq.fvarId!
          if (← observing? <| prove g params).isSome then
            process cthm type' argKinds (argKinds'.push .subsingletonInst)
              (params := params ++ #[x, y]) (args := args ++ #[x, y, .mvar g])
          else
            process cthm type' argKinds (argKinds'.push argKind)
              (params := params ++ params') (args := args ++ params')
      | _ => panic! "Unexpected CongrArgKind"
  /-- Close the goal given only the fvars in `params`, or else fails. -/
  prove (g : MVarId) (params : Array Expr) : MetaM Unit := do
    -- Prune the local context.
    let g ← g.cleanup
    -- Substitute equalities that come from only this congruence lemma.
    let [g] ← g.casesRec fun localDecl => do
      return (localDecl.type.isEq || localDecl.type.isHEq) && params.contains localDecl.toExpr
      | failure
    try g.refl; return catch _ => pure ()
    try g.hrefl; return catch _ => pure ()
    if ← g.proofIrrelHeq then return
    -- Make the goal be an eq and then try `Subsingleton.elim`
    let g ← g.heqOfEq
    if ← g.subsingletonElim then return
    -- We have no more tricks.
    failure

end Lean.Meta
