/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Init

/-!
# simproc for `∃ a', ... ∧ a' = a ∧ ...`

This module implements the `existsAndEq` simproc that triggers on goals of the form `∃ a, body` and
checks whether `body` has the form `... ∧ a = a' ∧ ...` or `... ∧ a' = a ∧ ...` for some `a'` that
is independent of `a`. If so, it replaces all occurrences of `a` with `a'` and removes the
quantifier.
-/

open Lean Meta

namespace existsAndEq

universe u in
private theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ b, p b → a = b) :
    (∃ b, p b) = p a := by
  grind

/-- For an expression `p` of the form `fun (x : α) ↦ (body : Prop)`, checks whether
`body` implies `x = a` for some `a`, and constructs a proof of `(∃ x, p x) = p a` using
`exists_of_imp_eq`. -/
partial def findImpEqProof (p : Expr) :
    MetaM <| Option (Expr × Expr) := do
  lambdaTelescope p fun xs body => do
    let #[x] := xs | return none
    withLocalDecl .anonymous .default body fun h => withNewMCtxDepth do
      let .some ⟨res, proof⟩ ← go x h | return none
      let pf1 ← mkLambdaFVars #[x, h] proof
      return .some ⟨res, ← mkAppM ``exists_of_imp_eq #[res, pf1]⟩
where
  /-- Traverses the expression `h`, branching at each `And`, to find a proof of `x = a`
  for some `a`. -/
  go (x h : Expr) : MetaM <| Option (Expr × Expr) := do
    match (← inferType h).getAppFnArgs with
    | (``Eq, #[β, a, b]) =>
      if !(← isDefEq (← inferType x) β) then
        return none
      if (← isDefEq x a) && !(b.containsFVar x.fvarId!) then
        return .some ⟨b, ← mkAppM ``Eq.symm #[h]⟩
      if (← isDefEq x b) && !(a.containsFVar x.fvarId!) then
        return .some ⟨a, h⟩
      else
        return .none
    | (``And, #[_, _]) =>
      if let .some res ← go x (← mkAppM ``And.left #[h]) then
        return res
      if let .some res ← go x (← mkAppM ``And.right #[h]) then
        return res
      return none
    | _ => return none

end existsAndEq

/-- Triggers on goals of the form `∃ a, body` and checks whether `body` has the
form `... ∧ a = a' ∧ ...` or `... ∧ a' = a ∧ ...` for some `a'` that is independent of `a`.
If so, it replaces all occurrences of `a` with `a'` and removes the quantifier. -/
simproc existsAndEq (Exists (fun _ => And _ _)) := fun e => do
  match e.getAppFnArgs with
  | (``Exists, #[_, p]) =>
    let .some ⟨res, pf⟩ ← existsAndEq.findImpEqProof p | return .continue
    return .visit {expr := mkApp p res, proof? := pf}
  | _ => return .continue
