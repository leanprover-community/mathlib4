/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Init
import Qq

/-!
# simproc for `∃ a', ... ∧ a' = a ∧ ...`

This module implements the `existsAndEq` simproc that checks whether `P a'` has
the form `... ∧ a' = a ∧ ...` or `... ∧ a = a' ∧ ...` for the goal `∃ a', P a'`.
If so, it rewrites the latter as `P a`.
-/

open Lean Meta Qq

namespace existsAndEq

universe u in
private theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} {a : α} (h : ∀ b, p b → a = b) :
    (∃ b, p b) = p a := by
  apply propext
  constructor
  · intro h'
    obtain ⟨b, hb⟩ := h'
    rwa [h b hb]
  · intro h'
    exact ⟨a, h'⟩

/-- For an expression `p` of the form `fun (x : α) ↦ (body : Prop)`, checks whether
`body` implies `x = a` for some `a`, and constructs a proof of `(∃ x, p x) = p a` using
`exists_of_imp_eq`. -/
partial def findImpEqProof {u : Level} {α : Q(Sort u)} (p : Q($α → Prop)) :
    MetaM <| Option ((a : Q($α)) × Q((∃ x, $p x) = $p $a)) := do
  lambdaTelescope p fun xs (body : Q(Prop)) => do
    let #[(x : Q($α))] := xs | return none
    withLocalDeclQ .anonymous .default body fun h => withNewMCtxDepth do
      let .some ⟨res, proof⟩ ← go x h | return none
      let pf1 : Q(∀ (b : $α), $p b → $res = b) ← mkLambdaFVars #[x, h] proof
      return .some ⟨res, q(exists_of_imp_eq $pf1)⟩
where
  /-- Traverses the expression `h`, branching at each `And`, to find a proof of `x = a`
  for some `a`. -/
  go (x : Q($α)) {e : Q(Prop)} (h : Q($e)) : MetaM <| Option ((a : Q($α)) × Q($a = $x)) := do
    match e with
    | ~q(@Eq.{u} $β $a $b) =>
      let .defEq _ := ← isDefEqQ q($α) q($β) | return none
      if let .defEq _ ← isDefEqQ x a then
        return .some ⟨b, q(($h).symm)⟩
      else if let .defEq _ ← isDefEqQ x (b : Q($α)) then
        return .some ⟨a, q($h)⟩
      else
        return .none
    | ~q(And $a $b) =>
      if let .some res ← go x q(And.left $h) then
        return res
      if let .some res ← go x q(And.right $h) then
        return res
      return none
    | _ => return none

end existsAndEq

/-- Checks whether `P a'` has the form `... ∧ a' = a ∧ ...` or `... ∧ a = a' ∧ ...` in
the goal `∃ a', P a'`. If so, rewrites the goal as `P a`. -/
simproc existsAndEq (Exists (fun _ => And _ _)) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Prop), ~q(Exists $p) =>
    let .some ⟨_, pf⟩ ← existsAndEq.findImpEqProof p | return .continue
    return .visit <| .mk _ <| some q($pf)
  | _, _, _ => return .continue
