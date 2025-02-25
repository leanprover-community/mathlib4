import Qq

open Lean Meta Qq

universe u in
theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} {a : α} (h : ∀ b, p b → a = b) : (∃ b, p b) ↔ p a := by
  constructor
  · intro h'
    obtain ⟨b, hb⟩ := h'
    rwa [h b hb]
  · intro h'
    exact ⟨a, h'⟩

partial def fingImpEqProof (p : Expr) : MetaM <| Option Expr := do
  lambdaTelescope p fun xs body => do
    let #[x] := xs | return .none
    let ⟨_, _, x⟩ ← inferTypeQ x
    let ⟨u, _, body⟩ ← inferTypeQ body
    have : u =QL 0 := ⟨⟩
    withLocalDeclQ (u := 0) .anonymous .default body fun h => do
      let .some proof ← go x h | return .none
      let pf1 ← mkLambdaFVars #[x, h] proof
      let pf2 ← mkAppM ``exists_of_imp_eq #[pf1]
      let pf3 ← mkAppM ``propext #[pf2]
      return .some pf3
where
  go {u : Level} {α : Q(Sort u)} (x : Q($α)) {e : Q(Prop)} (h : Q($e)): MetaM <| Option Expr := do
    match e with
    | ~q(@Eq $α $a $b) =>
      if ← isDefEq x a then
        return .some q(Eq.symm $h)
      else if ← isDefEq x b then
        return .some h
      else
        return .none
    | ~q(And $a $b) =>
      match ← go x q(And.left $h) with
      | .some res => return .some res
      | .none =>
        match ← go x q(And.right $h) with
        | .some res => return .some res
        | .none => return .none
    | _ => return .none

simproc existsAndEq (Exists (fun _ => And _ _)) := fun e => do
  let_expr Exists _ p := e | return .continue
  let .some kek := ← fingImpEqProof p | return .continue
  let some (_, _, rhs) := (← inferType kek).eq? | return .continue
  return .visit {expr := rhs, proof? := kek}
