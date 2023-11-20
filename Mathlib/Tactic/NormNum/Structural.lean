/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core

/-!
# `norm_num` extension for inductive constructors
-/

set_option autoImplicit true

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

theorem prod_ne_1 {a₁ b₁ : α} {a₂ b₂ : β} (h : a₁ ≠ b₁) : (a₁, a₂) ≠ (b₁, b₂) | rfl => h rfl
theorem prod_ne_2 {a₁ b₁ : α} {a₂ b₂ : β} (h : a₂ ≠ b₂) : (a₁, a₂) ≠ (b₁, b₂) | rfl => h rfl

theorem cons_ne_1 {a₁ b₁ : α} {a₂ b₂ : List α} (h : a₁ ≠ b₁) :
    (a₁ :: a₂) ≠ (b₁ :: b₂) | rfl => h rfl
theorem cons_ne_2 {a₁ b₁ : α} {a₂ b₂ : List α} (h : a₂ ≠ b₂) :
    (a₁ :: a₂) ≠ (b₁ :: b₂) | rfl => h rfl

inductive MatchList {α : Q(Type u)} (a : Q(List $α)) where
  | nil (_ : $a =Q [])
  | cons (a₁ : Q($α)) (a₂ : Q(List $α)) (_ : $a =Q $a₁ :: $a₂)

def matchList {α : Q(Type u)} (a : Q(List $α)) : MetaM (MatchList a) := do
  match ← whnfR a with
  | .app (.const ``List.nil _) _ => return .nil ⟨⟩
  | .app (.app (.app (.const ``List.cons _) _) a₁) a₂ => return .cons a₁ a₂ ⟨⟩
  | _ => failure

/-- The `norm_num` extension which identifies expressions of the form `(a, b)`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_, _)] def evalProdMk : NormNumExt where eval {u α} e := do
  trace[Meta.debug] "norm_num prod.mk {e}"
  let .app (.app (.app (.app (.const ``Prod.mk [u₁, u₂])
      (α₁ : Q(Type u₁))) (α₂ : Q(Type u₂))) (a₁ : Q($α₁))) (a₂ : Q($α₂)) ← whnf e | failure
  have : u =QL max u₁ u₂ := ⟨⟩
  have : $α =Q ($α₁ × $α₂) := ⟨⟩
  have : $e =Q ($a₁, $a₂) := ⟨⟩
  let ⟨b₁, p₁⟩ := (← derive a₁).toRawEq
  let ⟨b₂, p₂⟩ := (← derive a₂).toRawEq
  return .other q(($b₁, $b₂)) q(congr (congrArg _ $p₁) $p₂)

/-- The `norm_num` extension which identifies expressions of the form `[]`. -/
@[norm_num []] def evalListNil : NormNumExt where eval {u α} e := do
  let e' : Q($α) ← whnf e
  have : $e =Q $e' := ⟨⟩
  return .other e' q(@rfl _ $e')

/-- The `norm_num` extension which identifies expressions of the form `(a, b)`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ :: _)] def evalListCons : NormNumExt where eval {u α} e := do
  let .app (.app (.app (.const ``List.cons _)
      (β : Q(Type u))) (a₁ : Q($β))) (a₂ : Q(List $β)) ← whnf e | failure
  have : $α =Q List $β := ⟨⟩
  have : $e =Q $a₁ :: $a₂ := ⟨⟩
  let ⟨b₁, p₁⟩ := (← derive a₁).toRawEq
  let ⟨b₂, p₂⟩ := (← derive (u := u) a₂).toRawEq
  return .other q(($b₁ :: $b₂)) q(congr (congrArg _ $p₁) $p₂)

/-- Evaluates an equality up to inductive constructors, using `norm_num` on the leaves. -/
partial def evalStructuralEq {α : Q(Type u)} (a b : Q($α)) : MetaM <| Q($a = $b) ⊕ Q($a ≠ $b) := do
  let α ← whnf α
  let .const f ls := α.getAppFn | failure
  match f with
  | ``Nat | ``Int | ``_root_.Rat =>
    match ← derive q($a = $b) with
    | .isTrue p => return .inl p
    | .isFalse p => return .inr p
    | _ => failure
  | ``Prod =>
    let [u₁, u₂] := ls | failure
    have : u =QL max u₁ u₂ := ⟨⟩
    have α₁ : Q(Type u₁) := α.getRevArg! 1
    have α₂ : Q(Type u₂) := α.getRevArg! 0
    have : $α =Q ($α₁ × $α₂) := ⟨⟩
    let .app (.app fa (a₁ : Q($α₁))) (a₂ : Q($α₂)) ← whnfR a | failure
    let .app (.app fb (b₁ : Q($α₁))) (b₂ : Q($α₂)) ← whnfR b | failure
    have : $a =Q ($a₁, $a₂) := ⟨⟩
    have : $b =Q ($b₁, $b₂) := ⟨⟩
    unless fa.isAppOfArity ``Prod.mk 2 && fb.isAppOfArity ``Prod.mk 2 do failure
    match ← evalStructuralEq a₁ b₁ with
    | .inr p₁ => return .inr q(prod_ne_1 $p₁)
    | .inl p₁ => match ← evalStructuralEq a₂ b₂ with
      | .inr p₂ => return .inr q(prod_ne_2 $p₂)
      | .inl p₂ => return .inl q(congr (congrArg _ $p₁) $p₂)
  | ``List =>
    have β : Q(Type u) := α.getRevArg! 0
    let rec evalList (a b : Q(List $β)) :
        MetaM <| Q($a ≠ $b) ⊕ MetaM (Q($a = $b) ⊕ Q($a ≠ $b)) := do
      match ← matchList a, ← matchList b with
      | .nil _, .nil  _ => pure <| .inr <| pure <| .inl q(rfl)
      | .cons .., .nil _ => pure <| .inl q(List.cons_ne_nil _ _)
      | .nil _, .cons .. => pure <| .inl q((List.cons_ne_nil _ _).symm)
      | .cons a₁ a₂ _, .cons b₁ b₂ _ =>
        match ← evalList a₂ b₂ with
        | .inl no => return .inl q(cons_ne_2 $no)
        | .inr p₂ => return .inr do
          match ← evalStructuralEq a₁ b₁ with
          | .inr p₁ => return .inr q(cons_ne_1 $p₁)
          | .inl p₁ => match ← p₂ with
            | .inr p₂ => return .inr q(cons_ne_2 $p₂)
            | .inl p₂ => return .inl q(congr (congrArg _ $p₁) $p₂)
    have : $α =Q List $β := ⟨⟩
    match ← evalList a b with
    | .inl no => return .inr no
    | .inr k => k
  | _ =>
    matchConstInduct α.getAppFn (fun _ => failure) fun v us => do
    let a ← whnfR a; let b ← whnfR b
    let .const fa _ := a.getAppFn | failure
    let .const fb _ := b.getAppFn | failure
    let some (.ctorInfo info) := (← getEnv).find? fa | failure
    unless fa == fb do
      let some (.ctorInfo _) := (← getEnv).find? fb | failure
      return .inr <| mkAppN (.const (.str v.name "noConfusion") (.zero :: us))
        (α.getAppArgs ++ #[(q(False) : Expr), a, b])
    let aArgs := a.getAppArgs; let bArgs := b.getAppArgs
    let mut args : Array ((u' : Level) × (α' : Q(Type u')) × Q($α') × Q($α')) := #[]
    for ai in aArgs[info.numParams:], bi in bArgs[info.numParams:] do
      let ⟨_, α', ai⟩ ← inferTypeQ' ai
      unless ← isDefEq α' (← inferType bi) do failure
      args := args.push ⟨_, _, ai, bi⟩
    let mut eq : Expr ← mkEqRefl <| mkAppN a.getAppFn a.getAppArgs[:info.numParams]
    for ⟨_, _, ai, bi⟩ in args, i in [0:args.size] do
      match ← evalStructuralEq ai bi with
      | .inl eq' => eq ← mkCongr eq eq'
      | .inr ne =>
        return .inr <| ← withLocalDeclD `h q($a = $b) fun h => do
          let e := mkAppN (.const (.str v.name "noConfusion") (.zero :: us))
            (α.getAppArgs ++ (#[q(False), a, b, h] : Array Expr))
          let .forallE _ dom _ _ ← whnf (← inferType e) | failure
          forallTelescopeReducing dom fun xs _ => do
            unless xs.size == args.size do failure
            mkLambdaFVars #[h] <| mkApp e <| ← mkLambdaFVars xs (.app ne xs[i]!)
    return .inl eq
