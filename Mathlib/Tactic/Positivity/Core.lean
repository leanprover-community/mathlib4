/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.HaveI
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Control.Basic
import Mathlib.Data.Nat.Cast.Basic
import Qq

/-!
## `positivity` core functionality

This file sets up the `positivity` tactic and the `@[positivity]` attribute,
which allow for plugging in new positivity functionality around a positivity-based driver.
The actual behavior is in `@[positivity]`-tagged definitions in `Tactic.Positivity.Basic`
and elsewhere.
-/

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `positivity` extensions. -/
syntax (name := positivity) "positivity " term,+ : attr

lemma ne_of_ne_of_eq' {α : Sort*} {a c b : α} (hab : (a : α) ≠ c) (hbc : a = b) : b ≠ c := hbc ▸ hab

namespace Mathlib.Meta.Positivity

variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))

/-- The result of `positivity` running on an expression `e` of type `α`. -/
inductive Strictness (e : Q($α)) where
  | positive (pf : Q(0 < $e))
  | nonnegative (pf : Q(0 ≤ $e))
  | nonzero (pf : Q($e ≠ 0))
  | none
  deriving Repr

/-- Gives a generic description of the `positivity` result. -/
def Strictness.toString {e : Q($α)} : Strictness zα pα e → String
  | positive _ => "positive"
  | nonnegative _ => "nonnegative"
  | nonzero _ => "nonzero"
  | none => "none"

/-- Extract a proof that `e` is positive, if possible, from `Strictness` information about `e`. -/
def Strictness.toPositive {e} : Strictness zα pα e → Option Q(0 < $e)
  | .positive pf => some pf
  | _ => .none

/-- Extract a proof that `e` is nonnegative, if possible, from `Strictness` information about `e`.
-/
def Strictness.toNonneg {e} : Strictness zα pα e → Option Q(0 ≤ $e)
  | .positive pf => some q(le_of_lt $pf)
  | .nonnegative pf => some pf
  | _ => .none

/-- Extract a proof that `e` is nonzero, if possible, from `Strictness` information about `e`. -/
def Strictness.toNonzero {e} : Strictness zα pα e → Option Q($e ≠ 0)
  | .positive pf => some q(ne_of_gt $pf)
  | .nonzero pf => some pf
  | _ => .none

/-- An extension for `positivity`. -/
structure PositivityExt where
  /-- Attempts to prove an expression `e : α` is `>0`, `≥0`, or `≠0`. -/
  eval {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α)) (e : Q($α)) :
    MetaM (Strictness zα pα e)

/-- Read a `positivity` extension from a declaration of the right type. -/
def mkPositivityExt (n : Name) : ImportM PositivityExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck PositivityExt opts ``PositivityExt n

/-- Each `positivity` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `positivity` declarations -/
initialize positivityExt : PersistentEnvExtension Entry (Entry × PositivityExt)
    (List Entry × DiscrTree PositivityExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq PositivityExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkPositivityExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `positivity
  descr := "adds a positivity extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| positivity $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'positivity', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'positivity', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkPositivityExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| positivityExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

variable {A : Type*} {e : A}

lemma pos_of_isNat {n : ℕ} [Semiring A] [PartialOrder A] [IsOrderedRing A] [Nontrivial A]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos.2
  simpa using w

lemma pos_of_isNat' {n : ℕ}
    [AddMonoidWithOne A] [PartialOrder A] [AddLeftMono A] [ZeroLEOneClass A] [h'' : NeZero (1 : A)]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos'.2
  simpa using w

lemma nonneg_of_isNat {n : ℕ} [Semiring A] [PartialOrder A] [IsOrderedRing A]
    (h : NormNum.IsNat e n) : 0 ≤ (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg n

lemma nonneg_of_isNat' {n : ℕ}
    [AddMonoidWithOne A] [PartialOrder A] [AddLeftMono A] [ZeroLEOneClass A]
    (h : NormNum.IsNat e n) : 0 ≤ (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg' n

lemma nz_of_isNegNat {n : ℕ} [Ring A] [PartialOrder A] [IsStrictOrderedRing A]
    (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.ble 1 n = true) : (e : A) ≠ 0 := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  simp only [ne_eq, neg_eq_zero]
  apply ne_of_gt
  simpa using w

lemma pos_of_isNNRat {n d : ℕ} [Semiring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsNNRat e n d) → (decide (0 < n)) → ((0 : A) < (e : A))
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟ (d : A)) := pos_invOf_of_invertible_cast d
    have pos_n : (0 < (n : A)) := Nat.cast_pos (n := n) |>.2 (of_decide_eq_true h)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

lemma pos_of_isRat {n : ℤ} {d : ℕ} [Ring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsRat e n d) → (decide (0 < n)) → ((0 : A) < (e : A))
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟(d : A)) := pos_invOf_of_invertible_cast d
    have pos_n : (0 < (n : A)) := Int.cast_pos (n := n) |>.2 (of_decide_eq_true h)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

lemma nonneg_of_isNNRat {n d : ℕ} [Semiring A] [LinearOrder A] :
    (NormNum.IsNNRat e n d) → (decide (n = 0)) → (0 ≤ (e : A))
  | ⟨inv, eq⟩, h => by rw [eq, of_decide_eq_true h]; simp

lemma nonneg_of_isRat {n : ℤ} {d : ℕ} [Ring A] [LinearOrder A] :
    (NormNum.IsRat e n d) → (decide (n = 0)) → (0 ≤ (e : A))
  | ⟨inv, eq⟩, h => by rw [eq, of_decide_eq_true h]; simp

lemma nz_of_isRat {n : ℤ} {d : ℕ} [Ring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsRat e n d) → (decide (n < 0)) → ((e : A) ≠ 0)
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟(d : A)) := pos_invOf_of_invertible_cast d
    have neg_n : ((n : A) < 0) := Int.cast_lt_zero (n := n) |>.2 (of_decide_eq_true h)
    have neg := mul_neg_of_neg_of_pos neg_n pos_invOf_d
    rw [eq]
    exact ne_iff_lt_or_gt.2 (Or.inl neg)

variable {zα pα} in
/-- Converts a `MetaM Strictness` which can fail
into one that never fails and returns `.none` instead. -/
def catchNone {e : Q($α)} (t : MetaM (Strictness zα pα e)) : MetaM (Strictness zα pα e) :=
  try t catch e =>
    trace[Tactic.positivity.failure] "{e.toMessageData}"
    pure .none

variable {zα pα} in
/-- Converts a `MetaM Strictness` which can return `.none`
into one which never returns `.none` but fails instead. -/
def throwNone {m : Type → Type*} {e : Q($α)} [Monad m] [Alternative m]
    (t : m (Strictness zα pα e)) : m (Strictness zα pα e) := do
  match ← t with
  | .none => failure
  | r => pure r

/-- Attempts to prove a `Strictness` result when `e` evaluates to a literal number. -/
def normNumPositivity (e : Q($α)) : MetaM (Strictness zα pα e) := catchNone do
  match ← NormNum.derive e with
  | .isBool .. => failure
  | .isNat _ lit p =>
    if 0 < lit.natLit! then
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
      -- difference, as synthesising the `try` classes is a bit faster.
      try
        let _a ← synthInstanceQ q(Semiring $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(IsOrderedRing $α)
        let _a ← synthInstanceQ q(Nontrivial $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        haveI' p' : Nat.ble 1 $lit =Q true := ⟨⟩
        pure (.positive q(pos_of_isNat (A := $α) $p $p'))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let _a ← synthInstanceQ q(AddMonoidWithOne $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(AddLeftMono $α)
        let _a ← synthInstanceQ q(ZeroLEOneClass $α)
        let _a ← synthInstanceQ q(NeZero (1 : $α))
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        haveI' p' : Nat.ble 1 $lit =Q true := ⟨⟩
        pure (.positive q(pos_of_isNat' (A := $α) $p $p'))
    else
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
      -- difference, as synthesising the `try` classes is a bit faster.
      try
        let _a ← synthInstanceQ q(Semiring $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(IsOrderedRing $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        pure (.nonnegative q(nonneg_of_isNat $p))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let _a ← synthInstanceQ q(AddMonoidWithOne $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(AddLeftMono $α)
        let _a ← synthInstanceQ q(ZeroLEOneClass $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        pure (.nonnegative q(nonneg_of_isNat' $p))
  | .isNegNat _ lit p =>
    let _a ← synthInstanceQ q(Ring $α)
    let _a ← synthInstanceQ q(PartialOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsInt $e (Int.negOfNat $lit)) := p
    haveI' p' : Nat.ble 1 $lit =Q true := ⟨⟩
    pure (.nonzero q(nz_of_isNegNat $p $p'))
  | .isNNRat _i q n d p =>
    let _a ← synthInstanceQ q(Semiring $α)
    let _a ← synthInstanceQ q(LinearOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsNNRat $e $n $d) := p
    if 0 < q then
      haveI' w : decide (0 < $n) =Q true := ⟨⟩
      pure (.positive q(pos_of_isNNRat $p $w))
    else -- should not be reachable, but just in case
      haveI' w : decide ($n = 0) =Q true := ⟨⟩
      pure (.nonnegative q(nonneg_of_isNNRat $p $w))
  | .isNegNNRat _i q n d p =>
    let _a ← synthInstanceQ q(Ring $α)
    let _a ← synthInstanceQ q(LinearOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsRat $e (.negOfNat $n) $d) := p
    if q < 0 then
      haveI' w : decide (Int.negOfNat $n < 0) =Q true := ⟨⟩
      pure (.nonzero q(nz_of_isRat $p $w))
    else -- should not be reachable, but just in case
      haveI' w : decide (Int.negOfNat $n = 0) =Q true := ⟨⟩
      pure (.nonnegative q(nonneg_of_isRat $p $w))

/-- Attempts to prove that `e ≥ 0` using `zero_le` in a `CanonicallyOrderedAdd` monoid. -/
def positivityCanon (e : Q($α)) : MetaM (Strictness zα pα e) := do
  let _add ← synthInstanceQ q(AddMonoid $α)
  let _le ← synthInstanceQ q(PartialOrder $α)
  let _i ← synthInstanceQ q(CanonicallyOrderedAdd $α)
  assumeInstancesCommute
  pure (.nonnegative q(zero_le $e))

/-- A variation on `assumption` when the hypothesis is `lo ≤ e` where `lo` is a numeral. -/
def compareHypLE (lo e : Q($α)) (p₂ : Q($lo ≤ $e)) : MetaM (Strictness zα pα e) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_le $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_trans $p₁ $p₂))
  | _ => pure .none

/-- A variation on `assumption` when the hypothesis is `lo < e` where `lo` is a numeral. -/
def compareHypLT (lo e : Q($α)) (p₂ : Q($lo < $e)) : MetaM (Strictness zα pα e) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_trans $p₁ $p₂))
  | .nonnegative p₁ => pure (.positive q(lt_of_le_of_lt $p₁ $p₂))
  | _ => pure .none

/-- A variation on `assumption` when the hypothesis is `x = e` where `x` is a numeral. -/
def compareHypEq (e x : Q($α)) (p₂ : Q($x = $e)) : MetaM (Strictness zα pα e) := do
  match ← normNumPositivity zα pα x with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_eq $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_of_le_of_eq $p₁ $p₂))
  | .nonzero p₁ => pure (.nonzero q(ne_of_ne_of_eq' $p₁ $p₂))
  | .none => pure .none

initialize registerTraceClass `Tactic.positivity
initialize registerTraceClass `Tactic.positivity.failure

/-- A variation on `assumption` which checks if the hypothesis `ldecl` is `a [</≤/=] e`
where `a` is a numeral. -/
def compareHyp (e : Q($α)) (ldecl : LocalDecl) : MetaM (Strictness zα pα e) := do
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@LE.le.{u} $β $_le $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with
    | ~q(0) =>
      assertInstancesCommute
      return .nonnegative q($p)
    | _ => compareHypLE zα pα lo e p
  | ~q(@LT.lt.{u} $β $_lt $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with
    | ~q(0) =>
      assertInstancesCommute
      return .positive q($p)
    | _ => compareHypLT zα pα lo e p
  | ~q(@Eq.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match ← isDefEqQ e rhs with
    | .defEq _ =>
      match lhs with
      | ~q(0) => pure <| .nonnegative q(le_of_eq $p)
      | _ => compareHypEq zα pα e lhs q($p)
    | .notDefEq =>
      let .defEq _ ← isDefEqQ e lhs | pure .none
      match rhs with
      | ~q(0) => pure <| .nonnegative q(ge_of_eq $p)
      | _ => compareHypEq zα pα e rhs q(Eq.symm $p)
  | ~q(@Ne.{u + 1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match lhs, rhs with
    | ~q(0), _ =>
      let .defEq _ ← isDefEqQ e rhs | pure .none
      pure <| .nonzero q(Ne.symm $p)
    | _, ~q(0) =>
      let .defEq _ ← isDefEqQ e lhs | pure .none
      pure <| .nonzero q($p)
    | _, _ => pure .none
  | _ => pure .none

variable {zα pα} in
/-- The main combinator which combines multiple `positivity` results.
It assumes `t₁` has already been run for a result, and runs `t₂` and takes the best result.
It will skip `t₂` if `t₁` is already a proof of `.positive`, and can also combine
`.nonnegative` and `.nonzero` to produce a `.positive` result. -/
def orElse {e : Q($α)} (t₁ : Strictness zα pα e) (t₂ : MetaM (Strictness zα pα e)) :
    MetaM (Strictness zα pα e) := do
  match t₁ with
  | .none => catchNone t₂
  | p@(.positive _) => pure p
  | .nonnegative p₁ =>
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonzero p₂ => pure (.positive q(lt_of_le_of_ne' $p₁ $p₂))
    | _ => pure (.nonnegative p₁)
  | .nonzero p₁ =>
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonnegative p₂ => pure (.positive q(lt_of_le_of_ne' $p₂ $p₁))
    | _ => pure (.nonzero p₁)

/-- Run each registered `positivity` extension on an expression, returning a `NormNum.Result`. -/
def core (e : Q($α)) : MetaM (Strictness zα pα e) := do
  let mut result := .none
  trace[Tactic.positivity] "trying to prove positivity of {e}"
  for ext in ← (positivityExt.getState (← getEnv)).2.getMatch e do
    try
      result ← orElse result <| ext.eval zα pα e
    catch err =>
      trace[Tactic.positivity] "{e} failed: {err.toMessageData}"
  result ← orElse result <| normNumPositivity zα pα e
  result ← orElse result <| positivityCanon zα pα e
  if let .positive _ := result then
    trace[Tactic.positivity] "{e} => {result.toString}"
    return result
  for ldecl in ← getLCtx do
    if !ldecl.isImplementationDetail then
      result ← orElse result <| compareHyp zα pα e ldecl
  trace[Tactic.positivity] "{e} => {result.toString}"
  throwNone (pure result)

private inductive OrderRel : Type
| le : OrderRel -- `0 ≤ a`
| lt : OrderRel -- `0 < a`
| ne : OrderRel -- `a ≠ 0`
| ne' : OrderRel -- `0 ≠ a`

end Meta.Positivity
namespace Meta.Positivity

/-- Given an expression `e`, use the core method of the `positivity` tactic to prove it positive,
or, failing that, nonnegative; return a Boolean (signalling whether the strict or non-strict
inequality was established) together with the proof as an expression. -/
def bestResult (e : Expr) : MetaM (Bool × Expr) := do
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let zα ← synthInstanceQ q(Zero $α)
  let pα ← synthInstanceQ q(PartialOrder $α)
  match ← try? (Meta.Positivity.core zα pα e) with
  | some (.positive pf) => pure (true, pf)
  | some (.nonnegative pf) => pure (false, pf)
  | _ => throwError "could not establish the nonnegativity of {e}"

/-- Given an expression `e`, use the core method of the `positivity` tactic to prove it nonnegative.
-/
def proveNonneg (e : Expr) : MetaM Expr := do
  let (strict, pf) ← bestResult e
  if strict then mkAppM ``le_of_lt #[pf] else pure pf

/-- An auxiliary entry point to the `positivity` tactic. Given a proposition `t` of the form
`0 [≤/</≠] e`, attempts to recurse on the structure of `t` to prove it. It returns a proof
or fails. -/
def solve (t : Q(Prop)) : MetaM Expr := do
  let rest {u : Level} (α : Q(Type u)) z e (relDesired : OrderRel) : MetaM Expr := do
    let zα ← synthInstanceQ q(Zero $α)
    assumeInstancesCommute
    let .true ← isDefEq z q(0 : $α) | throwError "not a positivity goal"
    let pα ← synthInstanceQ q(PartialOrder $α)
    assumeInstancesCommute
    let r ← catchNone <| Meta.Positivity.core zα pα e
    let throw (a b : String) : MetaM Expr := throwError
      "failed to prove {a}, but it would be possible to prove {b} if desired"
    let p ← show MetaM Expr from match relDesired, r with
    | .lt, .positive p
    | .le, .nonnegative p
    | .ne, .nonzero p => pure p
    | .le, .positive p => pure q(le_of_lt $p)
    | .ne, .positive p => pure q(ne_of_gt $p)
    | .ne', .positive p => pure q(ne_of_lt $p)
    | .ne', .nonzero p => pure q(Ne.symm $p)
    | .lt, .nonnegative _ => throw "strict positivity" "nonnegativity"
    | .lt, .nonzero _ => throw "strict positivity" "nonzeroness"
    | .le, .nonzero _ => throw "nonnegativity" "nonzeroness"
    | .ne, .nonnegative _
    | .ne', .nonnegative _ => throw "nonzeroness" "nonnegativity"
    | _, .none => throwError "failed to prove positivity/nonnegativity/nonzeroness"
    pure p
  match t with
  | ~q(@LE.le $α $_a $z $e) => rest α z e .le
  | ~q(@LT.lt $α $_a $z $e) => rest α z e .lt
  | ~q($a ≠ ($b : ($α : Type _))) =>
    let _zα ← synthInstanceQ q(Zero $α)
    if ← isDefEq b q((0 : $α)) then
      rest α b a .ne
    else
      let .true ← isDefEq a q((0 : $α)) | throwError "not a positivity goal"
      rest α a b .ne'
  | _ => throwError "not a positivity goal"

/-- The main entry point to the `positivity` tactic. Given a goal `goal` of the form `0 [≤/</≠] e`,
attempts to recurse on the structure of `e` to prove the goal.
It will either close `goal` or fail. -/
def positivity (goal : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← withReducible goal.getType'
  let p ← solve t
  goal.assign p

end Meta.Positivity

namespace Tactic.Positivity

open Tactic

/-- Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
according to the syntax of the expression `x`, if the atoms composing the expression all have
numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
either closes the goal or fails.

`positivity [t₁, …, tₙ]` first executes `have := t₁; …; have := tₙ` in the current goal,
then runs `positivity`. This is useful when `positivity` needs derived premises such as `0 < y`
for division/reciprocal, or `0 ≤ x` for real powers.

Examples:
```
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example {a b c d : ℝ} (hab : 0 < a * b) (hb : 0 ≤ b) (hcd : c < d) :
    0 < a ^ c + 1 / (d - c) := by
  positivity [sub_pos_of_lt hcd, pos_of_mul_pos_left hab hb]
```
-/
syntax (name := positivity) "positivity" (" [" term,* "]")? : tactic

elab_rules : tactic
| `(tactic| positivity) => liftMetaTactic fun g => do Meta.Positivity.positivity g; pure []

macro_rules
| `(tactic| positivity [$h,*]) => `(tactic| · ($[have := $h];*); positivity)

end Positivity

end Mathlib.Tactic

/-!
We set up `positivity` as a first-pass discharger for `gcongr` side goals.
-/

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-!
We register `positivity` with the `hint` tactic.
-/

register_hint positivity
