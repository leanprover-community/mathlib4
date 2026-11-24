/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
module

public meta import Mathlib.Control.Basic
public import Mathlib.Algebra.Order.Invertible
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Tactic.HaveI
public import Mathlib.Tactic.NormNum.Core

/-!
## `positivity` core functionality

This file sets up the `positivity` tactic and the `@[positivity]` attribute,
which allow for plugging in new positivity functionality around a positivity-based driver.
The actual behavior is in `@[positivity]`-tagged definitions in `Tactic.Positivity.Basic`
and elsewhere.
-/

public meta section

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- A definition of type `PositivityExt` tagged `@[positivity t]` extends the `positivity` tactic.
The term (with underscores) `t` indicates which expressions this extension accepts.
An extension will be given an expression `e : α`, together with hypotheses
`[Zero α] [PartialOrder α]` and attempts to prove `e > 0`, `e ≥ 0`, or `e ≠ 0`.

When `Positivity.core` calls this extension on an expression `e`, it does not guarantee that `e`
matches `t` perfectly: validate the form of the expression (using e.g.
`match_expr (← withReducible (whnf e))`) before building a proof. See also the
`let .app ... ← withReducible (whnf e) | throwError ...` lines in the example below.

An extension can call `Mathlib.Meta.Positivity.core` to recursively solve subgoals.
`core` fails if it cannot prove anything about the subexpression; wrap the call in `catchNone` to
get `Strictness.none` instead.

Extensions run in `PositivityM`, which is `MetaM` together with a cache of the results of earlier
`core` calls. `MetaM` code can be used in an extension without change. An extension may fail
freely: this does not discard the cache.

Example:
```lean
@[positivity ite _ _ _] def evalIte : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (.app (.app f (p : Q(Prop))) (_ : Q(Decidable $p))) (a : Q($α))) (b : Q($α))
    ← withReducible (whnf e) | throwError "not ite"
  haveI' : $e =Q ite $p $a $b := ⟨⟩
  guard <| ← withNewMCtxDepth <| isDefEq f q(ite (α := $α))
  let ra ← core zα pα a; let rb ← core zα pα b
  ...
```
-/
syntax (name := positivity) "positivity " term,+ : attr

lemma ne_of_ne_of_eq' {α : Sort*} {a c b : α} (hab : (a : α) ≠ c) (hbc : a = b) : b ≠ c := hbc ▸ hab

namespace Mathlib.Meta.Positivity

variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))

/-- The result of `positivity` running on an expression `e` of type `α`. -/
inductive Strictness (e : Q($α)) : Option Q(PartialOrder $α) → Type where
  | positive {pα : Q(PartialOrder $α)} (pf : Q(0 < $e)) : Strictness e pα
  | nonnegative {pα : Q(PartialOrder $α)} (pf : Q(0 ≤ $e)) : Strictness e pα
  | nonzero {pα?} (pf : Q($e ≠ 0)) : Strictness e pα?
  | none {pα?} : Strictness e pα?

/-- Gives a generic description of the `positivity` result. -/
def Strictness.toString {e pα?} : Strictness zα e pα? → String
  | positive _ => "positive"
  | nonnegative _ => "nonnegative"
  | nonzero _ => "nonzero"
  | none => "none"

/-- Extract a proof that `e` is positive, if possible, from `Strictness` information about `e`. -/
def Strictness.toPositive {e pα} : Strictness zα e (some pα) → Option Q(0 < $e)
  | .positive pf => some pf
  | _ => .none

/-- Extract a proof that `e` is nonnegative, if possible, from `Strictness` information about `e`.
-/
def Strictness.toNonneg {e pα} : Strictness zα e (some pα) → Option Q(0 ≤ $e)
  | .positive pf => some q(le_of_lt $pf)
  | .nonnegative pf => some pf
  | _ => .none

/-- Extract a proof that `e` is nonzero, if possible, from `Strictness` information about `e`. -/
def Strictness.toNonzero {e pα?} : Strictness zα e pα? → Option Q($e ≠ 0)
  | .positive pf => some q(ne_of_gt $pf)
  | .nonzero pf => some pf
  | _ => .none

/-- A `Strictness` result with its type information erased, as stored in the `positivity` cache. -/
inductive CachedResult where
  | positive (pf : Expr)
  | nonnegative (pf : Expr)
  | nonzero (pf : Expr)
  /-- `positivity` failed, so it should not be tried again. -/
  | none

variable {zα} in
/-- Erase the type information of a `Strictness` result, to store it in the cache. -/
def Strictness.toCached {e pα?} : Strictness zα e pα? → CachedResult
  | .positive pf => .positive pf
  | .nonnegative pf => .nonnegative pf
  | .nonzero pf => .nonzero pf
  | .none => .none

/-- Recover a `Strictness` result from the cache. This is only meaningful for an entry that was
stored for the same expression `e` and the same kind of `pα?`. -/
def CachedResult.toStrictness (pα? : Option Q(PartialOrder $α)) (e : Q($α)) (r : CachedResult) :
    Strictness zα e pα? :=
  match pα?, r with
  | _, .nonzero pf => .nonzero pf
  | .some _, .positive pf => .positive pf
  | .some _, .nonnegative pf => .nonnegative pf
  | _, _ => .none

/-- The state of the `positivity` tactic. -/
structure State where
  /-- The results of earlier `Positivity.core` calls, including failures.

  The key is the expression together with whether `core` was given a `PartialOrder` instance.
  Without one, `core` can only prove `e ≠ 0`, and it does not use hypotheses such as `0 < e`. So a
  result found without an order must not be reused when there is one, nor the other way around,
  even for the same expression: `evalNatCast` runs `core` without an order on terms of type `ℕ`. -/
  cache : Std.HashMap (Expr × Bool) CachedResult := {}

/-- The monad in which `positivity` and its extensions run: `MetaM` together with a cache of the
results of `Positivity.core`.

The state is a `StateRefT` rather than a `StateT`, so that entries added before an exception is
thrown are still there after it is caught. Extensions throw to signal that they do not apply, so
a `StateT` would lose most of the cache.

The cache does not record the local context. An extension that calls `core` in an extended local
context may add new variables (as the extensions for `∑` and `∫` do), but it must not add
hypotheses that `core` could use, such as `0 < x`: a result found before the hypothesis was added
would be reused, and a proof using the hypothesis could be reused outside its scope. -/
abbrev PositivityM := StateRefT State MetaM

section AssertInstancesCommute
open Qq.Impl

/-- A variant of the implementation of `assertInstancesCommute` in `Qq` which works in any monad
that `MetaM` lifts to, and not only in `MetaM`. The only difference is the `monadLift`. -/
syntax "assertInstancesCommuteLiftImpl" term : term

elab_rules : term <= expectedType | `(assertInstancesCommuteLiftImpl $cont) => do
  match ← findRedundantLocalInstQuoted? with
  | some ⟨fvar, _, _, lhs, rhs⟩ =>
    let n ← mkFreshUserName ((← fvar.getUserName).eraseMacroScopes.appendAfter "_eq")
    let cmd := q(withNewMCtxDepth do withDefault do assertDefEqQ $lhs $rhs)
    elabTerm (← `(monadLift (m := MetaM) $(← exprToSyntax cmd) >>=
        fun __defeqres =>
          have $(mkIdent n) := __defeqres.1
          assertInstancesCommuteLiftImpl $cont))
      expectedType
  | none => elabTerm cont expectedType

/-- `assertInstancesCommute` expands to a bind in `MetaM`, so by itself it cannot be used in a
`do` block in `PositivityM`. While `Mathlib.Meta.Positivity` is open, we expand it to the lifted
variant above instead, so that `positivity` extensions can keep using it.

TODO: make this change in `Qq` (it is one `monadLift`) and remove this override. -/
scoped macro_rules
  | `(assert! assertInstancesCommuteDummy; $cont) => `(assertInstancesCommuteLiftImpl $cont)

end AssertInstancesCommute

/-- An extension for `positivity`. -/
structure PositivityExt where
  /-- Attempts to prove an expression `e : α` is `>0`, `≥0`, or `≠0`. -/
  eval {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα? : Option Q(PartialOrder $α)) (e : Q($α)) :
    PositivityM (Strictness zα e pα?)

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
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertKeyValue ks v) dt
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
      ensureAttrDeclIsMeta `positivity declName kind
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
      -- TODO: track what `[positivity]` decls are actually used at use sites
      recordExtraRevUseOfCurrentModule
    | _ => throwUnsupportedSyntax
}

variable {A : Type*} {e : A}

lemma pos_of_isNat {n : ℕ} [Semiring A] [PartialOrder A] [IsOrderedRing A] [Nontrivial A]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos.2
  simpa using! w

lemma pos_of_isNat' {n : ℕ}
    [AddMonoidWithOne A] [PartialOrder A] [AddLeftMono A] [ZeroLEOneClass A] [h'' : NeZero (1 : A)]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos'.2
  simpa using! w

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
  simpa using! w

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

variable {zα} in
/-- Converts a computation of a `Strictness` which can fail
into one that never fails and returns `.none` instead.
This works in `MetaM` and in `PositivityM`. -/
def catchNone {m : Type → Type} [Monad m] [MonadExceptOf Exception m] [MonadLiftT MetaM m]
    {e pα?} (t : m (Strictness zα e pα?)) : m (Strictness zα e pα?) :=
  tryCatch t fun e => do
    liftM (m := MetaM) (do trace[Tactic.positivity.failure] "{e.toMessageData}")
    pure .none

variable {zα} in
/-- Converts a computation of a `Strictness` which can return `.none`
into one which never returns `.none` but fails instead.
This works in `MetaM` and in `PositivityM`. -/
def throwNone {m : Type → Type} [Monad m] [MonadError m]
    {e pα?} (t : m (Strictness zα e pα?)) : m (Strictness zα e pα?) := do
  match ← t with
  | .none => throwError "Strictness result was `{.ofConstName ``Strictness.none}`."
  | r => pure r

/-- Attempts to prove a `Strictness` result when `e` evaluates to a literal number. -/
def normNumPositivity (pα : Q(PartialOrder $α)) (e : Q($α))
    : MetaM (Strictness zα e (some pα)) := catchNone do
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
def positivityCanon (pα : Q(PartialOrder $α)) (e : Q($α)) : MetaM (Strictness zα e (some pα)) := do
  let _add ← synthInstanceQ q(AddMonoid $α)
  let _le ← synthInstanceQ q(PartialOrder $α)
  let _i ← synthInstanceQ q(CanonicallyOrderedAdd $α)
  assumeInstancesCommute
  pure (.nonnegative q(zero_le (a := $e)))

/-- A variation on `assumption` when the hypothesis is `lo ≤ e` where `lo` is a numeral. -/
def compareHypLE (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo ≤ $e))
    : MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_le $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_trans $p₁ $p₂))
  | _ => pure .none

/-- A variation on `assumption` when the hypothesis is `lo < e` where `lo` is a numeral. -/
def compareHypLT (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo < $e)) :
    MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_trans $p₁ $p₂))
  | .nonnegative p₁ => pure (.positive q(lt_of_le_of_lt $p₁ $p₂))
  | _ => pure .none

/-- A variation on `assumption` when the hypothesis is `x = e` where `x` is a numeral. -/
def compareHypEq (pα : Q(PartialOrder $α)) (e x : Q($α)) (p₂ : Q($x = $e)) :
    MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα x with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_eq $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_of_le_of_eq $p₁ $p₂))
  | .nonzero p₁ => pure (.nonzero q(ne_of_ne_of_eq' $p₁ $p₂))
  | .none => pure .none

initialize registerTraceClass `Tactic.positivity
initialize registerTraceClass `Tactic.positivity.failure
initialize registerTraceClass `Tactic.positivity.cache (inherited := true)

/-- A variation on `assumption` which checks if the hypothesis `ldecl` is `a [</≤/=] e`
where `a` is a numeral. -/
def compareHyp (pα : Q(PartialOrder $α)) (e : Q($α)) (ldecl : LocalDecl) :
    MetaM (Strictness zα e pα) := do
  unless ← isProp ldecl.type do return .none
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
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
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

/-- A variation on `assumption` when the hypothesis is `e ≠ 0` or `0 ≠ e`. -/
def compareHypNonzero {pα?} (e : Q($α)) (ldecl : LocalDecl) : MetaM (Strictness zα e pα?) := do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
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

variable {zα} in
/-- The main combinator which combines multiple `positivity` results.
It assumes `t₁` has already been run for a result, and runs `t₂` and takes the best result.
It will skip `t₂` if `t₁` is already a proof of `.positive`, and can also combine
`.nonnegative` and `.nonzero` to produce a `.positive` result. -/
def orElse {pα?} {e : Q($α)} (t₁ : Strictness zα e pα?) (t₂ : PositivityM (Strictness zα e pα?)) :
    PositivityM (Strictness zα e pα?) :=
  match t₁ with
  | .none => catchNone t₂
  | p@(.positive _) => pure p
  | .nonnegative p₁ => do
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonzero p₂ => pure (.positive q(lt_of_le_of_ne' $p₁ $p₂))
    | _ => pure (.nonnegative p₁)
  | .nonzero p₁ => do
    match (dependent := true) ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonnegative p₂ => pure (.positive q(lt_of_le_of_ne' $p₂ $p₁))
    | _ => pure (.nonzero p₁)

/-- Run each registered `positivity` extension on an expression, without consulting or updating the
cache, and return the best `Strictness` result found. This returns `.none` if nothing can be
proved. Extensions should call `Positivity.core` instead. -/
def coreUncached (pα? : Option Q(PartialOrder $α)) (e : Q($α)) :
    PositivityM (Strictness zα e pα?) :=
  withReducible do
  let mut result := .none
  trace[Tactic.positivity] "trying to prove positivity of {e}"
  for ext in ← (positivityExt.getState (← getEnv)).2.getMatch e do
    try
      result ← orElse result <| ext.eval zα pα? e
    catch err =>
      trace[Tactic.positivity] "{e} failed: {err.toMessageData}"
  trace[Tactic.positivity] "current result from positivity extensions: {result.toString}"
  match h : pα?, result with
  | some pα, res =>
    trace[Tactic.positivity] "{α} has some {pα}"
    let mut res ← orElse res <| normNumPositivity zα pα e
    trace[Tactic.positivity] "current result from normNum: {res.toString}"
    res ← orElse res <| positivityCanon zα pα e
    trace[Tactic.positivity] "current result from canonicity: {res.toString}"
    if let .positive _ := res then
      trace[Tactic.positivity] "{e} => {res.toString}"
      return h ▸ res
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        res ← orElse res <| compareHyp zα pα e ldecl
    trace[Tactic.positivity] "{e} => {res.toString}"
    return h ▸ res
  | .none, _ =>
    trace[Tactic.positivity] "{α} has no PartialOrder"
    if let .nonzero _ := result then
      trace[Tactic.positivity] "{e} => {result.toString}"
      return result
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        result ← orElse result <| compareHypNonzero zα e ldecl
    trace[Tactic.positivity] "{e} => {result.toString}"
    return result

/-- Run each registered `positivity` extension on an expression `e`, and return the best
`Strictness` result found. Results, including failures, are cached, so each expression is
analysed only once per `positivity` call.

This fails if nothing can be proved about `e`: it never returns `.none`.
Use `catchNone` to get `.none` instead of a failure. -/
def core (pα? : Option Q(PartialOrder $α)) (e : Q($α)) : PositivityM (Strictness zα e pα?) := do
  let key : Expr × Bool := (e, pα?.isSome)
  let r ← do
    if let some r := (← get).cache[key]? then
      let r := r.toStrictness zα pα? e
      trace[Tactic.positivity.cache] "cached: {e} => {r.toString}"
      pure r
    else
      let r ← coreUncached zα pα? e
      modify fun s => { s with cache := s.cache.insert key r.toCached }
      pure r
  throwNone (pure r)

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
def bestResult (e : Expr) : PositivityM (Bool × Expr) := do
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let zα ← synthInstanceQ q(Zero $α)
  let pα? ← try? <| synthInstanceQ q(PartialOrder $α)
  assumeInstancesCommute
  match pα?, ← try? (Meta.Positivity.core zα pα? e) with
  | _, some (.positive pf) => pure (true, pf)
  | _, some (.nonnegative pf) => pure (false, pf)
  | _, _ => throwError "could not establish the nonnegativity of {e}"

/-- Given an expression `e`, use the core method of the `positivity` tactic to prove it nonnegative.
-/
def proveNonneg (e : Expr) : PositivityM Expr := do
  let (strict, pf) ← bestResult e
  if strict then mkAppM ``le_of_lt #[pf] else pure pf

/-- An auxiliary entry point to the `positivity` tactic. Given a proposition `t` of the form
`0 [≤/</≠] e`, attempts to recurse on the structure of `t` to prove it. It returns a proof
or fails. -/
def solve (t : Q(Prop)) : MetaM Expr := do
  let rest {u : Level} (α : Q(Type u)) z e (relDesired : OrderRel) : MetaM Expr := do
    let zα ← synthInstanceQ q(Zero $α)
    let .true ← isDefEq z q(0 : $α) | throwError "not a positivity goal"
    let pα? ← try? <| synthInstanceQ q(PartialOrder $α)
    let r ← (catchNone <| Meta.Positivity.core zα pα? e).run' {}
    let throw (a b : String) : MetaM Expr := throwError
      "failed to prove {a}, but it would be possible to prove {b} if desired"
    match (dependent := true) pα? with
    | some _ =>
      match relDesired, r with
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
    | none =>
      match relDesired, r with
      | .ne, .nonzero p => pure p
      | .ne', .nonzero p => pure q(Ne.symm $p)
      | .lt, .nonzero _ => throw "strict positivity" "nonzeroness"
      | .le, .nonzero _ => throw "nonnegativity" "nonzeroness"
      | _, _ => throwError "failed to prove nonzeroness"
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

/-- `positivity` solves goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`. The tactic works recursively
according to the syntax of the expression `x`, by attempting to prove subexpressions are
positive/nonnegative/nonzero and combining this into a final proof. This tactic either closes the
goal or fails.

For each subexpression `e`, `positivity` will try to:
* try `@[positivity]`-tagged extensions to recursively prove `e` is positive/nonnegative/nonzero
  based on its subexpressions (see the `positivity` attribute for more details), or
* try the `norm_num` tactic to prove `e` is positive/nonnegative/nonzero, or
* try showing `e : t` is nonnegative because there is a `CanonicallyOrderedAdd t` instance, or
* use a local hypothesis of the form `0 ≤ e`, `0 < e` or `e ≠ 0`.

This tactic is extensible. See the `positivity` attribute documentation for more details.

* `positivity [t₁, …, tₙ]` first executes `have := t₁; …; have := tₙ` in the current goal,
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

register_hint 1000 positivity
register_try?_tactic (priority := 1000) positivity
