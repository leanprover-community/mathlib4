/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.Positivity.Core

/-!
## The `@[auto_positivity]` attribute

This file defines the `@[auto_positivity]` attribute, which automatically generates `positivity`
extensions from ordinary lemmas.

A lemma tagged `@[auto_positivity]` must have a conclusion of the form `0 < f …`, `0 ≤ f …`,
`f … ≠ 0` or `0 ≠ f …`. When the `positivity` tactic encounters an expression matching `f …`,
it will try to apply the lemma, discharging:
* instance arguments by instance synthesis,
* hypotheses of the form `0 < _`, `0 ≤ _`, `_ ≠ 0`, `0 ≠ _` by a recursive call to `positivity`,
* any other propositional hypotheses by looking for a matching local hypothesis.

Example:
```lean
def double (x : ℤ) : ℤ := 2 * x

@[auto_positivity]
theorem double_pos {x : ℤ} (hx : 0 < x) : 0 < double x := by
  unfold double; positivity

example {x : ℤ} (hx : 0 < x) : 0 < double (double x) + 1 := by positivity
```

This is implemented by a single catch-all `positivity` extension which consults a
discrimination tree of tagged lemmas, so tagging a lemma does not require writing any
metaprogramming code. Lemmas from other files can also be tagged with
`attribute [auto_positivity] my_lemma`.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Positivity

/-- The `auto_positivity` attribute. Tag a lemma whose conclusion has the form `0 < f …`,
`0 ≤ f …`, `f … ≠ 0` or `0 ≠ f …` to generate a `positivity` extension for expressions
matching `f …`. Hypotheses of the lemma must be instance arguments, positivity-shaped facts
(recursively dischargeable by `positivity`), or side conditions available verbatim in the
local context. -/
syntax (name := auto_positivity) "auto_positivity" : attr

end Mathlib.Tactic.Positivity

namespace Mathlib.Meta.Positivity

/-- The relation proved by the conclusion of an `@[auto_positivity]` lemma. -/
inductive AutoRel : Type
  | /-- The conclusion is `0 < a`. -/ lt
  | /-- The conclusion is `0 ≤ a`. -/ le
  | /-- The conclusion is `a ≠ 0`. -/ ne
  | /-- The conclusion is `0 ≠ a`. -/ ne'
  deriving Repr, DecidableEq

/-- Check whether `e` is syntactically the zero of its type
(either `OfNat.ofNat 0` or `Zero.zero`). -/
def isZeroExpr (e : Expr) : Bool :=
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0)
    || e.isAppOfArity ``Zero.zero 2

/-- Parse a proposition of the form `0 < a`, `0 ≤ a`, `a ≠ 0` or `0 ≠ a`, returning the
relation together with the subject `a`. Returns `none` if `concl` does not have this form.

The proposition is first inspected syntactically; if that fails, it is normalized with `whnfR`
and inspected again (note that this unfolds `a ≠ b` into `a = b → False`, which is why `Ne`
must be recognized before normalizing). -/
def parseConcl? (concl : Expr) : MetaM (Option (AutoRel × Expr)) := do
  let concl ← instantiateMVars concl
  if let some r ← go concl then
    return some r
  go (← whnfR concl)
where
  /-- Match one candidate form of the conclusion. -/
  go (concl : Expr) : MetaM (Option (AutoRel × Expr)) := do
    if concl.isAppOfArity ``Ne 3 then
      if isZeroExpr (← whnfR (concl.getArg! 2)) then
        return some (.ne, concl.getArg! 1)
      else if isZeroExpr (← whnfR (concl.getArg! 1)) then
        return some (.ne', concl.getArg! 2)
    else if concl.isAppOfArity ``LT.lt 4 then
      if isZeroExpr (← whnfR (concl.getArg! 2)) then
        return some (.lt, concl.getArg! 3)
    else if concl.isAppOfArity ``LE.le 4 then
      if isZeroExpr (← whnfR (concl.getArg! 2)) then
        return some (.le, concl.getArg! 3)
    else if concl.isArrow && concl.bindingBody!.isConstOf ``False then
      -- an unfolded `Ne`, i.e. `a = b → False`
      let eq := concl.bindingDomain!
      if eq.isAppOfArity ``Eq 3 then
        if isZeroExpr (← whnfR (eq.getArg! 2)) then
          return some (.ne, eq.getArg! 1)
        else if isZeroExpr (← whnfR (eq.getArg! 1)) then
          return some (.ne', eq.getArg! 2)
    return none

/-- An entry in the `auto_positivity` lemma table: discrimination-tree keys for the subject of
the lemma's conclusion, paired with the lemma name. -/
abbrev AutoEntry := Array DiscrTree.Key × Name

/-- Environment extension storing the lemmas tagged `@[auto_positivity]`. -/
initialize autoPositivityExt : SimpleScopedEnvExtension AutoEntry (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (keys, n) => dt.insertKeyValue keys n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `auto_positivity
  descr := "generate a positivity extension from a lemma concluding `0 < _`, `0 ≤ _` or `_ ≠ 0`"
  add := fun declName _stx kind => MetaM.run' do
    let info ← getConstInfo declName
    let (_, _, concl) ← forallMetaTelescope info.type
    let some (_, subject) ← parseConcl? concl
      | throwError "@[auto_positivity] requires a conclusion of the form \
          `0 < a`, `0 ≤ a`, `a ≠ 0` or `0 ≠ a`, but the conclusion of {declName} \
          is{indentExpr concl}"
    if subject.getAppFn.isMVar then
      throwError "@[auto_positivity] requires the head of the conclusion's subject to be a \
        constant, but in {declName} it is a variable, so the extension would apply to every \
        expression"
    let keys ← DiscrTree.mkPath subject
    autoPositivityExt.add (keys, declName) kind
}

/-- Try to prove a positivity fact about `e` by applying the `@[auto_positivity]` lemma
`lemmaName`. Returns the relation proved by the lemma's conclusion together with the proof term.

The lemma's conclusion is unified with the corresponding relation about `e`; remaining instance
arguments are synthesized, positivity-shaped hypotheses are discharged by a recursive call to
the `positivity` machinery, and other propositional hypotheses are looked up in the local
context. -/
def applyAutoLemma (lemmaName : Name) (e : Expr) : MetaM (AutoRel × Expr) := do
  let info ← getConstInfo lemmaName
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let (args, bis, concl) ←
    forallMetaTelescope (info.type.instantiateLevelParams info.levelParams us)
  let some (rel, subject) ← parseConcl? concl
    | throwError "auto_positivity lemma {lemmaName} has an unsupported conclusion"
  unless ← isDefEq subject e do
    throwError "{e} does not match the conclusion of {lemmaName}"
  for arg in args, bi in bis do
    let m := arg.mvarId!
    unless ← m.isAssigned do
      let t ← instantiateMVars (← m.getType)
      if bi.isInstImplicit then
        m.assign (← synthInstance t)
      else if ← Meta.isProp t then
        try
          m.assign (← Meta.Positivity.solve t)
        catch ex =>
          if let some fvarId ← findLocalDeclWithType? t then
            m.assign (.fvar fvarId)
          else
            throw ex
  for arg in args do
    unless ← arg.mvarId!.isAssigned do
      throwError "could not determine all arguments of {lemmaName} when proving positivity of {e}"
  return (rel, ← instantiateMVars (mkAppN (.const lemmaName us) args))

/-- Package a raw proof `pf` of the relation `rel` about `e` into a `Strictness` result. -/
def AutoRel.toStrictness {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (pα? : Option Q(PartialOrder $α)) (e : Q($α)) (rel : AutoRel) (pf : Expr) :
    MetaM (Strictness zα e pα?) :=
  match pα?, rel with
  | _, .ne => pure (.nonzero pf)
  | _, .ne' => do return .nonzero (← mkAppM ``Ne.symm #[pf])
  | some pα, .lt => pure (.positive (pα := pα) pf)
  | some pα, .le => pure (.nonnegative (pα := pα) pf)
  | none, .lt => throwError "cannot record a positivity result without a `PartialOrder` instance"
  | none, .le =>
    throwError "cannot record a nonnegativity result without a `PartialOrder` instance"

/-- The `positivity` extension that tries all applicable `@[auto_positivity]` lemmas.

This is registered with a catch-all pattern; the actual filtering happens via the
discrimination tree in `autoPositivityExt`. -/
@[positivity _]
def evalAutoPositivityLemmas : PositivityExt where
  eval {_u _α} zα pα? e := do
    let names ← (autoPositivityExt.getState (← getEnv)).getMatch e
    let mut result : Strictness zα e pα? := .none
    for lemmaName in names do
      result ← orElse result do
        let (rel, pf) ← applyAutoLemma lemmaName e
        rel.toStrictness zα pα? e pf
    return result

end Mathlib.Meta.Positivity
