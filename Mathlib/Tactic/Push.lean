/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Patrick Massot, Simon Hudon, Alice Laroche, Frédéric Dupuis,
Jireh Loreaux
-/
import Lean.Elab.Tactic.Location
import Mathlib.Tactic.Push.Attr
import Mathlib.Logic.Basic
import Mathlib.Tactic.Conv

/-!
# The `push` and `push_neg` tactics

The `push` tactic pushes a given constant inside expressions: it can be applied to goals as well
as local hypotheses and also works as a `conv` tactic. `push_neg` is a macro for `push Not`
-/

namespace Mathlib.Tactic.Push

universe u
variable (p q : Prop) {α : Sort u} (s : α → Prop)

-- Note: the lemma `Classical.not_imp` is attempted before `not_forall_eq`
attribute [push] not_not not_or Classical.not_imp

-- We may want to rewrite `¬n = 0` into `0 < n` for `n : ℕ`, so `ne_eq` is marked with low priority.
attribute [push ← low] ne_eq

@[push] theorem not_iff : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

/-
TODO:

attribute [push]
  forall_const forall_and forall_or_left forall_or_right forall_eq forall_eq' forall_self_imp
  exists_const exists_or exists_and_left exists_and_right exists_eq exists_eq'
  and_or_left and_or_right and_true true_and and_false false_and
  or_and_left or_and_right or_true true_or or_false false_or

@[push high] theorem Nat.not_nonneg_iff_eq_zero (n : Nat) : ¬0 < n ↔ n = 0 :=
  Nat.not_lt.trans Nat.le_zero
-/

theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists

/-- Make `push_neg` use `not_and_or` rather than the default `not_and`. -/
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_or` rather than the default `not_and`." }

open Lean Meta Elab.Tactic Parser.Tactic

/--
`pushNegBuiltin` is a simproc to do some rewriting that can't be done by just tagging lemmas.
- `¬(p ∧ q)` turns into `p → ¬q` or `¬a ∨ ¬q`, depending on the option `push_neg.use_distrib`.
- `¬∃ a, p` turns into `∀ a, ¬p`, where the binder name `a` is preserved.
- `¬∀ a, p` turns into `∃ a, ¬p`, where the binder name `a` is preserved.
-/
private def pushNegBuiltin : Simp.Simproc := fun e => do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e.getAppFnArgs with
  | (``And, #[p, q]) =>
    if ← getBoolOption `push_neg.use_distrib then
      return mkSimpStep (mkOr (mkNot p) (mkNot q)) (← mkAppM ``not_and_or_eq #[p, q])
    else
      return mkSimpStep (.forallE `_ p (mkNot q) default) (← mkAppM ``not_and_eq #[p, q])
  | (``Exists, #[_, .lam n typ bo bi]) =>
    return mkSimpStep (.forallE n typ (mkNot bo) bi) (← mkAppM ``not_exists_eq #[.lam n typ bo bi])
  | _ =>
    pushNegForall e
where
  mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
    Simp.Step.continue (some { expr := e, proof? := some pf })
  /--
  Pushes a negation into a forall binder.
  This function is separate because this speeds up compilation.
  -/
  pushNegForall : Simp.Simproc := fun e => do
    if let .forallE name ty body binfo := e then
      let body' : Expr := .lam name ty (mkNot body) binfo
      let body'' : Expr := .lam name ty body binfo
      return mkSimpStep (← mkAppM ``Exists #[body']) (← mkAppM ``not_forall_eq #[body''])
    else
      return Simp.Step.continue

/-- The type for a constant to be pushed by `push`. -/
inductive Head where
| name (const : Name)
| lambda
| Forall

/-- Retreave the `Head` of an expression. -/
def Head.ofExpr (e : Expr) : MetaM Head := do
  if e.isForall then return .Forall
  if e.isLambda then return .lambda
  if let some const := e.getAppFn.constName? then
    return .name const
  throwError "tactic `push` expected a term that can be pushed, not {indentExpr e}"

/--
Check whether the expression is a target for pushing `head`.

Note that for constants, we require `e` to be an application,
because otherwise there is nothing to push.
-/
def Head.isHeadOf (head : Head) (e : Expr) : Bool :=
  match head with
  | .name const => e.isApp && e.isAppOf const
  | .lambda => e.isLambda
  | .Forall => e.isForall

/-- Push at the top level of the current expression. -/
def pushStep (head : Head) : Simp.Simproc := fun e => do
  let e_whnf ← whnfR e
  unless head.isHeadOf e_whnf do
    return Simp.Step.continue
  let thms ← pushExt.getTheorems
  if let some r ← Simp.rewrite? e thms.pre {} (tag := "push") (rflOnly := false) then
    -- We return `.visit r` instead of `.continue r`, because in the case of a triple negation,
    -- after rewriting `¬¬¬p` into `¬p`, we want to rewrite again at `¬p`.
    return Simp.Step.visit r
  if let some ex := e_whnf.not? then
    pushNegBuiltin ex
  else
    return Simp.Step.continue

/--
A simproc variant of `push_neg` that can be used as `simp [↓pushNeg]`.
Note that you should write `↓pushNeg` instead of `pushNeg`, so that negations are pushed greedily.
-/
simproc_decl _root_.pushNeg (Not _) := pushStep (.name ``Not)

/-- The `simp` configuration used in `push`. -/
def PushSimpConfig : Simp.Config where
  zeta := false
  proj := false

/-- Common entry point to the implementation of `push`. -/
def pushCore (head : Head) (tgt : Expr) (disch? : Option Simp.Discharge) : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext PushSimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := match disch? with
    | none => { pre := pushStep head }
    | some disch => { pre := pushStep head, discharge? := disch, wellBehavedDischarge := false }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

/-- Execute main loop of `push` at the main goal. -/
def pushNegTarget (head : Head) (discharge? : Option Simp.Discharge) :
    TacticM Unit := do
  let mvarId ← getMainGoal
  let tgt ← instantiateMVars (← mvarId.getType)
  let mvarIdNew ← applySimpResultToTarget mvarId tgt (← pushCore head tgt discharge?)
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

/-- Execute main loop of `push` at a local hypothesis. -/
def pushNegLocalDecl (head : Head) (discharge? : Option Simp.Discharge) (fvarId : FVarId) :
    TacticM Unit := do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let mvarId ← getMainGoal
  let result ← pushCore head tgt discharge?
  let some (_, mvarIdNew) ← applySimpResultToLocalDecl mvarId fvarId result False | failure
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

open private Lean.Elab.Tactic.mkDischargeWrapper in mkSimpContext

/--
Push a given constant inside of an expression.
For instance, `push (disch := positivity) Real.log` could turn
`log (a * b ^ 2)` into `log a + 2 * log b`.

The `push` tactic can be extended using the `@[push]` attribute.

See also `push_neg`, which is a macro for `push Not`.

In addition to constants, `push` can be used to push `∀` and `fun` binders:
- `push ∀ _, _` can turn `∀ a, p a ∧ q a` into `(∀ a, p a) ∧ (∀ a, q a)`.
- `push fun _ ↦ _` can turn `fun x => f x + g x` into `(fun x => f x) + (fun x => g x)`
(or into `f + g`).

One can use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢`, as usual.
-/
syntax (name := push) "push " (discharger)? (colGt term) (location)? : tactic

open Elab in
/-- Elaborator for the expression passed to `push` -/
def elabHead (stx : Syntax) : TermElabM Expr := withRef stx do
  if stx.isIdent then
    if let some e ← Term.resolveId? stx (withInfo := true) then
      return e
  withTheReader Term.Context ({ · with ignoreTCFailures := true }) <|
  Term.withoutModifyingElabMetaStateWithInfo <|
  Term.withoutErrToSorry <|
  Term.elabTerm stx none

@[tactic push, inherit_doc push]
def elabPush : Tactic := fun stx => withMainContext do
  let dischargeWrapper ← Lean.Elab.Tactic.mkDischargeWrapper stx[1]
  let head ← Head.ofExpr (← elabHead stx[2])
  let loc := expandOptLocation stx[3]
  dischargeWrapper.with fun discharge? => do
    withLocation loc
      (pushNegLocalDecl head discharge?)
      (pushNegTarget head discharge?)
      (fun _ ↦ logInfo "push_neg couldn't find a negation to push")

/--
Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.

`push_neg` is a special case of the more general `push` tactic, applied to the constant `Not`.
The `push` tactic can be extended using the `@[push]` attribute. Additionally,
there is a `pushNeg` simproc, which can be used as `simp [↓pushNeg]`.

`push_neg` has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.

Another example: given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε > 0 ∧ ∀ δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢`, as usual.
-/
macro (name := push_neg) "push_neg" loc:(location)? : tactic => `(tactic| push Not $[$loc]?)

section Conv

@[inherit_doc push]
syntax (name := pushConv) "push " (discharger)? (colGt term) : conv

@[inherit_doc push_neg]
macro "push_neg" : conv => `(conv| push Not)

/-- Execute `push` as a conv tactic. -/
@[tactic pushConv] def elabPushConv : Tactic := fun stx ↦ withMainContext do
  let dischargeWrapper ← Lean.Elab.Tactic.mkDischargeWrapper stx[1]
  let head ← Head.ofExpr (← elabHead stx[2])
  dischargeWrapper.with fun discharge? => do
    Conv.applySimpResult (← pushCore head (← instantiateMVars (← Conv.getLhs)) discharge?)

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNeg) tk:"#push_neg " e:term : command => `(command| #conv%$tk push_neg => $e)

end Conv

section DiscrTree

/--
`#push_discr_tree` is a command to see what `push` lemmas are in the environment for pushing
a given constant. This can be helpful when you are constructing a set of `push` lemmas.
-/
syntax (name := pushTree) "#push_discr_tree " (colGt term) : command

@[command_elab pushTree, inherit_doc pushTree]
def elabPushTree : Elab.Command.CommandElab := fun stx => do
  Elab.Command.runTermElabM fun _ => do
  let head ← elabHead stx[1]
  let headKey : DiscrTree.Key := (← withReducible <| DiscrTree.getMatchKeyRootFor head).1
  let thms ← pushExt.getTheorems
  let mut logged := false
  for (key, trie) in thms.pre.root do
    let keyEq (k k' : DiscrTree.Key) : Bool :=
      match k, k' with
      | .const n _, .const n' _ => n == n'
      | .other    , .other      => true
      | .arrow    , .arrow      => true
      | _         , _           => false
    if keyEq key headKey then
      logInfo m! "DiscrTree branch for {key}:{indentD (format trie)}"
      logged := true
  unless logged do
    logInfo m! "There are no `push` theorems for the key {headKey}"

end DiscrTree

end Mathlib.Tactic.Push
