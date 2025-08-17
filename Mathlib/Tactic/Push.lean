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

-- Note: we want `Classical.not_imp` to be attempted before the more general `not_forall_eq`.
-- This happens because `not_forall_eq` isn't a `push` lemma,
-- but instead is handled manually by the `pushNegBuiltin`.
attribute [push] not_not not_or Classical.not_imp not_true not_false
attribute [push ←] ne_eq

@[push] theorem not_iff : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]
@[push] theorem not_exists : (¬ ∃ x, s x) ↔ (∀ x, binderNameHint x s <| ¬ s x) :=
  _root_.not_exists


attribute [push]
  forall_const forall_and forall_or_left forall_or_right forall_eq forall_eq' forall_self_imp
  exists_const exists_or exists_and_left exists_and_right exists_eq exists_eq'
  and_or_left and_or_right and_true true_and and_false false_and
  or_and_left or_and_right or_true true_or or_false false_or

-- TODO(Jovan): Decide if we want this lemma, and if so, fix the proofs that break as a result
-- @[push high] theorem Nat.not_nonneg_iff_eq_zero (n : Nat) : ¬0 < n ↔ n = 0 :=
--   Nat.not_lt.trans Nat.le_zero

theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall

/-- Make `push_neg` use `not_and_or` rather than the default `not_and`. -/
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_or` rather than the default `not_and`." }

open Lean Meta Elab.Tactic Parser.Tactic

/--
`pushNegBuiltin` is a simproc for pushing `¬` in a way that can't be done
using the `@[push]` attribute.
- `¬(p ∧ q)` turns into `p → ¬q` or `¬a ∨ ¬q`, depending on the option `push_neg.use_distrib`.
- `¬∀ a, p` turns into `∃ a, ¬p`, where the binder name `a` is preserved.
-/
private def pushNegBuiltin : Simp.Simproc := fun e => do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e with
  | .app (.app (.const ``And _) p) q =>
    if ← getBoolOption `push_neg.use_distrib then
      return mkSimpStep (mkOr (mkNot p) (mkNot q)) (mkApp2 (.const ``not_and_or_eq []) p q)
    else
      return mkSimpStep (.forallE `_ p (mkNot q) .default) (mkApp2 (.const ``not_and_eq []) p q)
  | .forallE name ty body binfo =>
    let body' : Expr := .lam name ty (mkNot body) binfo
    let body'' : Expr := .lam name ty body binfo
    return mkSimpStep (← mkAppM ``Exists #[body']) (← mkAppM ``not_forall_eq #[body''])
  | _ =>
    return Simp.Step.continue
where
  mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
    Simp.Step.continue (some { expr := e, proof? := some pf })

section ElabHead
open Elab Term

private partial def syntaxLambdaBody (stx : Syntax) : Syntax :=
  match stx with
  | `(fun $_ => $stx) => syntaxLambdaBody stx
  | _ => stx

/--
This is a copy of `elabCDotFunctionAlias?` in core lean.
It has been modified so that it can also support `∃ _, ·`, `∑ _, ·`, etc.
-/
def elabCDotFunctionAlias? (stx : Term) : TermElabM (Option Expr) := do
  let some stx ← liftMacroM <| expandCDotArg? stx | pure none
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(fun $binders* => $f $args*) =>
    -- we use `syntaxLambdaBody` to get rid of extra lambdas in cases like `∃ _, ·`
    if binders.raw.toList.isPerm (args.raw.toList.map syntaxLambdaBody) then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => binop% $f $a $b)
  | `(fun $binders* => binop_lazy% $f $a $b)
  | `(fun $binders* => leftact% $f $a $b)
  | `(fun $binders* => rightact% $f $a $b)
  | `(fun $binders* => binrel% $f $a $b)
  | `(fun $binders* => binrel_no_prop% $f $a $b) =>
    if binders == #[a, b] || binders == #[b, a] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | `(fun $binders* => unop% $f $a) =>
    if binders == #[a] then
      try Term.resolveId? f catch _ => return none
    else
      return none
  | _ => return none
where
  expandCDotArg? (stx : Term) : MacroM (Option Term) :=
    match stx with
    | `(($h:hygieneInfo $e)) => Term.expandCDot? e h.getHygieneInfo
    | _ => Term.expandCDot? stx none

/-- Elaborator for the argument passed to `push`. It accepts a constant, or a function -/
def elabHead (term : Term) : TermElabM Head := withRef term do
  match term with
  | `(fun $_ => ·) => return .lambda
  | `(∀ $_, ·) => return .forall
  | _ =>
    match ← resolveId? term (withInfo := true) <|> elabCDotFunctionAlias? term with
    | some (.const name _) =>
      return .name name
    | _ => throwError "Could not resolve `push` arugment {term}. \
      Expected either a constant as in `push Not`, \
      or a function with `·` notation as in `push ¬.`"

end ElabHead


/-- Push at the top level of the current expression. -/
def pushStep (head : Head) : Simp.Simproc := fun e => do
  let e_whnf ← whnfR e
  let some e_head := Head.ofExpr? e_whnf | return Simp.Step.continue
  unless e_head == head do
    return Simp.Step.continue
  let thms := pushExt.getState (← getEnv)
  if let some r ← Simp.rewrite? e thms {} "push" false then
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
def pushSimpConfig : Simp.Config where
  zeta := false
  proj := false
  congrConsts := false -- this is a workaround, and can hopefully be removed

/-- Common entry point to the implementation of `push`. -/
def pushCore (head : Head) (tgt : Expr) (disch? : Option Simp.Discharge) : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext pushSimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := match disch? with
    | none => { pre := pushStep head }
    | some disch => { pre := pushStep head, discharge? := disch, wellBehavedDischarge := false }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

/-- Execute main loop of `push` at the main goal. -/
def pushTarget (head : Head) (discharge? : Option Simp.Discharge) :
    TacticM Unit := withMainContext do
  let mvarId ← getMainGoal
  let tgt ← instantiateMVars (← mvarId.getType)
  let mvarIdNew ← applySimpResultToTarget mvarId tgt (← pushCore head tgt discharge?)
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

/-- Execute main loop of `push` at a local hypothesis. -/
def pushLocalDecl (head : Head) (discharge? : Option Simp.Discharge) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let mvarId ← getMainGoal
  let result ← pushCore head tgt discharge?
  let some (_, mvarIdNew) ← applySimpResultToLocalDecl mvarId fvarId result False | failure
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

/--
`push` pushes the given constant away from the root of the expression. For example
- `push · ∈ ·` rewrites `x ∈ {y} ∪ zᶜ` into `x = y ∨ ¬ x ∈ z`
- `push (disch := positivity) Real.log` rewrites `log (a * b ^ 2)` into `log a + 2 * log b`.
- `push ¬·` is the same as `push_neg` or `push Not`, and it rewrites
  `¬∀ ε > 0, ∃ δ > 0, δ < ε` into `∃ ε > 0, ∀ δ > 0, ε ≤ δ`.

In addition to constants, `push` can be used to push `∀` and `fun` binders:
- `push ∀ _, ·` rewrites `∀ a, p a ∧ q a` into `(∀ a, p a) ∧ (∀ a, q a)`.
- `push fun _ ↦ ·` rewrites  `fun x => f x + g x` into `f + g`

The `push` tactic can be extended using the `@[push]` attribute.

To push a constant at a hypothesis, use the `push ... at h` or `push ... at *` syntax.
-/
syntax (name := push) "push " (discharger)? (colGt term) (location)? : tactic

open private Lean.Elab.Tactic.mkDischargeWrapper in mkSimpContext

@[tactic push, inherit_doc push]
def elabPush : Tactic := fun stx => do
  let dischargeWrapper ← Lean.Elab.Tactic.mkDischargeWrapper stx[1]
  let head ← elabHead ⟨stx[2]⟩
  let loc := expandOptLocation stx[3]
  dischargeWrapper.with fun discharge? => do
    withLocation loc
      (pushLocalDecl head discharge?)
      (pushTarget head discharge?)
      (fun _ ↦ logInfo m!"`push` couldn't find a {head.toString} to push")

/--
Push negations into the conclusion or a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved. There is also a `pushNeg` simproc which
should be used as `simp [↓pushNeg]`

`push_neg` is a special case of the more general `push` tactic, for the constant `Not`.
The `push` tactic can be extended using the `@[push]` attribute.

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
  let head ← elabHead ⟨stx[2]⟩
  dischargeWrapper.with fun discharge? => do
    Conv.applySimpResult (← pushCore head (← instantiateMVars (← Conv.getLhs)) discharge?)

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNegCommand) tk:"#push_neg " e:term : command =>
  `(command| #conv%$tk push_neg => $e)

/--
The syntax is `#push head e`, where `head` is a constant and `e` is an expression,
which will print the `push head` form of `e`.

`#push` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushCommand) tk:"#push " head:ident e:term : command =>
  `(command| #conv%$tk push $head:ident => $e)

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
  let head ← elabHead ⟨stx[1]⟩
  let thms := pushExt.getState (← getEnv)
  let mut logged := false
  for (key, trie) in thms.root do
    let matchesHead (k : DiscrTree.Key) : Bool :=
      match k, head with
      | .const n _, .name n' => n == n'
      | .other    , .lambda  => true
      | .arrow    , .forall  => true
      | _         , _        => false
    if matchesHead key then
      logInfo m! "DiscrTree branch for {key}:{indentD (format trie)}"
      logged := true
  unless logged do
    logInfo m! "There are no `push` theorems for {head.toString}"

end DiscrTree

end Mathlib.Tactic.Push
