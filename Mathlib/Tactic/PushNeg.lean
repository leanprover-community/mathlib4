/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Patrick Massot, Simon Hudon, Alice Laroche, Frédéric Dupuis,
  Jireh Loreaux
-/

import Mathlib.Data.Finite.Defs

/-!
# The `push` and `push_neg` tactics

The `push` tactic pushes a given constant inside expressions: it can be applied to goals as well
as local hypotheses and also works as a `conv` tactic. `push_neg` is a macro for `push Not`
-/

namespace Mathlib.Tactic.Push

open Lean Meta Elab.Tactic Parser.Tactic

initialize registerTraceClass `Tactic.push

section Attr

/-- The `push` simp attribute. -/
initialize pushExt : SimpExtension ←
  registerSimpAttr `push "\
    The `push` simp attribute uses `push` lemmas to move \
    the given constants toward the leaf nodes of the expression."

/--
The `push` attribute is used to tag lemmas that "push" a constant into an expression.

For example:
```lean

```

should be given to lemmas that "push" a constant towards the leaf nodes of
an expression. The main use case is for pushing negations.
-/
syntax (name := pushAttr) "push" (ppSpace num)? : attr

initialize registerBuiltinAttribute {
  name := `pushAttr
  descr := "attribute for push"
  add := fun decl stx kind => MetaM.run' do
    let `(attr| push $[$prio]?) := stx | unreachable!
    let prio := (prio.bind (·.1.isNatLit?)).getD (eval_prio default)
    addSimpTheorem pushExt decl (post := false) (inv := false) kind prio
}

end Attr


variable (p q : Prop) {α : Sort*} {β : Type*} (s : α → Prop)

theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists


/-- Make `push_neg` use `not_and_or` rather than the default `not_and`. -/
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_or` rather than the default `not_and`." }

/--
Pushes a negation in ways that aren't possible with a lemma:
- `¬(a ∧ b)` turns into `a → ¬b` or `¬a ∨ ¬b`, depending on the option `push_neg.use_distrib`.
- `¬(a = b)` turns into `a ≠ b`, which would cause a loop if used as a `simp` lemma.
- `¬∃ a, p` turns into `∀ a, ¬p`, where the binder name `a` is preserved.
- `¬∀ a, p` turns into `∃ a, ¬p`, where the binder name `a` is preserved.
-/
private def pushNegBuiltin : Simp.Simproc := fun e => do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e.getAppFnArgs with
  | (``And, #[p, q]) =>
    match ← getBoolOption `push_neg.use_distrib with
    | false => return mkSimpStep (.forallE `_ p (mkNot q) default) (← mkAppM ``not_and_eq #[p, q])
    | true  => return mkSimpStep (mkOr (mkNot p) (mkNot q)) (← mkAppM ``not_and_or_eq #[p, q])
  | (``Eq, #[_, e₁, e₂]) =>
    return Simp.Step.continue (some { expr := ← mkAppM ``Ne #[e₁, e₂] })
  | (``Exists, #[_, .lam n typ bo bi]) =>
    return mkSimpStep (.forallE n typ (mkNot bo) bi)
      (← mkAppM ``not_exists_eq #[.lam n typ bo bi])
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


/-- Push at the top level of the current expression. -/
def pushStep (const : Name) : Simp.Simproc := fun e => do
  let e_whnf ← whnfR e
  unless e_whnf.isAppOf const do
    return Simp.Step.continue
  if let Simp.Step.visit r ← (Simp.rewritePre) e then
    return Simp.Step.visit r
  if let some ex := e_whnf.not? then
    pushNegBuiltin ex
  else
    return Simp.Step.continue

def PushSimpConfig : Simp.Config where
  zeta := false
  proj := false

/-- Common entry point to the implementation of `push`. -/
def pushCore (const : Name) (tgt : Expr) : MetaM Simp.Result := do
  let myctx : Simp.Context ← Simp.mkContext PushSimpConfig
      (simpTheorems := #[← pushExt.getTheorems])
      (congrTheorems := (← getSimpCongrTheorems))
  (·.1) <$> Simp.main tgt myctx (methods := { pre := (pushStep const) })

/-- Execute main loop of `push` at the main goal. -/
def pushNegTarget (const : Name) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let newGoal ← applySimpResultToTarget goal tgt (← pushCore const tgt)
  if newGoal == goal then throwError "push made no progress"
  replaceMainGoal [newGoal]


/-- Execute main loop of `push` at a local hypothesis. -/
def pushNegLocalDecl (const : Name) (fvarId : FVarId) : TacticM Unit := withMainContext do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let goal ← getMainGoal
  let myres ← pushCore const tgt
  let some (_, newGoal) ← applySimpResultToLocalDecl goal fvarId myres False | failure
  if newGoal == goal then throwError "push made no progress"
  replaceMainGoal [newGoal]

/--
Push a given constant inside of an expression
For instance, `push Real.log` could turn `log (a * b ^ 2)` into `log a + 2 * log b`.

The `push` tactic can be extended using the `@[push]` attribute.

See also `push_neg`, which is a macro for `push Not`.

One can use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢`, as usual.
-/
elab (name := push) "push" nameId:(ppSpace colGt ident) loc:(location)? : tactic => do
  let const ← Elab.realizeGlobalConstNoOverloadWithInfo nameId
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  withLocation loc
    (pushNegLocalDecl const)
    (pushNegTarget const)
    (fun _ ↦ logInfo "push_neg couldn't find a negation to push")

/--
Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.

`push_neg` is a special case of the more general `push` tactic, applied to the constant `Not`.
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
syntax (name := pushConv) "push" (ppSpace colGt ident) : conv

@[inherit_doc push_neg]
macro "push_neg" : conv => `(conv| push Not)

/-- Execute `push` as a conv tactic. -/
@[tactic pushConv] def elabPushConv : Tactic := fun stx ↦ withMainContext do
  let const ← Elab.realizeGlobalConstNoOverloadWithInfo stx[1]
  Conv.applySimpResult (← pushCore const (← instantiateMVars (← Conv.getLhs)))

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNeg) tk:"#push_neg " e:term : command => `(command| #conv%$tk push_neg => $e)

end Conv

end Mathlib.Tactic.Push
