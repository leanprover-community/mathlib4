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
import Mathlib.Util.AtLocation

/-!
# The `push`, `push_neg` and `pull` tactics

The `push` tactic pushes a given constant inside expressions: it can be applied to goals as well
as local hypotheses and also works as a `conv` tactic. `push_neg` is a macro for `push Not`.

The `pull` tactic does the reverse: it pulls the given constant towards the root of the expression.
-/

namespace Mathlib.Tactic.Push

variable (p q : Prop) {α : Sort*} (s : α → Prop)

-- The more specific `Classical.not_imp` is attempted before the more general `not_forall_eq`.
-- This happens because `not_forall_eq`  is handled manually in `pushNegBuiltin`.
attribute [push] not_not not_or Classical.not_imp not_false_eq_true not_true_eq_false
attribute [push ←] ne_eq

@[push] theorem not_iff : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]
@[push] theorem not_exists : (¬ ∃ x, s x) ↔ (∀ x, binderNameHint x s <| ¬ s x) :=
  _root_.not_exists

-- TODO: lemmas involving `∃` should be tagged using `binderNameHint`,
-- and lemmas involving `∀` would need manual rewriting to keep the binder name.
attribute [push]
  forall_const forall_and forall_or_left forall_or_right forall_eq forall_eq' forall_self_imp
  exists_const exists_or exists_and_left exists_and_right exists_eq exists_eq'
  and_or_left and_or_right and_true true_and and_false false_and
  or_and_left or_and_right or_true true_or or_false false_or

attribute [push ←] Function.id_def

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

section push

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

/-- The `simp` configuration used in `push`. -/
def pushSimpConfig : Simp.Config where
  zeta := false
  proj := false

/-- Try to rewrite using a push lemma. -/
def pushStep (head : Head) : Simp.Simproc := fun e => do
  let e_whnf ← whnf e
  let some e_head := Head.ofExpr? e_whnf | return Simp.Step.continue
  unless e_head == head do
    return Simp.Step.continue
  let thms := pushExt.getState (← getEnv)
  if let some r ← Simp.rewrite? e thms {} "push" false then
    -- We return `.visit r` instead of `.continue r`, because in the case of a triple negation,
    -- after rewriting `¬ ¬ ¬p` into `¬p`, we want to rewrite again at `¬p`.
    return Simp.Step.visit r
  if let some ex := e_whnf.not? then
    pushNegBuiltin ex
  else
    return Simp.Step.continue

/-- Common entry point to the implementation of `push`. -/
def pushCore (head : Head) (tgt : Expr) (disch? : Option Simp.Discharge) : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext pushSimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := match disch? with
    | none => { pre := pushStep head }
    | some disch => { pre := pushStep head, discharge? := disch, wellBehavedDischarge := false }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

end push

section pull

open Simp in
/-- Try to rewrite using a pull lemma. -/
def pullStep (head : Head) : Simp.Simproc := fun e => do
  let thms := pullExt.getState (← getEnv)
  -- We can't use `Simp.rewrite?` here, because we need to only allow rewriting with theorems
  -- that pull the correct head.
  let candidates ← withSimpIndexConfig <| thms.getMatchWithExtra e
  if candidates.isEmpty then
    return Simp.Step.continue
  let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.1.priority > e₂.1.1.priority
  for ((thm, thm_head), numExtraArgs) in candidates do
    if thm_head == head then
      if let some result ← tryTheoremWithExtraArgs? e thm numExtraArgs then
        return Simp.Step.continue result
  return Simp.Step.continue

/-- Common entry point to the implementation of `pull`. -/
def pullCore (head : Head) (tgt : Expr) (disch? : Option Simp.Discharge) : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext pushSimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := match disch? with
    | none => { post := pullStep head }
    | some disch => { post := pullStep head, discharge? := disch, wellBehavedDischarge := false }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

end pull

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
  /-- Auxiliary function for `elabCDotFunctionAlias?` -/
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
      or a function with `·` notation as in `push ¬ .`"

end ElabHead

/-- Elaborate the `(disch := ...)` syntax for a `simp`-like tactic. -/
def elabDischarger (stx : TSyntax ``discharger) : TacticM Simp.Discharge :=
  return (← tacticToDischarge stx.raw[3]).2

/--
`push` pushes the given constant away from the root of the expression. For example
- `push · ∈ ·` rewrites `x ∈ {y} ∪ zᶜ` into `x = y ∨ ¬ x ∈ z`.
- `push (disch := positivity) Real.log` rewrites `log (a * b ^ 2)` into `log a + 2 * log b`.
- `push ¬ ·` is the same as `push_neg` or `push Not`, and it rewrites
  `¬∀ ε > 0, ∃ δ > 0, δ < ε` into `∃ ε > 0, ∀ δ > 0, ε ≤ δ`.

In addition to constants, `push` can be used to push `∀` and `fun` binders:
- `push ∀ _, ·` rewrites `∀ a, p a ∧ q a` into `(∀ a, p a) ∧ (∀ a, q a)`.
- `push fun _ ↦ ·` rewrites  `fun x => f x + g x` into `f + g`

The `push` tactic can be extended using the `@[push]` attribute.

To push a constant at a hypothesis, use the `push ... at h` or `push ... at *` syntax.
-/
elab (name := push) "push " disch?:(discharger)? head:(colGt term) loc:(location)? : tactic => do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (pushCore head · disch?) "push" loc (failIfUnchanged := true) false

/--
Push negations into the conclusion or a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.

`push_neg` is a special case of the more general `push` tactic, namely `push Not`.
The `push` tactic can be extended using the `@[push]` attribute. `push` has special-casing
built in for `push Not`, so that it can preserve binder names, and so that `¬ (p ∧ q)` can be
transformed to either of `p → ¬ q` (the default) and `¬ p ∨ ¬ q`. To get `¬ p ∨ ¬ q`, use
`set_option push_neg.use_distrib true`.

Another example: given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|
```
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢`, as usual.
-/
macro (name := push_neg) "push_neg" loc:(location)? : tactic => `(tactic| push Not $[$loc]?)

/--
`pull` is the inverse tactic to `push`.
It pulls the given constant towards the root of the expression. For example
- `pull · ∈ ·` rewrites `x ∈ y ∨ ¬ x ∈ z` into `x ∈ y ∪ zᶜ`.
- `pull (disch := positivity) Real.log` rewrites `log a + 2 * log b` into `log (a * b ^ 2)`.

A lemma is considdered a `pull` lemma if its reverse direction is a `push` lemma
in which the pushed constant is present in the result.
For example, `not_or : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q` is a `pull` lemma for negation,
but `not_not : ¬ ¬ p ↔ p` is not a `pull` lemma.
-/
elab (name := pull) "pull " disch?:(discharger)? head:(colGt term) loc:(location)? : tactic => do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (pullCore head · disch?) "pull" loc (failIfUnchanged := true) false

/-- A simproc variant of `push fun _ ↦ ·` that should be used as `simp [↓pushFun]`. -/
simproc_decl _root_.pushFun (fun _ ↦ _) := pushStep .lambda

section Conv

@[inherit_doc push]
elab "push " disch?:(discharger)? head:(colGt term) : conv => withMainContext do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  Conv.applySimpResult (← pushCore head (← instantiateMVars (← Conv.getLhs)) disch?)

@[inherit_doc push_neg]
macro "push_neg" : conv => `(conv| push Not)

/--
The syntax is `#push head e`, where `head` is a constant and `e` is an expression,
which will print the `push head` form of `e`.

`#push` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushCommand) tk:"#push " head:ident e:term : command =>
  `(command| #conv%$tk push $head:ident => $e)

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNegCommand) tk:"#push_neg " e:term : command => `(command| #push%$tk Not $e)

@[inherit_doc pull]
elab "pull " disch?:(discharger)? head:(colGt term) : conv => withMainContext do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  Conv.applySimpResult (← pullCore head (← instantiateMVars (← Conv.getLhs)) disch?)

/--
The syntax is `#pull head e`, where `head` is a constant and `e` is an expression,
which will print the `pull head` form of `e`.

`#pull` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pullCommand) tk:"#pull " head:ident e:term : command =>
  `(command| #conv%$tk pull $head:ident => $e)

end Conv

section DiscrTree

/--
`#push_discr_tree X` shows the discrimination tree of all lemmas used by `push X`.
This can be helpful when you are constructing a set of `push` lemmas for the constant `X`.
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
    logInfo m! "There are no `push` theorems for `{head.toString}`"

end DiscrTree

end Mathlib.Tactic.Push
