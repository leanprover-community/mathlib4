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

The `pull` tactic does the reverse: it pulls the given constant towards the head of the expression.
-/

namespace Mathlib.Tactic.Push

variable (p q : Prop) {α : Sort*} (s : α → Prop)

-- The more specific `Classical.not_imp` is attempted before the more general `not_forall_eq`.
-- This happens because `not_forall_eq` is handled manually in `pushNegBuiltin`.
attribute [push] not_not not_or Classical.not_imp not_false_eq_true not_true_eq_false
attribute [push ←] ne_eq

@[push] theorem not_iff : ¬ (p ↔ q) ↔ (p ∧ ¬ q) ∨ (¬ p ∧ q) :=
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

-- these lemmas are only for the `pull` tactic
attribute [push low]
  forall_and_left forall_and_right -- needs lower priority than `forall_and` in the `pull` tactic

attribute [push ←] Function.id_def

-- TODO: decide if we want this lemma, and if so, fix the proofs that break as a result
-- @[push high] theorem Nat.not_nonneg_iff_eq_zero (n : Nat) : ¬ 0 < n ↔ n = 0 :=
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
- `¬ (p ∧ q)` turns into `p → ¬ q` or `¬ p ∨ ¬ q`, depending on the option `push_neg.use_distrib`.
- `¬ ∀ a, p` turns into `∃ a, ¬ p`, where the binder name `a` is preserved.
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

/-- Try to rewrite using a `push` lemma. -/
def pushStep (head : Head) : Simp.Simproc := fun e => do
  let e_whnf ← whnf e
  let some e_head := Head.ofExpr? e_whnf | return Simp.Step.continue
  unless e_head == head do
    return Simp.Step.continue
  let thms := pushExt.getState (← getEnv)
  if let some r ← Simp.rewrite? e thms {} "push" false then
    -- We return `.visit r` instead of `.continue r`, because in the case of a triple negation,
    -- after rewriting `¬ ¬ ¬ p` into `¬ p`, we may want to rewrite `¬ p` again.
    return Simp.Step.visit r
  if let some e := e_whnf.not? then
    pushNegBuiltin e
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

/-- Try to rewrite using a `pull` lemma. -/
def pullStep (head : Head) : Simp.Simproc := fun e => do
  let thms := pullExt.getState (← getEnv)
  -- We can't use `Simp.rewrite?` here, because we need to only allow rewriting with theorems
  -- that pull the correct head.
  let candidates ← Simp.withSimpIndexConfig <| thms.getMatchWithExtra e
  if candidates.isEmpty then
    return Simp.Step.continue
  let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.1.priority > e₂.1.1.priority
  for ((thm, thm_head), numExtraArgs) in candidates do
    if thm_head == head then
      if let some result ← Simp.tryTheoremWithExtraArgs? e thm numExtraArgs then
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

section ElabHead
open Elab Term

/-- Return `true` if `stx` is an underscore, i.e. `_` or `fun $_ => _`/`fun $_ ↦ _`. -/
partial def isUnderscore : Term → Bool
  | `(_) | `(fun $_ => _) => true
  | _ => false

/-- `resolvePushId?` is a version of `resolveId?` that also supports notations like `_ ∈ _`,
`∃ x, _` and `∑ x, _`. -/
def resolvePushId? (stx : Term) : TermElabM (Option Expr) := do
  match ← liftMacroM <| expandMacros stx with
  | `($f $args*) =>
    -- Note: we would like to insist that all arguments in the notation are given as underscores,
    -- but for example `∑ x, _` expands to `Finset.sum Finset.univ fun _ ↦ _`,
    -- in which `Finset.univ` is not an underscore. So instead
    -- we only insist that the last argument is an underscore.
    if args.back?.all isUnderscore then
      try resolveId? f catch _ => return none
    else
      return none
  | `(binop% $f _ _)
  | `(binop_lazy% $f _ _)
  | `(leftact% $f _ _)
  | `(rightact% $f _ _)
  | `(binrel% $f _ _)
  | `(binrel_no_prop% $f _ _)
  | `(unop% $f _)
  | f => try resolveId? f catch _ => return none

/-- Elaborator for the argument passed to `push`. It accepts a constant, or a function -/
def elabHead (stx : Term) : TermElabM Head := withRef stx do
  -- we elaborate `stx` to get an appropriate error message if the term isn't well formed,
  -- and to add hover information
  _ ← withTheReader Term.Context ({ · with ignoreTCFailures := true }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| Term.withoutErrToSorry <| Term.elabTerm stx none
  match stx with
  | `(fun $_ => _) => return .lambda
  | `(∀ $_, _) => return .forall
  | _ =>
    match ← resolvePushId? stx with
    | some (.const c _) => return .const c
    | _ => throwError "Could not resolve `push` argument {stx}. \
      Expected either a constant, e.g. `push Not`, \
      or notation with underscores, e.g. `push ¬ _`"

end ElabHead

/-- Elaborate the `(disch := ...)` syntax for a `simp`-like tactic. -/
def elabDischarger (stx : TSyntax ``discharger) : TacticM Simp.Discharge :=
  (·.2) <$> tacticToDischarge stx.raw[3]

/--
`push` pushes the given constant away from the head of the expression. For example
- `push _ ∈ _` rewrites `x ∈ {y} ∪ zᶜ` into `x = y ∨ ¬ x ∈ z`.
- `push (disch := positivity) Real.log` rewrites `log (a * b ^ 2)` into `log a + 2 * log b`.
- `push ¬ _` is the same as `push_neg` or `push Not`, and it rewrites
  `¬ ∀ ε > 0, ∃ δ > 0, δ < ε` into `∃ ε > 0, ∀ δ > 0, ε ≤ δ`.

In addition to constants, `push` can be used to push `fun` and `∀` binders:
- `push fun _ ↦ _` rewrites `fun x => f x ^ 2 + 5` into `f ^ 2 + 5`
- `push ∀ _, _` rewrites `∀ a, p a ∧ q a` into `(∀ a, p a) ∧ (∀ a, q a)`.

The `push` tactic can be extended using the `@[push]` attribute.

To instead move a constant closer to the head of the expression, use the `pull` tactic.

To push a constant at a hypothesis, use the `push ... at h` or `push ... at *` syntax.
-/
elab (name := push) "push" disch?:(discharger)? head:(ppSpace colGt term) loc:(location)? :
    tactic => do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (pushCore head · disch?) "push" loc (failIfUnchanged := true) false

/--
Push negations into the conclusion or a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Binder names are preserved.

`push_neg` is a special case of the more general `push` tactic, namely `push Not`.
The `push` tactic can be extended using the `@[push]` attribute. `push` has special-casing
built in for `push Not`, so that it can preserve binder names, and so that `¬ (p ∧ q)` can be
transformed to either `p → ¬ q` (the default) or `¬ p ∨ ¬ q`. To get `¬ p ∨ ¬ q`, use
`set_option push_neg.use_distrib true`.

Another example: given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|
```
Note that binder names are preserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢`, as usual.
-/
macro (name := push_neg) "push_neg" loc:(location)? : tactic => `(tactic| push Not $[$loc]?)

/--
`pull` is the inverse tactic to `push`.
It pulls the given constant towards the head of the expression. For example
- `pull _ ∈ _` rewrites `x ∈ y ∨ ¬ x ∈ z` into `x ∈ y ∪ zᶜ`.
- `pull (disch := positivity) Real.log` rewrites `log a + 2 * log b` into `log (a * b ^ 2)`.
- `pull fun _ ↦ _` rewrites `f ^ 2 + 5` into `fun x => f x ^ 2 + 5` where `f` is a function.

A lemma is considered a `pull` lemma if its reverse direction is a `push` lemma
that actually moves the given constant away from the head. For example
- `not_or : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q` is a `pull` lemma, but `not_not : ¬ ¬ p ↔ p` is not.
- `log_mul : log (x * y) = log x + log y` is a `pull` lemma, but `log_abs : log |x| = log x` is not.
- `Pi.mul_def : f * g = fun (i : ι) => f i * g i` and `Pi.one_def : 1 = fun (x : ι) => 1` are both
  `pull` lemmas for `fun`, because every `push fun _ ↦ _` lemma is also considered a `pull` lemma.

TODO: define a `@[pull]` attribute for tagging `pull` lemmas that are not `push` lemmas.
-/
elab (name := pull) "pull" disch?:(discharger)? head:(ppSpace colGt term) loc:(location)? :
    tactic => do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (pullCore head · disch?) "pull" loc (failIfUnchanged := true) false

/-- A simproc variant of `push fun _ ↦ _`, to be used as `simp [↓pushFun]`. -/
simproc_decl _root_.pushFun (fun _ ↦ ?_) := pushStep .lambda

/-- A simproc variant of `pull fun _ ↦ _`, to be used as `simp [pullFun]`. -/
simproc_decl _root_.pullFun (_) := pullStep .lambda

section Conv

@[inherit_doc push]
elab "push" disch?:(discharger)? head:(ppSpace colGt term) : conv => withMainContext do
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
macro (name := pushCommand) tk:"#push " head:ident ppSpace e:term : command =>
  `(command| #conv%$tk push $head:ident => $e)

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNegCommand) tk:"#push_neg " e:term : command => `(command| #push%$tk Not $e)

@[inherit_doc pull]
elab "pull" disch?:(discharger)? head:(ppSpace colGt term) : conv => withMainContext do
  let disch? ← disch?.mapM elabDischarger
  let head ← elabHead head
  Conv.applySimpResult (← pullCore head (← instantiateMVars (← Conv.getLhs)) disch?)

/--
The syntax is `#pull head e`, where `head` is a constant and `e` is an expression,
which will print the `pull head` form of `e`.

`#pull` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pullCommand) tk:"#pull " head:ident ppSpace e:term : command =>
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
      | .const c _, .const c' => c == c'
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
