/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Mario Carneiro, Reid Barton, Johan Commelin
-/

import Mathlib.Util.Tactic
import Mathlib.Logic.Function.Basic

/-!
# `choose` tactic
Performs Skolemization, that is, given `h : ∀ a:α, ∃ b:β, p a b |- G` produces
`f : α → β, hf: ∀ a, p a (f a) |- G`.

TODO: switch to `rcases` syntax: `choose ⟨i, j, h₁ -⟩ := expr`.
-/

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Choose

/-- Given `α : Sort u`, `nonemp : Nonempty α`, `p : α → Prop`, a context of free variables
`ctx`, and a pair of an element `val : α` and `spec : p val`,
`mk_sometimes u α nonemp p ctx (val, spec)` produces another pair `val', spec'`
such that `val'` does not have any free variables from elements of `ctx` whose types are
propositions. This is done by applying `Function.sometimes` to abstract over all the propositional
arguments. -/
def mk_sometimes (u : Level) (α nonemp p : Expr) :
    List Expr → Expr × Expr → MetaM (Expr × Expr)
| [], (val, spec) => pure (val, spec)
| (e :: ctx), (val, spec) => do
  let (val, spec) ← mk_sometimes u α nonemp p ctx (val, spec)
  let t ← inferType e
  let b ← isProp t
  if b then do
    let val' ← mkLambdaFVars #[e] val
    pure
      (mkApp4 (Expr.const ``Function.sometimes [Level.zero, u]) t α nonemp val',
      mkApp7 (Expr.const ``Function.sometimes_spec [u]) t α nonemp p val' e spec)
  else pure (val, spec)

/-- Results of searching for nonempty instances,
to eliminate dependencies on propositions (`choose!`).
`success` means we found at least one instance;
`failure ts` means we didn't find instances for any `t ∈ ts`.
(`failure []` means we didn't look for instances at all.)

Rationale:
`choose!` means we are expected to succeed at least once
in eliminating dependencies on propositions.
-/
inductive ElimStatus
  | success
  | failure (ts : List Expr)

/-- Combine two statuses, keeping a success from either side
or merging the failures. -/
def ElimStatus.merge : ElimStatus → ElimStatus → ElimStatus
  | success, _ => success
  | _, success => success
  | failure ts₁, failure ts₂ => failure (ts₁ ++ ts₂)

/-- `mkFreshNameFrom orig base` returns `mkFreshUserName base` if ``orig = `_``
and `orig` otherwise. -/
def mkFreshNameFrom (orig base : Name) : CoreM Name :=
  if orig = `_ then mkFreshUserName base else pure orig

/-- Changes `(h : ∀ xs, ∃ a:α, p a) ⊢ g` to `(d : ∀ xs, a) ⊢ (s : ∀ xs, p (d xs)) → g` and
`(h : ∀ xs, p xs ∧ q xs) ⊢ g` to `(d : ∀ xs, p xs) ⊢ (s : ∀ xs, q xs) → g`.
`choose1` returns a tuple of

- the error result (see `ElimStatus`)
- the data new free variable that was "chosen"
- the new goal (which contains the spec of the data as domain of an arrow type)

If `nondep` is true and `α` is inhabited, then it will remove the dependency of `d` on
all propositional assumptions in `xs`. For example if `ys` are propositions then
`(h : ∀ xs ys, ∃ a:α, p a) ⊢ g` becomes `(d : ∀ xs, a) (s : ∀ xs ys, p (d xs)) ⊢ g`. -/
def choose1 (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Name) :
    MetaM (ElimStatus × Expr × MVarId) := do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none   => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctx t ↦ do
      (← withTransparency .all (whnf t)).withApp fun
      | .const ``Exists [u], #[α, p] => do
        let data ← mkFreshNameFrom data ((← p.getBinderName).getD `h)
        let ((neFail : ElimStatus), (nonemp : Option Expr)) ← if nondep then
          let ne := (Expr.const ``Nonempty [u]).app α
          let m ← mkFreshExprMVar ne
          let mut g' := m.mvarId!
          for e in ctx do
            if (← isProof e) then continue
            let ty ← whnf (← inferType e)
            let nety := (Expr.const ``Nonempty [u]).app ty
            let neval := mkApp2 (Expr.const ``Nonempty.intro [u]) ty e
            g' ← g'.assert .anonymous nety neval
          (_, g') ← g'.intros
          g'.withContext do
            match ← synthInstance? (← g'.getType) with
            | some e => do
              g'.assign e
              let m ← instantiateMVars m
              pure (.success, some m)
            | none => pure (.failure [ne], none)
        else pure (.failure [], none)
        let ctx' ← if nonemp.isSome then ctx.filterM (not <$> isProof ·) else pure ctx
        let dataTy ← mkForallFVars ctx' α
        let mut dataVal := mkApp3 (.const ``Classical.choose [u]) α p (mkAppN h ctx)
        let mut specVal := mkApp3 (.const ``Classical.choose_spec [u]) α p (mkAppN h ctx)
        if let some nonemp := nonemp then
          (dataVal, specVal) ← mk_sometimes u α nonemp p ctx.toList (dataVal, specVal)
        dataVal ← mkLambdaFVars ctx' dataVal
        specVal ← mkLambdaFVars ctx specVal
        let (fvar, g) ← withLocalDeclD .anonymous dataTy fun d ↦ do
          let specTy ← mkForallFVars ctx (p.app (mkAppN d ctx')).headBeta
          g.withContext <| withLocalDeclD data dataTy fun d' ↦ do
            let mvarTy ← mkArrow (specTy.replaceFVar d d') (← g.getType)
            let newMVar ← mkFreshExprSyntheticOpaqueMVar mvarTy (← g.getTag)
            g.assign <| mkApp2 (← mkLambdaFVars #[d'] newMVar) dataVal specVal
            pure (d', newMVar.mvarId!)
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (neFail, fvar, g)
      | .const ``And _, #[p, q] => do
        let data ← mkFreshNameFrom data `h
        let e1 ← mkLambdaFVars ctx <| mkApp3 (.const ``And.left  []) p q (mkAppN h ctx)
        let e2 ← mkLambdaFVars ctx <| mkApp3 (.const ``And.right []) p q (mkAppN h ctx)
        let t1 ← inferType e1
        let t2 ← inferType e2
        let (fvar, g) ← (← (← g.assert .anonymous t2 e2).assert data t1 e1).intro1P
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (.success, .fvar fvar, g)
      -- TODO: support Σ, ×, or even any inductive type with 1 constructor ?
      | _, _ => throwError "expected a term of the shape `∀ xs, ∃ a, p xs a` or `∀ xs, p xs ∧ q xs`"

/-- A wrapper around `choose1` that parses identifiers and adds variable info to new variables. -/
def choose1WithInfo (g : MVarId) (nondep : Bool) (h : Option Expr) (data : TSyntax ``binderIdent) :
    MetaM (ElimStatus × MVarId) := do
  let n := if let `(binderIdent| $n:ident) := data then n.getId else `_
  let (status, fvar, g) ← choose1 g nondep h n
  g.withContext <| fvar.addLocalVarInfoForBinderIdent data
  pure (status, g)

/-- A loop around `choose1`. The main entry point for the `choose` tactic. -/
def elabChoose (nondep : Bool) (h : Option Expr) :
    List (TSyntax ``binderIdent) → ElimStatus → MVarId → MetaM MVarId
  | [], _, _ => throwError "expect list of variables"
  | [n], status, g =>
    match nondep, status with
    | true, .failure tys => do -- We expected some elimination, but it didn't happen.
      let mut msg := m!"choose!: failed to synthesize any nonempty instances"
      for ty in tys do
        msg := msg ++ m!"{(← mkFreshExprMVar ty).mvarId!}"
      throwError msg
    | _, _ => do
      let (fvar, g) ← match n with
      | `(binderIdent| $n:ident) => g.intro n.getId
      | _ => g.intro1
      g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent n
      return g
  | n::ns, status, g => do
    let (status', g) ← choose1WithInfo g nondep h n
    elabChoose nondep none ns (status.merge status') g

/--
* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```
-/
syntax (name := choose) "choose" "!"? (ppSpace colGt binderIdent)+ (" using " term)? : tactic
elab_rules : tactic
| `(tactic| choose $[!%$b]? $[$ids]* $[using $h]?) => withMainContext do
  let h ← h.mapM (Elab.Tactic.elabTerm · none)
  let g ← elabChoose b.isSome h ids.toList (.failure []) (← getMainGoal)
  replaceMainGoal [g]

@[inherit_doc choose]
syntax "choose!" (ppSpace colGt binderIdent)+ (" using " term)? : tactic
macro_rules
  | `(tactic| choose! $[$ids]* $[using $h]?) => `(tactic| choose ! $[$ids]* $[using $h]?)

end Mathlib.Tactic.Choose
