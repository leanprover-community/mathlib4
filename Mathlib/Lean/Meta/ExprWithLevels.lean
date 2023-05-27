/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Mathlib.Lean.Meta.Basic

/-!

# ExprWithLevels

The functionality provided by this file is meant to emulate a "universe-polymorphic expression".
That is, we'd like to write something like `fun {u : Level} {v : Level} ... => body`, but Lean
doesn't allow this to work the way we'd like—`u`, `v`, etc. can't be used as universes in `body`.
Lean doesn't allow bound universe variables; instead, each level parameter ``u := .param `u`` only
functions as a free universe variable.

Instead, Lean only allows level parameters to be attached to constants, and level parameters for a
given constant `const` are stored in `← getConstInfo f`. The resulting `ConstantInfo` (which has a
field `.params`) effectively fulfills the role of "binding" the level params (i.e. free universe
variables) in `f` at the meta level.

An `ExprWithLevels` follows this pattern, and simply packages an array of level params (as `Name`s)
with an `Expr`. The provided API for handling an `e : ExprWithLevels` effectively treats `e` as a
lambda with body `e.expr` and implicit level arguments `e.params`. E.g., we can appropriately
replacing these with level mvars when constructing an application of such a lambda, then re-bind
the mvars that didn't get assigned.

-/

open Lean Expr Meta

namespace Lean.Meta

/-- A "universe-polymorphic" expression. `{ expr, params } : ExprWithLevels` should be thought of
as a lambda `fun {params} => expr`, with the levels named by `params` being bound in `expr` and
regarded as implicit arguments. Displayed as `lfun params => expr` in `MessageData`. -/
structure ExprWithLevels where
  expr   : Expr
  params : Array Name
deriving Repr

instance : ToMessageData ExprWithLevels where
  toMessageData e := "lfun " ++ toMessageData e.params ++ " => " ++ toMessageData e.expr

/-- Given some `e : Expr`, create an `ExprWithLevels` with no level param arguments. -/
def _root_.Lean.Expr.toExprWithLevels (e : Expr) : ExprWithLevels := ⟨e,#[]⟩

namespace ExprWithLevels

/-- Apply `f` to the body of some `ExprWithLevels`. -/
def map : (e : ExprWithLevels) → (f : Expr → Expr) → ExprWithLevels
| ⟨expr, params⟩, f => ⟨f expr, params⟩

/-- Apply `f` to the body of some `ExprWithLevels`. -/
def mapM [Monad m] : (e : ExprWithLevels) → (f : Expr → m Expr) → m ExprWithLevels
| ⟨expr, params⟩, f => return ⟨← f expr, params⟩

/-- Checks if some `e : ExprWithLevels` represents a "constant" function in its bound level params.
I.e., that no level param in `e.expr` is contained in `e.params`. -/
def isConstantInLevelArgs (e : ExprWithLevels) : Bool :=
  ! (collectLevelParams {} e.expr |>.params.any e.params.contains)

/-- Removes parameter arguments which are unused in `(e : ExprWithLevels).expr`. -/
def removeConstantLevelArgs : ExprWithLevels → ExprWithLevels
| ⟨expr, params⟩ => ⟨expr, params.filter (collectLevelParams {} expr |>.params.contains)⟩

/-- Returns the body of an `ExprWithLevels` if `params` is empty. -/
def toExpr? (e : ExprWithLevels) : Option Expr := if e.params.isEmpty then some e.expr else none

/-- Returns the body of an `ExprWithLevels` if `params` is empty or if `ExprWithLevels` represents
a constant function with respect to `params`. -/
def toExpr'? (e : ExprWithLevels) : Option Expr :=
  if e.params.isEmpty || e.isConstantInLevelArgs then some e.expr else none

/-- A low-level "environment" used to associate "variables" (parameter names) to level
metavariables. Used when "telescoping" an `ExprWithLevels`.

We maintain the following assumptions:

* All elements of `levels` are level metavariables.
* `env.params.size == env.levels.size`; this lets us avoid extra zipping and unzipping compared to
  using an `Array (Name × Level)`. -/
structure Environment where
  params : Array Name
  levels : Array Level
deriving Repr

instance : EmptyCollection Environment := ⟨⟨#[],#[]⟩⟩

instance : ToMessageData Environment where
  toMessageData env :=
    let a := env.params.zipWith env.levels fun p l => toMessageData p ++ " ↤ " ++ toMessageData l
    MessageData.ofArray a

/-- Instantiate all bound level params in the body of an `ExprWithLevels` with fresh level
metavariables. Returns the resulting expression along with an environment associating the original
bound level params to the fresh metavariables.  -/
def levelMetaTelescope : ExprWithLevels → MetaM (Environment × Expr)
| ⟨expr, params⟩ => do
  let levels ← mkFreshLevelMVarsArray params.size
  return ({ params, levels }, expr.instantiateLevelParamsArray params levels)

/-- Assigns any unassigned level mvars in the `Environment` to their corresponding level param,
effectively "abstracting the levels out" into the parameter names, which repesent "bound" universe
variables. -/
def abstractEnvironment {m : Type → Type} [Monad m] [MonadMCtx m] : Environment → m (Array Name)
| { params, levels } => do
  let mut unresolvedParams : Array Name := #[]
  for i in [: levels.size] do
    match levels[i]! with
    | .mvar mvarId => do
      if ! (← isLevelMVarAssigned mvarId) then
        let p := params[i]!
        assignLevelMVar mvarId (.param p)
        unresolvedParams := unresolvedParams.push p
    | l => panic! s!"{l} was expected to be a level mvar"
  pure unresolvedParams

/-- Abstract out the unassigned level mvars in `e` according to the environment `env`.

Note that this does not prevent capture of any level params in `e` which might clash with the level
params in `env`. -/
def abstract (env : Environment) (e : Expr) {m : Type → Type} [Monad m] [MonadMCtx m]
    : m ExprWithLevels := do
  let params ← abstractEnvironment env
  pure ⟨← instantiateMVars e, params⟩

/-- Abstract out the unassigned level mvars in `e` according to the environment `env`, ignoring
params which no longer appear in the resulting expression. -/
def abstract' (env : Environment) (e : Expr) {m : Type → Type} [Monad m] [MonadMCtx m]
    : m ExprWithLevels :=
  return removeConstantLevelArgs (← abstract env e)

/-- Abstract out the unassigned level mvars in `e` according to the environment `env`.

This avoids capture of level params in `e` which might clash with those in `env`, renaming the
params in `env` as necessary. -/
def abstractAvoidingCapture (env : Environment) (e : Expr) {m : Type → Type} [Monad m] [MonadMCtx m]
    : m ExprWithLevels := do
  let eParams := collectLevelParams {} e
  let newParams := env.params.map fun p =>
    match eParams.getUnusedLevelParam p with
    | .param n => n
    | l => panic! s!"expected {l} to be a level param"
  let env := { env with params := newParams }
  let params ← abstractEnvironment env
  pure ⟨← instantiateMVars e, params⟩

section Combinators

variable [MonadControlT MetaM m] [Monad m]

@[inline] private def mapWithLevelsMetaM
    (f : forall {α}, ((β → γ → MetaM δ) → β' → γ' → MetaM α) → MetaM α) {α}
    (k : (β → γ → m δ) → β' → γ' → m α) : m α :=
  controlAt MetaM fun runInBase => f fun d b' c' =>
    runInBase <| k (fun b c => liftWith fun _ => d b c) b' c'

/-- Evaluates `k := fun abstract' env e' => ...` on the body `e'` of `e`, with the level params of
`e` having been replaced by metavariables according to `env`.

The arguments `abstract'` and `env` of `k` can be used within the body of `k` to "re-bind" any of
these level metavariables that appear in some `x : Expr` to obtain an `ExprWithLevels`, e.g.
`abstract' env x`. The argument `abstract` will be lifted to fulfill this functionality
(`ExprWithLevels.abstract` by default). -/
def withLevels (e : ExprWithLevels)
    (k : (Environment → Expr → m ExprWithLevels) → Environment → Expr → m α)
    (abstract := (abstract (m := MetaM))) : m α :=
  mapWithLevelsMetaM
    (fun k => do let (env, expr) ← levelMetaTelescope e; k abstract env expr) k

/-- Evaluates `k := fun env e' => ...` on the body `e'` of `e`, with the level params of `e` having
been replaced by metavariables according to `env`.

The remaining unassigned level metavariables in the `Expr` produced by `k` will be abstracted out
into an `ExprWithLevels` by `abstract`. -/
def withLevelsExpr (e : ExprWithLevels) (k : Environment → Expr → m Expr)
    (abstract := (abstract (m := MetaM))) : m ExprWithLevels :=
  withLevels e (abstract := abstract) fun abstract env expr => do abstract env (← k env expr)

/-- Evaluates `k := fun env e' => ...` on the body `e'` of `e`, with the level params of `e` having
been replaced by metavariables according to `env`.

The remaining unassigned level metavariables in the `Expr` produced in the first component of `k`'s
output will be abstracted out into an `ExprWithLevels` by `abstract`. -/
def withLevelsExpr' (e : ExprWithLevels) (k : Environment → Expr → m (Expr × α))
    (abstract := abstract (m := MetaM)) : m (ExprWithLevels × α) :=
  withLevels e (abstract := abstract) fun abstract env expr => do
    let (e, a) ← k env expr
    pure (← abstract env e, a)

end Combinators
