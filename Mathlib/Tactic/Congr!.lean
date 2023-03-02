/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Tactic.Relation.Rfl

/-!
# The `congr!` tactic

This is a more powerful version of the `congr` tactic.
-/

open Lean Meta Elab Tactic

/--
Asserts the given congruence theorem as fresh hypothesis, and then applies it.
Return the `fvarId` for the new hypothesis and the new subgoals.
-/
private def applyCongrThm? (mvarId : MVarId) (congrThmType congrThmProof : Expr) :
    MetaM (List MVarId) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

/--
Try applying user-provided congruence lemmas. If any are applicable,
returns a list of new goals.
-/
def Lean.MVarId.userCongr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, _) := (← mvarId.getType').eqOrIff? | return none
    let some name := lhs.getAppFn.cleanupAnnotations.constName? | return none
    let congrTheorems := (← getSimpCongrTheorems).get name
    -- Note: congruence theorems are in provided in decreasing order of priority.
    for congrTheorem in congrTheorems do
      let res ← observing? do
        let cinfo ← getConstInfo congrTheorem.theoremName
        let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let proof := mkConst congrTheorem.theoremName us
        let ptype ← instantiateTypeLevelParams cinfo us
        applyCongrThm? mvarId ptype proof
      if let some mvars := res then
        return mvars
    return none

/--
Try to convert an `Iff` into an `Eq` by applying `iff_of_eq`.
If successful, returns the new goal, and otherwise returns the original `MVarId`.
-/
def Lean.MVarId.iffOfEq (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    let some [mvarId] ← observing? do mvarId.apply (mkConst `iff_of_eq []) | return mvarId
    return mvarId

/--
Try to convert an `Eq` into an `Iff` by applying `propext`.
If successful, then returns then new goal, otherwise returns the original `MVarId`.
-/
def Lean.MVarId.propext (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    let some [mvarId] ← observing? do mvarId.apply (mkConst ``propext []) | return mvarId
    return mvarId

/-- Helper theorem for `LEan.MVar.liftReflToEq`. -/
theorem Lean.MVarId.rel_of_eq_and_refl {R : α → α → Prop} (hxy : x = y) (h : R x x) :
    R x y := hxy ▸ h

/--
Use a `refl`-tagged lemma to convert the goal into an `Eq`. If this can't be done, returns
the original `MVarId`.
-/
def Lean.MVarId.liftReflToEq (mvarId : MVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `liftReflToEq
  let tgt ← withReducible <| mvarId.getType'
  let .app (.app rel _) _ := tgt | return mvarId
  if rel.isAppOf `Eq then
    -- No need to lift Eq to Eq
    return mvarId
  let reflLemmas ← (Mathlib.Tactic.reflExt.getState (← getEnv)).getMatch rel
  for lem in reflLemmas do
    let res ← observing? do
      -- First create an equality relating the LHS and RHS
      -- and reduce the goal to proving that LHS is related to LHS.
      let [mvarIdEq, mvarIdR] ←
            mvarId.apply (← mkConstWithFreshMVarLevels ``Lean.MVarId.rel_of_eq_and_refl)
        | failure
      -- Then fill in the proof of the latter by reflexivity.
      let [] ← mvarIdR.apply (← mkConstWithFreshMVarLevels lem) | failure
      return mvarIdEq
    if let some mvarId := res then
      return mvarId
  return mvarId

/--
Try to close the goal using `Subsingleton.elim`. Returns whether or not it succeeds.
-/
def Lean.MVarId.subsingletonElim (mvarId : MVarId) : MetaM Bool := do
  let some [] ← observing? do mvarId.apply (mkConst ``Subsingleton.elim [← mkFreshLevelMVar])
    | return false
  return true

def Lean.MVarId.proofIrrelHeq (mvarId : MVarId) : MetaM Bool := do
  let some [] ← observing? do mvarId.apply (mkConst `proof_irrel_heq [])
    | return false
  return true

/--
Try to apply `pi_congr`. This is similar to `Lean.MVar.congrImplies?`.
-/
def Lean.MVarId.congrPi? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)

/--
Try to apply `funext`, but only if it is an equality of two functions where at least one is
a lambda expression.
One thing this check prevents is accidentally applying `funext` to a set equality, but also when
doing congruence we don't want to apply `funext` unnecessarily.
"Obvious" means that the type of the terms being equated is a pi type.
-/
def Lean.MVarId.obviousFunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let tgt ← mvarId.getType'
    let some (_, lhs, rhs) := tgt.eq? | failure
    if not lhs.isLambda && not rhs.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)

/--
Try to apply `Function.hfunext`, returning the new goals if it succeeds.
Like `Lean.MVarId.obviousFunext?`, we only do so if at least one side of the `HEq` is a
lambda. This is to prevent unfolding of things like `Set`.
-/
def Lean.MVarId.obviousHfunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let tgt ← mvarId.getType'
    let some (_, _, lhs, rhs) := tgt.heq? | failure
    if not lhs.isLambda && not rhs.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)

/-- The list of passes used by `Lean.MVarId.congrCore!`. -/
def Lean.MVarId.congrPasses! : List (MVarId → MetaM (Option (List MVarId))) :=
  [userCongr?, congr?, hcongr?, obviousFunext?, obviousHfunext?, congrImplies?, congrPi?]

/-- Convert a goal into an `Eq` goal if possible (since we have a better shot at those).
Also try to dispatch the goal using an assumption, `Subsingleton.Elim`, or definitional equality. -/
def Lean.MVarId.preCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  -- User congr lemmas might have created additional hypotheses.
  let (_, mvarId) ← mvarId.intros
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  -- This is a good time to check whether we have a relevant hypothesis.
  if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  -- Now try definitional equality. No need to try `mvarId.hrefl` since we already did  `heqOfEq`.
  try mvarId.refl; return none catch _ => pure ()
  -- Now we go for (heterogenous) equality via subsingleton considerations
  if ← mvarId.subsingletonElim then return none
  if ← mvarId.proofIrrelHeq then return none
  return some mvarId

def Lean.MVarId.congrCore! (mvarId : MVarId) : MetaM (List MVarId) := do
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want it to stick
     if there are no relevant congr lemmas. -/
  let mvarId ← mvarId.liftReflToEq
  for pass in congrPasses! do
    if let some mvarIds ← pass mvarId then
      return mvarIds
  throwTacticEx `congr! mvarId "failed to apply congruence"

/-- A pass to clean up after `Lean.MVarId.preCongr!` and `Lean.MVarId.congrCore!`. -/
def Lean.MVarId.postCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  let some mvarId ← mvarId.preCongr! | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if ← mvarId.assumptionCore then return none
  return some mvarId

/-- A more insistent version of `Lean.MVarId.congrN`. -/
def Lean.MVarId.congrN! (mvarId : MVarId) (depth : Nat := 1000000) : MetaM (List MVarId) := do
  let (_, s) ← go depth mvarId |>.run #[]
  return s.toList
where
  post (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← mvarId.postCongr! | return
    modify (·.push mvarId)
  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← withReducible mvarId.preCongr! | return
    match n with
      | 0 => post mvarId
      | n + 1 =>
        let some mvarIds ← observing? (m := MetaM) mvarId.congrCore!
          | post mvarId
        mvarIds.forM (go n)

/--
Apply congruence (recursively) to goals that have some notion of a left-hand side and a
right-hand side, for example `⊢ f as = f bs` or `⊢ R (f as) (f bs)` where `R` is a reflexive
relation. It also applies functional extensionality and propositional extensionality lemmas, as
well as using `Subsingleton.elim` and `assumption` to dispatch goals.

In general, `congr!` aims be able to break up equalities to navigate into arbitrary subterms.
Everything `simp` is able to rewrite should be doable using `congr!` and `rw`.

The optional parameter is the depth of the recursive applications.
This is useful when `congr!` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr!` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr! 2` produces the intended `⊢ x + y = y + x`.
-/
syntax (name := congr!) "congr! " (num)? : tactic

elab_rules : tactic
| `(tactic| congr! $[$n]?) =>
  let hugeDepth := 1000000
  let depth := n.map (·.getNat) |>.getD hugeDepth
  liftMetaTactic fun g ↦ g.congrN! depth
