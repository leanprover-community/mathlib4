/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Cases
public import Mathlib.Util.AtomM
public meta import Lean.Meta.Tactic.Generalize

/-!
# The `basify` tactic

Mathlib has many types built from a well-behaved type by a construction that makes the resulting
arithmetic partial or truncated. The two commonest are

* *extensions* by a point at infinity, such as `ℕ∞ = WithTop ℕ`;
* *subtypes* cut out by an inequality, such as `ℝ≥0 = {r : ℝ // 0 ≤ r}`.

Goals about them are painful, because the decision procedures one would like to use (`grind`,
`linarith`, `norm_num`) only understand the underlying type. `basify`
peels the construction off, turning the goal into an equivalent one about that type:

```
example (a b : ℝ≥0∞) (h : a + b = 0) : a = 0 := by
  basify
  -- goal now: a : ℝ, a_nonneg : 0 ≤ a, b : ℝ, b_nonneg : 0 ≤ b, h : a + b = 0 ⊢ a = 0
  linarith
```

## Implementation

We proceed in three phases.

1. We traverse the goal and the hypotheses and collect the *atoms*: the subexpressions of a
  compound type, the type we are going to shift to its base type. A compound type is one
  registered with `@[basify_elim]`. During the search we look through operations that can
  themselves be translated to the base type, so in `a + b` with `a b : ℝ≥0∞` we collect `a` and
  `b` rather than the sum; such operations are registered with `@[basify_op]`.
2. We iterate through the atoms, applying `cases` to each with the eliminator tagged
  `@[basify_elim]`. That sometimes leaves several goals, and often (for `ℕ∞` and `ℝ≥0∞`) the ones
  mentioning an infinity are typically trivial, so we run the `basify_simp` simp set after every
  split to discharge them early and keep the branching from blowing up.
3. We finish the descent with a final `simp_all only [basify_simp]`, which uses the hypotheses to
  discharge the side conditions of the conditional cast lemmas.

## Relation to other tactics

`basify` achieves what `zify`/`qify`/`rify` achieve -- propositions shifted to a type where the
arithmetic is total -- but not in the same way: those leave every variable's type alone, whereas
`basify` destructs the variables, so an `ℝ≥0` hypothesis really does become an `ℝ` one paired with
`0 ≤ ·`. In that respect it is closer to `lift`. The name says "the base type" rather than a fixed
one because the target depends on what is registered: `ℕ` for `ℕ∞`, `ℝ` for `ℝ≥0∞`.

* `rify` already covers `ℝ≥0 → ℝ`, and `linarith` ships a preprocessor doing the same shift with
  the nonnegativity facts. On a goal stated purely in `ℝ≥0` those usually suffice; `basify` earns
  its keep there only on truncated subtraction, which it rewrites with `NNReal.coe_sub_def`.
* `lift` is the per-variable version of the interesting branch of a split: `lift a to ℝ≥0 using ha`
  is what one writes by hand once `a ≠ ⊤` is known. `basify` splits on it instead, and discharges
  the other branch.
* `norm_cast` removes coercions and therefore lands in the *smallest* type of a cast tower, which
  for `ℝ≥0∞` is `ℝ≥0`, not `ℝ`. Reaching `ℝ` means travelling down one coercion and up another,
  which is why `basify_simp` holds `←` lemmas for the extension layer and forward ones for the
  subtype layer.

The case split has no counterpart elsewhere: `⊤ - a` is not a cast-normalisation problem, and no
amount of rewriting turns it into one.

## Extending the tactic

Three attributes drive the tactic, so that a new construction needs no change to this file:

* `@[basify_elim]` marks an eliminator; the type it destructs and the shape of each of its cases
  are read off from its type.
* `@[basify_op]` marks the lemma relating an operation of a compound type to the corresponding
  operation below, such as `ENNReal.coe_add : ↑(a + b) = ↑a + ↑b`. It records the operation and
  adds the lemma to `basify_simp`, reversed if `←` is given -- the direction the coercion has to
  travel, outwards for a `WithTop` layer and inwards for a subtype.
* `@[basify_simp]` is the simp set described above, for everything that is not an operation:
  relations such as `ENNReal.coe_inj`, and the lemmas that clear away infinities.

`Mathlib/Tactic/Basify/ENNReal.lean` is a worked example using all three.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Basify

/-! ### Propositional cleanup

The `basify_simp` simp set is run with `simp only`, so it has to carry the handful of
propositional lemmas needed to actually make a contradictory branch disappear.
-/

attribute [basify_simp] ne_eq not_true_eq_false not_false_eq_true eq_self_iff_true
  true_and and_true and_self true_or or_true or_self true_iff iff_true implies_true forall_const

/-! ### Atoms -/

/-- The eliminator registered for the type `ty`, if any. -/
def elimEntryFor? (ty : Expr) : MetaM (Option ElimEntry) := do
  let some tyName := ty.getAppFn.constName? | return none
  return (elimExt.getState (← getEnv)).find? tyName

/-- The operations registered for the type `ty`, i.e. the applications of type `ty` that
`basify` looks inside of instead of treating as atoms. -/
def opsFor (ty : Expr) : MetaM NameSet := do
  let some tyName := ty.getAppFn.constName? | return ∅
  return (opExt.getState (← getEnv)).find? tyName |>.getD ∅

/-- Does `basify` know anything about the type `ty`? -/
def isRegisteredType (ty : Expr) : MetaM Bool := return (← elimEntryFor? ty).isSome

/-- Is `e` an atom, i.e. a term of a registered type that `basify` cannot see inside of?

A term of a registered type is *not* an atom when its head is an operation registered with
`@[basify_op]`, in which case its arguments are visited instead. Everything else is opaque and gets
generalized and case split as a whole. -/
def isAtom (e : Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← inferType e)
  unless ← isRegisteredType ty do return false
  let some head := e.getAppFn.constName? | return true
  return !(← opsFor ty).contains head

/-- Collect the atoms of `e` -/
partial def collectAtoms (e : Expr) : AtomM Unit := do
  -- we traverse subexpressions under binders too, and check there's no loose bound variables
  if !e.hasLooseBVars then
    if ← isAtom e then
      discard <| AtomM.addAtom e
      return
  match e with
  | .app .. =>
    unless e.getAppFn.isConst do collectAtoms e.getAppFn
    for a in e.getAppArgs do
      collectAtoms a
  | .lam _ t b _ | .forallE _ t b _ => collectAtoms t; collectAtoms b
  | .letE _ t v b _ => collectAtoms t; collectAtoms v; collectAtoms b
  | .mdata _ b | .proj _ _ b => collectAtoms b
  | _ => pure ()

/-- All the atoms of the goal `g`, taken from the target and from every hypothesis. -/
def goalAtoms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  -- we use `instances` transparency because that's what `generalizeHyp` later uses
  AtomM.run .instances do
    collectAtoms (← instantiateMVars (← g.getType))
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      collectAtoms (← instantiateMVars decl.type)
    return (← get).atoms

/-! ### The phases -/

/-- Generalize the single atom `e`, naming the new variable `x`-something and its defining equation
that name with `_eq` appended. Returns the substitution for the hypotheses that were reverted along
the way, the new variable, and the new goal. -/
private def generalizeAtom (g : MVarId) (e : Expr) :
    MetaM (FVarSubst × FVarId × MVarId) := g.withContext do
  -- We pass `hName?` to create a hypothesis connecting the new variable with the original term.
  let arg : GeneralizeArg := { expr := e, hName? := ← mkFreshUserName `h }
  let hyps : Array FVarId := (← getLCtx).foldl (init := #[]) fun hyps decl =>
    if decl.isImplementationDetail then hyps else hyps.push decl.fvarId
  let (subst, introduced, g) ← g.generalizeHyp #[arg] hyps
  let #[var, eqFVarId] := introduced |
    panic! "`generalize` did not introduce exactly one variable and one equation"
  let name ← g.withContext do return (← getLCtx).getUnusedName `x
  let g ← g.rename var name
  let g ← g.withContext do g.rename eqFVarId ((← getLCtx).getUnusedName (name.appendAfter "_eq"))
  return (subst, var, g)

/-- Turn every atom of `g` into a variable that can be case split, generalizing the ones that are
not variables already and keeping their defining equation as `<name>_eq`. Returns those
variables. -/
def generalizeAtoms (g : MVarId) : MetaM (MVarId × Array FVarId) := g.withContext do
  let (varAtoms, termAtoms) := (← goalAtoms g).partition Expr.isFVar
  let mut g := g
  let mut vars := varAtoms.map Expr.fvarId!
  let mut atomsToGeneralize := termAtoms
  for i in [0:atomsToGeneralize.size] do
    -- `generalizeHyp` throws when the abstracted goal is not type correct, having already assigned
    -- `g` to revert the hypotheses. `observing?` rolls that back, so an atom that cannot be
    -- generalized is skipped.
    let some (subst, var, g') ← observing? (generalizeAtom g atomsToGeneralize[i]!) | continue
    g := g'
    -- `generalizeHyp` renumbers the context, so both the variables recorded so far
    -- and the atoms still to come have to be mapped through `subst` before they are used again.
    vars := (vars.map (subst.get · |>.fvarId!)).push var
    atomsToGeneralize := atomsToGeneralize.map subst.apply
  return (g, vars)

/-- The names for what an alternative introduces: the binder carrying the value takes `base`, the
others take `base` with their own name appended verbatim, so a binder `_pos` yields `x_pos`.
Without a `base` everything stays anonymous. -/
private def altNames (base? : Option Name) (binders : Array (Option Name)) : MetaM (List Name) := do
  let some base := base? | binders.toList.mapM fun _ => mkFreshUserName `x
  return binders.toList.map fun
    | none => base
    | some binder => base.appendAfter binder.toString

/-- Case split `fvarId` with the eliminator `entry.elimName`, naming what each alternative
introduces after `fvarId` itself. Returns one goal per alternative, each paired with the variables
that alternative introduced. -/
def casesAtom (g : MVarId) (fvarId : FVarId) (entry : ElimEntry) :
    TacticM (List (MVarId × Array FVarId)) := do
  -- `cases fvarId using entry.elimName` at the `Expr` level, adapted from `Mathlib.Tactic.cases'`.
  let (base?, result, targets, motive) ← g.withContext do
    let elimInfo ← getElimInfo entry.elimName
    let name ← fvarId.getUserName
    let base? := if name.hasMacroScopes then none else some name
    let targets ← addImplicitTargets elimInfo #[.fvar fvarId]
    let result ← ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    return (base?, result, targets, elimArgs[elimInfo.motivePos]!)
  let g ← g.withContext do generalizeTargetsEq g (← inferType motive) targets
  let (targetsNew, g) ← g.introN targets.size
  g.withContext do
    ElimApp.setMotiveArg g motive.mvarId! targetsNew
    g.assign result.elimApp
    let mut goals := #[]
    for alt in result.alts, binders in entry.altBinders do
      let (introduced, g) ← alt.mvarId.introN binders.size (← altNames base? binders)
      let some (g, subst) ← Cases.unifyEqs? targets.size g {} | continue
      let g ← targetsNew.foldlM (fun g fv => do return ← g.tryClear fv) g
      -- `unifyEqs?` may have rewritten the new variables, so follow its substitution.
      goals := goals.push (g, introduced.filterMap fun fvarId =>
        match subst.get fvarId with | .fvar fvarId => some fvarId | _ => none)
    return goals.toList

/-- Remove the `True` hypotheses that `simp only ... at *` leaves behind. -/
def clearTrivialHypotheses (g : MVarId) : MetaM MVarId := g.withContext do
  g.tryClearMany <| ← (← getLCtx).foldlM (init := #[]) fun fvarIds decl => do
    if decl.isImplementationDetail then return fvarIds
    return if (← instantiateMVars decl.type).isTrue then fvarIds.push decl.fvarId else fvarIds

/-- The main loop of the `basify` tactic: case split the variables in `varsToElim` one at a time,
running the `basify_simp` simp set after each so that the degenerate branches (`⊤ + a = ⊤` and
friends) die before the branching explodes. -/
partial def basifyLoop (g : MVarId) (varsToElim : List FVarId) : TacticM (List MVarId) := do
  let fvarId :: varsToElim := varsToElim | return [g]
  let entry? : Option ElimEntry ← g.withContext do
    let some decl := (← getLCtx).find? fvarId | return none
    elimEntryFor? (← instantiateMVars decl.type)
  let some entry := entry? | basifyLoop g varsToElim
  let mut result := []
  for (branch, newVars) in ← casesAtom g fvarId entry do
    setGoals [branch]
    evalTactic (← `(tactic| try simp only [basify_simp] at *))
    for g in ← getGoals do
      let g ← clearTrivialHypotheses g
      -- What a split introduces goes to the front, so each atom descends all the way --
      -- `ℝ≥0∞ → ℝ≥0 → ℝ` -- before the next one is touched.
      result := result ++ (← basifyLoop g (newVars.toList ++ varsToElim))
  return result

/--
`basify` removes the layers that separate a type from the type its arithmetic really lives in,
turning the goal into an equivalent goal about that type: `ℕ∞` and `ℕ+` become `ℕ`, `ℝ≥0` becomes
`ℝ`, and `ℝ≥0∞` becomes `ℝ` by way of `ℝ≥0`.

Every value of a registered type is destructed with the eliminator registered for it -- `⊤` or
`↑x` for an extension such as `ℕ∞`, `n.toPNat'` together with `0 < n` for a subtype such as `ℕ+`
-- the degenerate branches are discharged, and the surviving propositions are pushed down along
the coercions. The result is then can be finished off by a decision procedure for the underlying
type:

```
example (a b : ℕ∞) (h : a ≤ b) : a - b < b + 1 := by basify; lia
example (a b : ℕ+) (h : a < b) : 1 < b := by basify; lia
example (a b : ℝ≥0) (h : a + b = 0) : a = 0 := by basify; linarith
example (a b c : ℝ≥0∞) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by basify <;> linarith
```

The cast lemmas for division and inverse are conditional, and are discharged from the context, so a
goal using them needs the relevant `≠ 0` to be available; without it the descent stops part-way.

```
example (a : ℝ≥0∞) (h : a ≠ 0) (h' : a ≠ ⊤) : a * a⁻¹ = 1 := by basify; field_simp
```

New types are supported by tagging an eliminator with `@[basify_elim]`, its operations with
`@[basify_op]`, and the relevant rewrite lemmas with `@[basify_simp]`.
-/
elab "basify" : tactic => focus do
  let (g, varsToElim) ← generalizeAtoms (← getMainGoal)
  setGoals (← basifyLoop g varsToElim.toList)
  evalTactic (← `(tactic| all_goals first
    | simp_all only [basify_simp]
    | simp only [basify_simp] at *
    | skip))
  setGoals (← (← getGoals).mapM fun g => do return ← clearTrivialHypotheses g)

end Mathlib.Tactic.Basify
