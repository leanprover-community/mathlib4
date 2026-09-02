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
arithmetic partial or truncated:

* *extensions* by a point at infinity, such as `ℕ∞ = WithTop ℕ` and `ℝ≥0∞ = WithTop ℝ≥0`;
* *subtypes* cut out by an inequality, such as `ℝ≥0 = {r : ℝ // 0 ≤ r}`.

Goals about them are painful, because the decision procedures one would like to use (`lia`,
`linarith`, `nlinarith`, `positivity`, `norm_num`) only understand the underlying type. `basify`
peels the construction off, turning the goal into an equivalent one about that type:

```
example (a b : ℝ≥0∞) (h : a ≤ b) : a - b = 0 := by basify <;> simp_all
```

## Implementation

Both constructions go through one mechanism: case splitting on the eliminator registered with
`@[basify_elim]`. All that distinguishes them is how many cases it has. `ENNReal.recTopCoe` has
two, `⊤` and `↑x` with `x : ℝ≥0`; a subtype's has one, replacing `t : ℝ≥0` by `x.toNNReal` and
handing `0 ≤ x` over as a binder. A subtype is a degenerate case split.

1. The *atoms* of a registered type are collected once and each turned into a variable, since a
   case split needs one to work on: those that are not variables already are generalized, keeping
   the defining equation so that nothing is lost.
2. The variables are destructed one at a time, running `basify_simp` after each so that the
   degenerate branches (`⊤ + a = ⊤` and friends) die *before* the number of branches explodes. A
   split makes fresh variables -- `↑x` gives an `x : ℝ≥0`, itself an atom -- which join the list
   still to do. That is the descent `ℝ≥0∞ → ℝ≥0 → ℝ`, and why the goal is never searched twice.
3. A final `simp_all only [basify_simp]` finishes it, using the hypotheses to discharge the side
   conditions of the conditional cast lemmas. For `ℝ≥0∞` the descent pulls `ℝ≥0 → ℝ≥0∞` coercions
   outwards until they cancel, then pushes `ℝ≥0 → ℝ` coercions inwards until only atoms remain
   under them.

An *atom* is a subterm of a registered type whose head is not an operation registered with
`@[basify_op]`: `a + b` is not one, so the tactic recurses into `a` and `b`, whereas `f x` for an
unregistered `f` is, and gets generalized and split whole. Operations have to be declared rather
than inferred: that `↑a + ↑b` is worth descending into is exactly the content of `ENNReal.coe_add`.

Names come from the eliminator. What a case introduces is named after the atom being split, with
the eliminator's own binder name appended, so splitting `a : ℝ≥0∞` yields `a : ℝ` and
`a_nonneg : 0 ≤ a`. A generalized atom has no name to inherit, so it gets `x` and its equation
`x_eq`.

## Limitations

* Conditional cast lemmas fire only when the context implies their hypothesis: `ℝ≥0∞` division and
  inverse need a `≠ 0` in hand, and without one the descent stops part-way, on a goal belonging to
  neither type. Supplying the fact as a `have` beforehand is the fix.
* Truncated subtraction comes out as `max (a - b) 0`, which `linarith` does not understand; such
  goals usually need a case split on `a ≤ b` afterwards.
* A subterm mentioning a bound variable is never an atom, so `h : ∀ i, f i ≤ 1` is left
  untranslated; instantiating it first is the way round.
* Generalizing keeps the defining equation, so nothing is lost, but a fact true of an atom by
  definition rather than by hypothesis (`ENNReal.ofReal x ≠ ⊤`) is only used if `basify_simp` can
  derive it from that equation.

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
  are read off from its type. It must not produce `Subtype.mk` terms, for the reason given in its
  own docstring.
* `@[basify_op]` marks the lemma relating an operation of a registered type to the corresponding
  operation below, such as `ENNReal.coe_add : ↑(a + b) = ↑a + ↑b`. For a subtype that is the
  statement that the operation agrees with the one upstairs, which has the same shape.
* `@[basify_simp]` is the simp set described above. Like any simp set it accepts `←`, which is what
  the lemmas moving a coercion outwards need.

`Mathlib/Tactic/Basify/ENNReal.lean` is a worked example using all three.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Basify

/-! ### Propositional cleanup

The `basify_simp` simp set is run with `simp only`, so it has to carry the handful of
propositional lemmas needed to actually make a contradictory branch disappear: without
`not_true_eq_false` a hypothesis `⊤ ≠ ⊤` gets stuck at `¬True` instead of closing the goal, and
without `implies_true` a goal under a binder gets stuck at `∀ i, True`.
-/

attribute [basify_simp] ne_eq not_true_eq_false not_false_eq_true eq_self_iff_true
  true_and and_true and_self true_or or_true or_self true_iff iff_true implies_true forall_const

/-! ### Atoms -/

/-- Head symbols that are never atoms whatever the type: a numeric literal is a literal, not an
opaque value that it could make sense to case split on. Every other operation has to be registered
with `@[basify_op]`. -/
private def literalHeads : Array Name :=
  #[``OfNat.ofNat, ``OfScientific.ofScientific]

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

A term of a registered type is *not* an atom when it is a numeric literal, or when its head is an
operation registered with `@[basify_op]`, in which case its arguments are visited instead.
Everything else, an application of an unregistered function in particular, is opaque and gets
generalized and case split as a whole -- including `⊤`, which costs a branch that immediately dies
but keeps `basify` from assuming that a term already in a constructor's shape belongs to that
constructor's case. Two alternatives can share a pattern and differ in their hypotheses. -/
def isAtom (e : Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← inferType e)
  unless ← isRegisteredType ty do return false
  let some head := e.getAppFn.constName? | return true
  if literalHeads.contains head then return false
  return !(← opsFor ty).contains head

/-- Collect the maximal atoms of `e` that contain no loose bound variables, interning them with
`AtomM` so that atoms that differ only up to definitional unfolding are identified. -/
partial def collectAtoms (e : Expr) : AtomM Unit := do
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

/-- All the atoms of the goal `g`, taken from the target and from every hypothesis.

Atoms are identified up to `instances` transparency, the setting `generalizeHyp` uses for
`kabstract`: identifying fewer atoms than the abstraction step goes on to identify would create one
variable per spelling and leave incoherent equations behind. -/
def goalAtoms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  AtomM.run .instances do
    collectAtoms (← instantiateMVars (← g.getType))
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      collectAtoms (← instantiateMVars decl.type)
    return (← get).atoms

/-! ### The steps -/

/-- Collect the atoms of `g` and turn each one into a variable, so that it can be case split:
those that are not variables already are generalized, keeping their defining equation as a new
hypothesis so that this step loses no information -- asking `GeneralizeArg` for a name is what
produces the equation at all, and without it the step would discard the link to the original term.
Each variable gets a short name and its equation that name with `_eq` appended, so that the case
split has something to name what it introduces after.

Returns the variables to split. They are collected once and then tracked: a case split replaces a
variable by a constructor pattern whose arguments are fresh variables, and those are added to the
list as they appear, so there is never a need to search the goal again. -/
def generalizeAtoms (g : MVarId) : MetaM (MVarId × Array FVarId) := g.withContext do
  let (varAtoms, termAtoms) := (← goalAtoms g).partition Expr.isFVar
  let varAtoms := varAtoms.map Expr.fvarId!
  if termAtoms.isEmpty then return (g, varAtoms)
  let args : Array GeneralizeArg := ← termAtoms.mapM fun e =>
    return { expr := e, hName? := ← mkFreshUserName `h }
  let hyps := (← getLCtx).foldl (init := #[]) fun hyps decl =>
    if decl.isImplementationDetail then hyps else hyps.push decl.fvarId
  try
    let (subst, introduced, g) ← g.generalizeHyp args hyps
    -- `introduced` holds the equations as well as the variables. Only the variables are of a
    -- registered type, and both follow the order of `args`, so splitting on that pairs each
    -- variable with its own equation.
    let mut vars := #[]
    let mut eqs := #[]
    for fvarId in introduced do
      if ← g.withContext do isRegisteredType (← instantiateMVars (← fvarId.getType)) then
        vars := vars.push fvarId
      else
        eqs := eqs.push fvarId
    -- Name each variable and its equation. Doing so one pair at a time is enough to keep them
    -- apart: `getUnusedName` sees the names already given out.
    let mut g := g
    for fvarId in vars, eqFVarId in eqs do
      let name ← g.withContext do return (← getLCtx).getUnusedName `x
      g ← g.rename fvarId name
      g ← g.withContext do g.rename eqFVarId ((← getLCtx).getUnusedName (name.appendAfter "_eq"))
    -- `generalizeHyp` may renumber the variables it abstracted inside, so follow the substitution.
    return (g, varAtoms.map (subst.get · |>.fvarId!) ++ vars)
  catch _ =>
    return (g, varAtoms)

/-- The names to give what an alternative introduces, following the plan recorded for it: the
binder carrying the value takes `base`, the others take `base` with their own name appended. When
the atom itself is anonymous everything stays anonymous.

The binder's name is appended verbatim, so an eliminator that writes `_pos` -- as the
unused-variable linter asks it to for a binder it does not itself use -- yields `x_pos`. -/
private def altNames (base? : Option Name) (binders : Array (Option Name)) : MetaM (List Name) := do
  let some base := base? | binders.toList.mapM fun _ => mkFreshUserName `x
  return binders.toList.map fun
    | none => base
    | some binder => base.appendAfter binder.toString

/-- Destruct the variable `fvarId` with the eliminator `entry.elimName`, naming what each
alternative introduces after `fvarId` itself.

This is what `cases x using e` does, minus the syntax: going through the tactic would mean making
`fvarId` referable by name first, which is a rename dance that the `Expr`-level API does not need.
The alternatives are introduced here rather than through `ElimApp.evalNames` so that the names can
be handed to `introN` directly. -/
def casesAtom (g : MVarId) (fvarId : FVarId) (entry : ElimEntry) : TacticM (List MVarId) := do
  let elimInfo ← getElimInfo entry.elimName
  let base? ← g.withContext do
    let name ← fvarId.getUserName
    return if name.hasMacroScopes then none else some name
  let targets ← g.withContext do addImplicitTargets elimInfo #[.fvar fvarId]
  let result ← g.withContext do ElimApp.mkElimApp elimInfo targets (← g.getTag)
  let elimArgs := result.elimApp.getAppArgs
  let targets ← g.withContext do elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
  let motive := elimArgs[elimInfo.motivePos]!
  let g ← generalizeTargetsEq g (← g.withContext do inferType motive) targets
  let (targetsNew, g) ← g.introN targets.size
  g.withContext do
    ElimApp.setMotiveArg g motive.mvarId! targetsNew
    g.assign result.elimApp
    let mut goals := #[]
    for alt in result.alts, binders in entry.altBinders do
      let (_, g) ← alt.mvarId.introN binders.size (← altNames base? binders)
      let some (g, _) ← Cases.unifyEqs? targets.size g {} | continue
      goals := goals.push (← targetsNew.foldlM (fun g fv => do return ← g.tryClear fv) g)
    return goals.toList

/-- Remove the `True` hypotheses that the simp sets leave behind: `simp only ... at *` rewrites a
hypothesis to `True` and re-asserts it, where `simp_all` would drop it. -/
def clearTrivialHypotheses (g : MVarId) : MetaM MVarId := g.withContext do
  g.tryClearMany <| ← (← getLCtx).foldlM (init := #[]) fun fvarIds decl => do
    if decl.isImplementationDetail then return fvarIds
    return if (← instantiateMVars decl.type).isTrue then fvarIds.push decl.fvarId else fvarIds

/-- The variables of a registered type that `g` has gained relative to `old`. These are the value
binders of the eliminator that has just been applied: the hypotheses a case split reverts and
reintroduces are also new, but they are `Prop`s, and no registered type is a `Prop`. -/
def newAtomVars (g : MVarId) (old : FVarIdSet) : MetaM (Array FVarId) := g.withContext do
  (← getLCtx).foldlM (init := #[]) fun acc decl => do
    if decl.isImplementationDetail || old.contains decl.fvarId then return acc
    return if ← isRegisteredType (← instantiateMVars decl.type) then acc.push decl.fvarId else acc

/-- Destruct the variables in `varsToElim`, one at a time, running the `basify_simp` simp set after
each so that the degenerate branches (`⊤ + a = ⊤` and friends) die *before* the number of branches
explodes. The variables a split introduces are appended to the list, which is how the descent
`ℝ≥0∞ → ℝ≥0 → ℝ` happens without ever searching the goal again.

A variable can disappear before its turn comes, when a branch simplifies it away; such an entry is
simply dropped. -/
partial def basifyLoop (g : MVarId) (varsToElim : List FVarId) : TacticM (List MVarId) := do
  let fvarId :: varsToElim := varsToElim | return [g]
  let entry? : Option ElimEntry ← g.withContext do
    let some decl := (← getLCtx).find? fvarId | return none
    elimEntryFor? (← instantiateMVars decl.type)
  let some entry := entry? | basifyLoop g varsToElim
  let old ← g.withContext do
    return (← getLCtx).foldl (init := (∅ : FVarIdSet)) fun s d => s.insert d.fvarId
  setGoals (← casesAtom g fvarId entry)
  evalTactic (← `(tactic| all_goals try simp only [basify_simp] at *))
  let mut result := []
  for g in ← getGoals do
    let g ← clearTrivialHypotheses g
    result := result ++ (← basifyLoop g (varsToElim ++ (← newAtomVars g old).toList))
  return result

/--
`basify` removes the layers that separate a type such as `ℝ≥0∞` or `ℕ∞` from the type its
arithmetic really lives in, turning the goal into an equivalent goal about that type.

Every value of a registered type is destructed with the eliminator registered for it -- `⊤` or
`↑x` for `ℝ≥0∞`, and `x.toNNReal` together with `0 ≤ x` for `ℝ≥0` -- the degenerate branches are
discharged, and the surviving propositions are pushed down along the coercions. The result is
normally finished off by a decision procedure for the underlying type:

```
example : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ = 4⁻¹ := by basify; norm_num
example (a b : ℕ∞) (h : a ≤ b) : a - b < b + 1 := by basify; lia
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
