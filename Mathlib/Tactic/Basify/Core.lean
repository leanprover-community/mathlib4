/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Util.AtomM
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Repeat

/-!
# The `basify` tactic

Mathlib has many types that are built from a well-behaved type by a construction that makes the
resulting arithmetic partial or truncated:

* *extensions* by a point at infinity, such as `ℕ∞ = WithTop ℕ` and `ℝ≥0∞ = WithTop ℝ≥0`;
* *subtypes* cut out by an inequality, such as `ℝ≥0 = {r : ℝ // 0 ≤ r}`.

Goals about such types are painful, because the decision procedures one would like to use (`lia`,
`linarith`, `nlinarith`, `positivity`, `norm_num`) only understand the underlying type.
`basify` peels these constructions off, turning the goal into an equivalent goal about the
underlying type, which can then be handed to those tactics:

```
example (a b : ℝ≥0∞) (h : a ≤ b) : a - b = 0 := by basify <;> simp_all
```

## Implementation

The two constructions are not handled by two mechanisms. Every registered type is taken apart the
same way, by case splitting on the eliminator registered for it with `@[basify_elim]`, and the only
thing that distinguishes them is how many cases that eliminator has: `ENNReal.recTopCoe` has two,
`⊤` and `↑x` with `x : ℝ≥0`, while a subtype's has one, replacing `t : ℝ≥0` by `x.toNNReal` and
handing `0 ≤ x` over as a binder. A subtype is just a degenerate case split.

The tactic runs three phases.

1. Every *atom* of a registered type is generalized to a local hypothesis, keeping its defining
   equation so that nothing is lost -- case splitting needs a variable to work on. Doing this once
   up front is enough: a case split replaces a variable by a constructor pattern whose arguments
   are themselves fresh variables, so it creates no new atom to generalize.
2. Until nothing registered is left: destruct one atom with its eliminator, then run the
   `basify_split` simp set everywhere. That simp set's job is to discharge the degenerate branches
   (e.g. `⊤ + a = ⊤`) *before* the number of branches explodes.
3. The `basify_cast` simp set moves the surviving propositions down to the underlying type. For
   `ℝ≥0∞` this means pulling `ℝ≥0 → ℝ≥0∞` coercions outwards until they can be cancelled, and then
   pushing `ℝ≥0 → ℝ` coercions inwards until only atoms are left under them.

An *atom* is a subterm of a registered type whose head is not an operation registered with
`@[basify_op]`: `a + b` is not an atom because addition is registered, and the tactic recurses
into `a` and `b`, whereas `f x` for an unregistered `f` is one and gets generalized and split as a
whole. This is why the operations have to be declared rather than inferred: knowing that `↑a + ↑b`
is worth descending into is exactly the content of `ENNReal.coe_add`.

One constraint on eliminators, and the reason subtypes can be handled this way at all: an
eliminator must not produce `Subtype.mk` terms. `ℝ≥0` and `ℕ+` are semireducible definitions, so a
goal mentioning `⟨x, hx⟩ : ℝ≥0` is not type-correct at the transparency `simp` checks at, and every
subsequent `simp` fails outright. Present the value through a properly typed constructor instead;
the two subtype layers use `Real.toNNReal` and `Nat.toPNat'`.

## Limitations

* Each case split doubles the number of branches, so the `basify_split` set has to be good
  enough to kill the degenerate ones; a goal with many independent atoms of a registered type will
  otherwise be slow.
* Truncated subtraction comes out as `max (a - b) 0`, which `linarith` does not understand. Such
  goals usually need a case split on `a ≤ b` afterwards.
* Generalizing an atom keeps its defining equation, so nothing is lost, but a fact that holds for
  the atom by definition rather than by hypothesis (for instance `ENNReal.ofReal x ≠ ⊤`) is only
  exploited if the `basify_split` set can derive it from that equation.

## Relation to other tactics

`basify` belongs to the `zify`/`qify`/`rify` family in what it achieves -- it shifts propositions to
a type where the arithmetic is total -- but not in how: those tactics deliberately leave every
variable's type alone, whereas `basify` destructs the variables, so an `ℝ≥0` hypothesis really does
become an `ℝ` one paired with `0 ≤ ·`. In that respect it is closer to `lift`. The name says "the
base type" rather than a fixed one because the target depends on what is registered: `ℕ` for `ℕ∞`,
`ℝ` for `ℝ≥0∞`.

* `rify` already covers `ℝ≥0 → ℝ`, and `linarith` ships a preprocessor doing the same shift
  together with the nonnegativity facts. On a goal stated purely in `ℝ≥0` those are usually
  enough; `basify` earns its keep there only on truncated subtraction, which it rewrites with the
  unconditional `NNReal.coe_sub_def`.
* `lift` is the per-variable version of the interesting branch of a case split: `lift a to ℝ≥0
  using ha` is what one writes by hand once `a ≠ ⊤` is known. `basify` does not need that
  hypothesis, because it splits on it and discharges the other branch.
* `norm_cast` removes coercions and therefore lands in the *smallest* type of a cast tower, which
  for `ℝ≥0∞` is `ℝ≥0`, not `ℝ`. Reaching `ℝ` means travelling down one coercion and up another,
  which is why the `basify_cast` set holds `←` lemmas for the extension layer and forward lemmas
  for the subtype layer.

What has no counterpart elsewhere is the case split: `⊤ - a` is not a cast-normalisation problem,
and no amount of rewriting turns it into one.

## Extending the tactic

Four attributes drive the tactic, so that new constructions can be supported without touching this
file:

* `@[basify_elim]` marks an eliminator, i.e. something usable with `cases x using ...`. The
  type it destructs and the shapes of its cases are read off from its type.
* `@[basify_op]` marks the lemma relating an operation of a registered type to the
  corresponding operation of the underlying type, such as `ENNReal.coe_add : ↑(a + b) = ↑a + ↑b`.
  For a subtype this is the statement that the operation agrees with the one upstairs, which has
  the same shape, so the same attribute covers both kinds of type.
* `@[basify_split]` and `@[basify_cast]` are the two simp sets described above. Like any
  simp set they accept `←` to register a lemma in the reversed direction, which is what one usually
  wants in the `basify_cast` set.

`Mathlib/Tactic/Basify/ENNReal.lean` is a worked example using all four.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Basify

/-! ### Propositional cleanup

The `basify_split` simp set is run with `simp only`, so it has to carry the handful of
propositional lemmas needed to actually make a contradictory branch disappear: without
`not_true_eq_false`, a hypothesis `⊤ ≠ ⊤` gets stuck at `¬True` instead of closing the goal.
-/

attribute [basify_split] ne_eq not_true_eq_false not_false_eq_true eq_self_iff_true
  true_and and_true and_self true_or or_true or_self true_iff iff_true

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

A term of a registered type is *not* an atom when it is a numeric literal, when it is already in
the shape the eliminator produces (`⊤`, `↑x`, ...), or when its head is an operation registered
with `@[basify_op]`, in which case its arguments are visited instead. Everything else, an
application of an unregistered function in particular, is opaque and gets case split as a whole. -/
def isAtom (e : Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← inferType e)
  unless ← isRegisteredType ty do return false
  let some head := e.getAppFn.constName? | return true
  if literalHeads.contains head then return false
  if ((← elimEntryFor? ty).elim #[] (·.altHeads)).contains head then return false
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

/-- The user name given to the equations that `basify` introduces when it generalizes an atom.
These hypotheses are not searched for atoms again, which is what makes the main loop terminate. -/
private def atomEqName : Name := `basify_eq

private def isAtomEq (n : Name) : Bool :=
  n.eraseMacroScopes.toString.startsWith atomEqName.toString

/-- All the atoms of the goal `g`, taken from the target and from every hypothesis except the ones
`basify` introduced itself when generalizing.

Atoms are identified up to `instances` transparency, the setting `generalizeHyp` uses for
`kabstract`: identifying fewer atoms than the abstraction step goes on to identify would create one
variable per spelling and leave incoherent equations behind. -/
def goalAtoms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  AtomM.run .instances do
    collectAtoms (← instantiateMVars (← g.getType))
    for decl in ← getLCtx do
      if decl.isImplementationDetail || isAtomEq decl.userName then continue
      collectAtoms (← instantiateMVars decl.type)
    return (← get).atoms

/-- Head symbols that say nothing about what an atom is, so that a name taken from them would be
worse than a plain `x`. `DFunLike.coe` is the common one: it heads every application of a bundled
map, such as the `uniformOn ... s` of a measure. -/
private def uninformativeNames : Array Name := #[`coe, `cast, `val, `fn, `ofNat, `toFun]

/-- A readable base name for a hypothesis about the atom `e`. -/
private def atomBaseName (e : Expr) : MetaM Name := do
  match e.getAppFn with
  | .const n _ =>
    let base := n.components.getLast?.getD `x
    return if uninformativeNames.contains base then `x else base
  | .fvar fvarId => return (← fvarId.getUserName).eraseMacroScopes
  | _ => return `x

/-- Pick names based on `bases` that are unused in `lctx` and pairwise distinct. -/
private def freshNames (lctx : LocalContext) (bases : Array Name) : Array Name := Id.run do
  let mut used : NameSet := ∅
  let mut out := #[]
  for base in bases do
    let mut name := lctx.getUnusedName base
    let mut i := 1
    while used.contains name do
      name := lctx.getUnusedName (base.appendAfter s!"_{i}")
      i := i + 1
    used := used.insert name
    out := out.push name
  return out

/-! ### The steps -/

/-- Generalize every atom whose type has an `@[basify_elim]` eliminator, so that it can be
case split. The defining equation of each atom is kept as a new hypothesis, so this step does not
lose information. -/
def generalizeAtoms (g : MVarId) : MetaM MVarId := g.withContext do
  let atoms ← (← goalAtoms g).filterM fun e => do
    if e.isFVar then return false
    return (← elimEntryFor? (← instantiateMVars (← inferType e))).isSome
  if atoms.isEmpty then return g
  let names := freshNames (← getLCtx) (← atoms.mapM atomBaseName)
  let args : Array GeneralizeArg := atoms.zipIdx.map fun (e, i) =>
    { expr := e, xName? := names[i]!, hName? := atomEqName.appendAfter s!"_{i}" }
  let hyps := (← getLCtx).foldl (init := #[]) fun hyps decl =>
    if decl.isImplementationDetail then hyps else hyps.push decl.fvarId
  try
    return (← g.generalizeHyp args hyps).2.2
  catch _ =>
    return g

/-- Can `decl` be referred to by its user name? This fails both for the inaccessible names that
`cases` introduces and for names shadowed by a later hypothesis. -/
def isNameable (lctx : LocalContext) (decl : LocalDecl) : Bool :=
  !decl.userName.hasMacroScopes &&
    (lctx.findFromUserName? decl.userName).any (·.fvarId == decl.fvarId)

/-- Give a usable name to every hypothesis of `g` that a case split has just introduced, using
`base` as a suggestion. -/
def nameNewHypotheses (g : MVarId) (old : FVarIdSet) (base : Name) : MetaM MVarId := do
  let fvarIds ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun fvarIds decl => do
      if decl.isImplementationDetail || old.contains decl.fvarId then return fvarIds
      return if isNameable (← getLCtx) decl then fvarIds else fvarIds.push decl.fvarId
  let mut g := g
  for fvarId in fvarIds do
    let name ← g.withContext do
      let suggestion := if ← isProp (← fvarId.getType) then base.appendBefore "h" else base
      return (← getLCtx).getUnusedName suggestion
    g ← g.rename fvarId name
  return g

/-- Destruct the first local hypothesis that is an atom of a type carrying an
`@[basify_elim]` eliminator, keeping the names of the hypotheses it introduces readable.

Only variables that are atoms are split: one occurring solely inside an opaque atom, or solely in
an equation left behind by an earlier generalization, has already been accounted for, and splitting
it would double the number of branches for nothing. -/
def casesFirstAtom (g : MVarId) : TacticM (List MVarId) := do
  let (fvarId, base, elimName, old) ← g.withContext do
    let atomFVars := (← goalAtoms g).foldl (init := (∅ : FVarIdSet)) fun atomFVars e =>
      if let .fvar fvarId := e then atomFVars.insert fvarId else atomFVars
    let lctx ← getLCtx
    let some decl ← lctx.findDeclM? fun decl => do
        if decl.isImplementationDetail || !atomFVars.contains decl.fvarId then return none
        if (← elimEntryFor? (← instantiateMVars decl.type)).isSome then return some decl
        else return none
      | throwError "`basify` made no progress: there is nothing left to take apart"
    let some entry ← elimEntryFor? (← instantiateMVars decl.type) | unreachable!
    let old := lctx.foldl (init := (∅ : FVarIdSet)) fun s d => s.insert d.fvarId
    return (decl.fvarId, decl.userName.eraseMacroScopes, entry.elimName, old)
  -- `cases x using e` refers to `x` by name, so rename it first if its name is not usable.
  let g ← g.withContext do
    if isNameable (← getLCtx) (← fvarId.getDecl) then pure g
    else g.rename fvarId ((← getLCtx).getUnusedName base)
  let name ← g.withContext fvarId.getUserName
  setGoals [g]
  evalTactic (← `(tactic| cases $(mkIdent name):ident using $(mkCIdent elimName):ident))
  (← getGoals).mapM (nameNewHypotheses · old base)

/-- Remove the `True` hypotheses that the simp sets leave behind: `simp only ... at *` rewrites a
hypothesis to `True` and re-asserts it, where `simp_all` would drop it. -/
def clearTrivialHypotheses (g : MVarId) : MetaM MVarId := g.withContext do
  g.tryClearMany <| ← (← getLCtx).foldlM (init := #[]) fun fvarIds decl => do
    if decl.isImplementationDetail then return fvarIds
    return if (← instantiateMVars decl.type).isTrue then fvarIds.push decl.fvarId else fvarIds

/-- One step of `basify`: destruct one atom of a registered type and clean up the degenerate
branches with the `basify_split` simp set. Fails once there is nothing left to take apart, which is
how the main loop knows it is done. -/
def basifyStep (g : MVarId) : TacticM (List MVarId) := do
  setGoals (← casesFirstAtom g)
  evalTactic (← `(tactic| all_goals try simp only [basify_split] at *))
  (← getGoals).mapM fun g => do return ← clearTrivialHypotheses g

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

New types are supported by tagging an eliminator with `@[basify_elim]`, its operations with
`@[basify_op]`, and the relevant rewrite lemmas with `@[basify_split]` and `@[basify_cast]`.
-/
elab "basify" : tactic => focus do
  setGoals (← Meta.repeat' basifyStep [← generalizeAtoms (← getMainGoal)])
  evalTactic (← `(tactic| all_goals first
    | simp_all only [basify_split, basify_cast]
    | simp only [basify_split, basify_cast] at *
    | skip))
  setGoals (← (← getGoals).mapM fun g => do return ← clearTrivialHypotheses g)

end Mathlib.Tactic.Basify
