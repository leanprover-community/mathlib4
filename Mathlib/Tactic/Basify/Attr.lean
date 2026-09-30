/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.ElimInfo
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Attributes for the `basify` tactic

This file declares the three attributes that drive `basify`, together with the two environment
extensions backing them. They live in their own file because Lean cannot use an attribute in the
file that declares it; `Mathlib/Tactic/Basify.lean` documents the tactic itself.
-/

public meta section

open Lean Meta Elab Tactic

/-- The simp set `basify` runs, after each case split and once at the end: the lemmas that clear
away the degenerate branches, where some atom is `⊤` or `⊥`, and those that translate a proposition
down, such as `↑a ≤ ↑b ↔ a ≤ b`. Lemmas tagged `@[basify_op]` are added here as well. -/
register_simp_attr basify_simp

namespace Mathlib.Tactic.Basify

/-! ### The registries -/

/-- Information about an eliminator registered with `@[basify_elim]`. -/
structure ElimEntry where
  /-- The name of the eliminator, used as `cases x using elimName`. -/
  elimName : Name
  /-- How to name what each minor premise introduces, one entry per premise and then one per
  binder, in order. `none` marks the binder carrying the value -- the one occurring in the
  alternative's pattern -- which takes the name of the atom being split; any other binder takes
  that name with its own appended. Splitting `x : ℕ+` with an alternative
  `∀ (n : ℕ) (_pos : 0 < n), C n.toPNat'` yields `x` and `x_pos`. -/
  altBinders : Array (Array (Option Name))
  deriving Inhabited

/-- The eliminators registered with `@[basify_elim]`, indexed by the head symbol of the type
they destruct. -/
initialize elimExt : SimpleScopedEnvExtension (Name × ElimEntry) (NameMap ElimEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, e) => m.insert n e
    initial := {}
  }

/-- The operations registered with `@[basify_op]`, indexed by the head symbol of the type they
act on. These are the applications `basify` looks inside of when searching for atoms. -/
initialize opExt : SimpleScopedEnvExtension (Name × Name) (NameMap NameSet) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (ty, op) => m.insert ty ((m.find? ty |>.getD ∅).insert op)
    initial := {}
  }

/-- Read one alternative: how to name each of the binders it introduces. -/
private def analyzeAlt (elimName altName : Name) (altType : Expr) : MetaM (Array (Option Name)) :=
  forallTelescopeReducing altType fun binders concl => do
    let pattern := concl.getAppArgs[0]!
    -- A pattern that is a bare variable leaves the target exactly as it was, so splitting with
    -- such an alternative would queue the same variable again and `basify` would not terminate.
    unless pattern.getAppFn.isConst do
      throwError "the `{altName}` alternative of `{.ofConstName elimName}` does not refine its \
        target: its pattern is a variable, so splitting with it would make no progress"
    binders.mapM fun binder => do
      if pattern.containsFVar binder.fvarId! then return none
      else return some (← binder.fvarId!.getUserName).eraseMacroScopes

/-- Read off, from the type of the eliminator `elimName`, the head symbol of the type it destructs
together with how to name what each of its alternatives introduces. -/
def analyzeElim (elimName : Name) : MetaM (Name × ElimEntry) := do
  -- `basify` hands the same `getElimInfo` to `ElimApp`, so what is recorded here lines up with the
  -- goals the case split produces.
  let elimInfo ← getElimInfo elimName
  let #[targetPos] := elimInfo.targetsPos |
    throwError "`{.ofConstName elimName}` eliminates {elimInfo.targetsPos.size} targets, but \
      `basify` only supports eliminators with a single target"
  for info in elimInfo.altsInfo do
    unless info.provesMotive do
      throwError "the `{info.name}` alternative of `{.ofConstName elimName}` does not conclude \
        with the motive, so `basify` cannot tell what shape it produces"
  forallTelescopeReducing elimInfo.elimType fun xs _ => do
    let tyName := (← instantiateMVars (← inferType xs[targetPos]!)).getAppFn.constName!
    let altTypes : Array Expr ← xs.zipIdx.filterMapM fun (x, i) => do
      if i == elimInfo.motivePos || i == targetPos then return none
      if (← x.fvarId!.getDecl).binderInfo.isExplicit then return some (← inferType x)
      else return none
    let altBinders ← elimInfo.altsInfo.zip altTypes |>.mapM fun (info, altType) => do
      analyzeAlt elimName info.name altType
    return (tyName, ⟨elimName, altBinders⟩)

/-- The explicit arguments of the application `e`. -/
private def explicitArgs (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  forallBoundedTelescope (← inferType e.getAppFn) args.size fun xs _ => do
    let mut out := #[]
    for x in xs, a in args do
      if (← x.fvarId!.getBinderInfo).isExplicit then out := out.push a
    return out

/-- The head symbol of `e` together with the head symbol of its type, when both are constants. -/
private def headPair? (e : Expr) : MetaM (Option (Name × Name)) := do
  let some head := e.getAppFn.constName? | return none
  let some tyName := (← instantiateMVars (← inferType e)).getAppFn.constName? | return none
  return some (tyName, head)

/-- The operations related by an `@[basify_op]` lemma `↑(f a₁ … aₙ) = g ↑a₁ … ↑aₙ`, namely `f` and
`g`, each paired with the type it operates on. -/
def analyzeOp (opName : Name) : MetaM (Array (Name × Name)) := do
  forallTelescopeReducing (← getConstInfo opName).type fun _ concl => do
    let some (_, lhs, rhs) := concl.eq? |
      throwError "the conclusion of `{.ofConstName opName}` is not an equation, so `basify` \
        cannot tell which operations it relates; it should look like `↑(f a₁ … aₙ) = g ↑a₁ … ↑aₙ`"
    let mut pairs := #[]
    -- Either side may be the coerced one, so both are inspected, and a side is looked through when
    -- it is a one-argument application such as a coercion.
    for side in #[lhs, rhs] do
      if let some pair ← headPair? side then pairs := pairs.push pair
      if let #[arg] ← explicitArgs side then
        if let some pair ← headPair? arg then pairs := pairs.push pair
    if pairs.isEmpty then
      throwError "neither side of `{.ofConstName opName}` is an application of a constant, so \
        there is no operation for `basify` to register"
    return pairs

/-- `@[basify_elim]` registers an eliminator for `basify` to case split with. The declaration must
be usable as `cases x using foo`: it takes a motive, some minor premises and a single target. The
type it destructs and the shape of each of its cases are read off from its type.

A subtype is registered the same way, with an eliminator that has a single minor premise. It must
present the value through a properly typed constructor rather than `Subtype.mk`: `ℝ≥0` and `ℕ+` are
semireducible definitions, so a goal mentioning `⟨x, hx⟩ : ℝ≥0` is not type-correct at the
transparency `simp` checks at. See `NNReal.recToNNReal`, which uses `Real.toNNReal`. -/
syntax (name := basifyElim) "basify_elim" : attr

initialize registerBuiltinAttribute {
  name := `basifyElim
  descr := "an eliminator that `basify` uses to case split a value of a registered type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyElim do throwUnsupportedSyntax
    elimExt.add (← MetaM.run' <| analyzeElim declName) kind
}

/-- `@[basify_op]` registers an operation of a registered type as one that `basify` knows
how to see inside of, by tagging the lemma that relates it to the corresponding operation of the
underlying type, such as `ENNReal.coe_add : ↑(a + b) = ↑a + ↑b`. Anything else of a registered type
is an atom: `basify` generalizes it and case splits on it rather than descending into it.

The lemma is also added to `basify_simp`, reversed if `←` is given, so that what `basify` looks
inside of it can also rewrite through. That rules out a lemma unusable as a rewrite:
`ENNReal.coe_ofNat` has a `no_index`ed right-hand side that would match everything when reversed,
so `Mathlib/Tactic/Basify/ENNReal.lean` restates it. -/
syntax (name := basifyOp) "basify_op" (" ←")? : attr

initialize registerBuiltinAttribute {
  name := `basifyOp
  descr := "an operation of a registered type that `basify` looks inside of"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyOp do throwUnsupportedSyntax
    let some ext ← getSimpExtension? `basify_simp |
      throwError "the `basify_simp` simp set is not registered"
    MetaM.run' <| addSimpTheorem ext declName (post := true) (inv := !stx[1].isNone) kind
      (prio := eval_prio default)
    for pair in ← MetaM.run' <| analyzeOp declName do
      opExt.add pair kind
}

end Mathlib.Tactic.Basify
