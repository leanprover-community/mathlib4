/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Attributes for the `basify` tactic

This file declares the three attributes that drive `basify`, together with the two environment
extensions backing them. They live in their own file because Lean cannot use an attribute in the
file that declares it; `Mathlib/Tactic/Basify/Core.lean` documents the tactic itself.
-/

public meta section

open Lean Meta Elab Tactic

/-- The simp set `basify` runs, both after each case split and once at the end. It holds the lemmas
that make the degenerate branches go away -- the ones where some atom is `⊤` or `⊥` -- together with
the lemmas that translate a proposition about a registered type into one about the underlying type,
such as `↑a ≤ ↑b ↔ a ≤ b`. -/
register_simp_attr basify_simp

namespace Mathlib.Tactic.Basify

/-! ### The registries -/

/-- Information about an eliminator registered with `@[basify_elim]`. -/
structure ElimEntry where
  /-- The name of the eliminator, used as `cases x using elimName`. -/
  elimName : Name
  /-- The head symbols of the patterns of the minor premises. For `ENNReal.recTopCoe` these are
  `Top.top` and `ENNReal.ofNNReal`: a term of the form `⊤` or `↑x` is already in the shape the
  eliminator produces, so it is not an atom. -/
  altHeads : Array Name
  /-- How to name what each minor premise introduces, one entry per binder, in order. `none` marks
  the binder carrying the value -- the one occurring in the alternative's pattern -- which takes the
  name of the atom being split; any other binder takes that name with its own appended. Splitting
  `x : ℕ+` with an alternative `∀ (n : ℕ) (_pos : 0 < n), C n.toPNat'` yields `x` and `x_pos`. -/
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

/-- Read off, from the type of the eliminator `elimName`, the head symbol of the type it destructs
together with the head symbols of the patterns of its minor premises. -/
def analyzeElim (elimName : Name) : MetaM (Name × ElimEntry) := do
  forallTelescopeReducing (← getConstInfo elimName).type fun xs concl => do
    let motive := concl.getAppFn
    unless motive.isFVar && xs.contains motive do
      throwError "`{.ofConstName elimName}` is not an eliminator: its conclusion is not an \
        application of one of its arguments"
    let targets := concl.getAppArgs
    unless targets.size == 1 do
      throwError "`{.ofConstName elimName}` eliminates {targets.size} targets, but `basify` \
        only supports eliminators with a single target"
    let some tyName := (← instantiateMVars (← inferType targets[0]!)).getAppFn.constName? |
      throwError "the target of `{.ofConstName elimName}` does not have a constant as its head"
    let mut altHeads := #[]
    let mut altBinders := #[]
    for x in xs do
      if x == motive || x == targets[0]! then continue
      let alt? ← forallTelescopeReducing (← inferType x) fun ys b => do
        unless b.getAppFn == motive do return none
        let args := b.getAppArgs
        unless args.size == 1 do return none
        let pattern := args[0]!
        let binders ← ys.mapM fun y => do
          if pattern.containsFVar y.fvarId! then return none
          else return some (← y.fvarId!.getUserName).eraseMacroScopes
        return some (pattern.getAppFn.constName?, binders)
      let some (head?, binders) := alt? | continue
      if let some head := head? then altHeads := altHeads.push head
      altBinders := altBinders.push binders
    return (tyName, { elimName, altHeads, altBinders })

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

/-- Read the operations related by an `@[basify_op]` lemma
`↑(f a₁ … aₙ) = g ↑a₁ … ↑aₙ`: both `f`, at the type it operates on, and `g`, at the type it
operates on. Either of the two sides may be the coerced one, so both are inspected, and a side is
looked through when it is a one-argument application such as a coercion. -/
def analyzeOp (opName : Name) : MetaM (Array (Name × Name)) := do
  forallTelescopeReducing (← getConstInfo opName).type fun _ concl => do
    let some (_, lhs, rhs) := concl.eq? |
      throwError "the conclusion of `{.ofConstName opName}` is not an equation, so `basify` \
        cannot tell which operations it relates; it should look like `↑(f a₁ … aₙ) = g ↑a₁ … ↑aₙ`"
    let mut pairs := #[]
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

This is the only mechanism: a subtype is registered the same way, with an eliminator that has a
single minor premise. Such an eliminator must present the value through a properly typed
constructor rather than `Subtype.mk`, because `ℝ≥0` and `ℕ+` are semireducible definitions and a
goal mentioning `⟨x, hx⟩ : ℝ≥0` is not type-correct at the transparency `simp` checks at. See
`NNReal.recToNNReal`, which uses `Real.toNNReal`. -/
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

Both operations the lemma relates are registered, so a single lemma covers the operation upstairs
and the operation downstairs. The attribute does not add the lemma to a simp set; an operation is
normally tagged `@[basify_simp ←, basify_op]` or `@[basify_simp, basify_op]`, depending on which
way the coercion has to travel.

Registering an operation that no `basify_simp` rule can rewrite is worse than not registering it at
all: `basify` descends into the arguments and splits them, but nothing then moves the operation
itself down, so every branch is left stranded in the registered type. What has to be covered is the
head symbol, not necessarily by the same lemma: `ENNReal.coe_ofNat` would serve here but is
unusable as a reversed simp lemma, so `Mathlib/Tactic/Basify/ENNReal.lean` restates it. -/
syntax (name := basifyOp) "basify_op" : attr

initialize registerBuiltinAttribute {
  name := `basifyOp
  descr := "an operation of a registered type that `basify` looks inside of"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyOp do throwUnsupportedSyntax
    for pair in ← MetaM.run' <| analyzeOp declName do
      opExt.add pair kind
}

end Mathlib.Tactic.Basify
