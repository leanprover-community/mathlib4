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

This file declares the five attributes that drive `basify`, together with the two environment
extensions backing them. They live in their own file because Lean cannot use an attribute in the
file that declares it; `Mathlib/Tactic/Basify/Core.lean` documents the tactic itself.
-/

public meta section

open Lean Meta Elab Tactic

/-- Simp set applied by `basify` after each case split. It is meant to contain the lemmas that
make the degenerate branches, the ones where some atom is `⊤` or `⊥`, go away. -/
register_simp_attr basify_split

/-- Simp set applied by `basify` at the very end. It is meant to contain the lemmas that
translate a proposition about an extended type into a proposition about the underlying type, such
as `↑a ≤ ↑b ↔ a ≤ b`. -/
register_simp_attr basify_cast

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

/-- The lemmas registered with `@[basify_fact]`, indexed by the head symbol of the type they
talk about. -/
initialize factExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.find? n |>.getD #[]).push lem)
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
    for x in xs do
      if x == motive || x == targets[0]! then continue
      let head? ← forallTelescopeReducing (← inferType x) fun _ b => do
        unless b.getAppFn == motive do return none
        let args := b.getAppArgs
        unless args.size == 1 do return none
        return args[0]!.getAppFn.constName?
      if let some head := head? then altHeads := altHeads.push head
    return (tyName, { elimName, altHeads })

/-- Read off, from the type of `factName`, the head symbol of the type its first explicit argument
ranges over. -/
def analyzeFact (factName : Name) : MetaM Name := do
  forallTelescopeReducing (← getConstInfo factName).type fun xs _ => do
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      unless localDecl.binderInfo.isExplicit do continue
      let some tyName := (← instantiateMVars localDecl.type).getAppFn.constName? |
        throwError "the first explicit argument of `{.ofConstName factName}` does not have a \
          constant as the head of its type"
      return tyName
    throwError "`{.ofConstName factName}` takes no explicit argument, so `basify` cannot \
      tell what it is a fact about"

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

/-- `@[basify_elim]` registers an eliminator for `basify` to case split with. The
declaration must be usable as `cases x using foo`: it takes a motive, some minor premises and a
single target. -/
syntax (name := basifyElim) "basify_elim" : attr

initialize registerBuiltinAttribute {
  name := `basifyElim
  descr := "an eliminator that `basify` uses to case split a value of an extended type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyElim do throwUnsupportedSyntax
    elimExt.add (← MetaM.run' <| analyzeElim declName) kind
}

/-- `@[basify_fact]` registers a lemma of the form `∀ x : X, p x` as a fact that `basify`
adds to the context for every atom of type `X`. The atom is passed as the lemma's first explicit
argument, and `X` is read off from that argument's type. This is how a subtype is handled: tagging
`NNReal.coe_nonneg` makes `basify` record `0 ≤ (x : ℝ)` for every `ℝ≥0`-atom `x`. -/
syntax (name := basifyFact) "basify_fact" : attr

initialize registerBuiltinAttribute {
  name := `basifyFact
  descr := "a fact that `basify` records about every atom of the relevant type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyFact do throwUnsupportedSyntax
    factExt.add (← MetaM.run' <| analyzeFact declName, declName) kind
}

/-- `@[basify_op]` registers an operation of an extended type as one that `basify` knows
how to see inside of, by tagging the lemma that relates it to the corresponding operation of the
underlying type, such as `ENNReal.coe_add : ↑(a + b) = ↑a + ↑b`. Anything else of an extended type
is an atom: `basify` generalizes it and case splits on it rather than descending into it.

Both operations the lemma relates are registered, so a single lemma covers the operation upstairs
and the operation downstairs. The attribute does not add the lemma to a simp set; an operation is
normally tagged `@[basify_cast ←, basify_op]` or `@[basify_cast, basify_op]`,
depending on which way the coercion has to travel. -/
syntax (name := basifyOp) "basify_op" : attr

initialize registerBuiltinAttribute {
  name := `basifyOp
  descr := "an operation of an extended type that `basify` looks inside of"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``basifyOp do throwUnsupportedSyntax
    for pair in ← MetaM.run' <| analyzeOp declName do
      opExt.add pair kind
}

end Mathlib.Tactic.Basify
