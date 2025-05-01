/-
Copyright (c) 2025 Tiancheng "Timothy" Gu and Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiancheng "Timothy" Gu, Kyle Miller
-/
import Lean
import Mathlib.Data.Fintype.EquivFin

/-!
# `Infinite` derive handler

This module defines a `Infinite` derive handler for inductive types.
It supports only non-`mutual` inductive types with no indices.

Recall that the arguments to an inductive type's constructor are divided into *parameters*
and *fields*, where the parameters are those arguments that are also arguments
to the type constructor.
The handler can derive an `Infinite α` instance if the inductive type `α`
satisfies at least one of the following:

1. There is a constructor whose fields all have types that are `Nonempty` and at least one
   if the fields is `Infinite`. (Note that `Infinite` implies `Nonempty`.)
2. There is a constructor whose fields all have types that are `Nonempty`,
   and a separate constructor whose fields all have types that are either `α` or `Nonempty`.

Here are two examples of what this handler can handle:
```
structure S where
  a : Nat
  b : Unit
  deriving Infinite

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
  deriving Inhabited, Infinite
```

Additionally, this module provides the `derive_infinite%` term elaborator, which allows adding some
more hypotheses to the derived `Infinite` instance.
```
inductive List' (α : Type u) where
  | nil : List' α
  | cons (head : α) (tail : List' α) : List' α
  deriving Inhabited

instance [Nonempty α] : Infinite (List' α) := derive_infinite% _
```

The deriving handler does not currently support mutually inductive types. It also doesn't support
indexed inductive types in general, but `derive_infinite%` works for specific indexed types:
```
inductive Vector' (α : Type u) : Nat → Type u where
  | nil : Vector' α 0
  | cons (head : α) (tail : Vector' α n) : Vector' α (n + 1)
instance [Inhabited α] : ∀ n, Inhabited (Vector' α n) := ⋯
instance [Inhabited α] [Infinite α] : Infinite (Vector' α (n + 1)) := derive_infinite% _
```

## Implementation Notes

To get debugging information (including generated proof), run
`set_option trace.Elab.Deriving.infinite true`.

The generated proof uses one of the following two strategies, depending on which of the two
scenarios we are currently in.
1. If there is a constructor with an `Infinite` field, we try to construct a proof for
   `Infinite α` by forming an injection from that `Infinite` type to `α`, and then using the
   lemma `Infinite.of_injective`.
2. If there is a constructor with an `α`-valued field, we construct an injection `α → α`
   and then use the second constructor to prove the injection is proper.
   The lemma `Infinite.of_injective_to_set` then completes the proof.

The deriving handler is implemented in terms of `derive_infinite%` in the following way:
```
instance [... Infinite for each parameter of α ...] : Infinite α := derive_infinite% _
```
-/

namespace Mathlib.Deriving.Infinite
open Lean Elab Command Parser.Term Meta

/-!
### Theory

We state the necessary lemmas to protect this module from changes to theory files.
-/

private theorem infinite_of_injective {α β : Sort _} [Infinite β]
    (f : β → α) (hf : Function.Injective f) : Infinite α :=
  Infinite.of_injective f hf

private theorem infinite_of_injective_to_set {α : Type _} {s : Set α} (hs : s ≠ Set.univ)
    {f : α → s} (hf : Function.Injective f) : Infinite α :=
  Infinite.of_injective_to_set hs hf

/-!
### `derive_infinite% α` term elaborator
-/

/--
Given a constructor `ctor` with `m` inductive parameters, `n` fields, and `fieldIdx = i`, returns
```
(@ctor _ᵐ b₁ b₂ … bₙ,
 bᵢ,
 fun x =>
   `(Nonempty.elim inferInstance fun b₁ =>
     …  -- (except bᵢ)
     Nonempty.elim inferInstance fun bₙ => $x))
```
Additionally, fields in `leaveAsHole` are left as `_` and don't have a corresponding
`Nonempty.elim`. `leaveAsHole` must be sorted.
-/
private def mkObj (ctorInfo : ConstructorVal) (fieldIdx : Nat) (leaveAsHole : Array Nat := {}) :
    MetaM (Term × Ident × (Term → MetaM Term)) := do
  let mut leaveAsHole := leaveAsHole.toSubarray
  let mut ctorArgs := #[]
  let mut addNonemptyElim := pure
  let holeArg := mkIdent <| ← mkFreshUserName `a
  for _ in [:ctorInfo.numParams] do
    ctorArgs := ctorArgs.push (← `(_))
  for i in [:ctorInfo.numFields] do
    if i = fieldIdx then
      ctorArgs := ctorArgs.push holeArg
    else if some i = leaveAsHole[0]? then
      ctorArgs := ctorArgs.push (← `(_))
      leaveAsHole := leaveAsHole.popFront
    else
      let arg := mkIdent <| ← mkFreshUserName `b
      addNonemptyElim := fun x => do
        let w ← `($(mkCIdent ``Nonempty.elim) $(mkCIdent ``inferInstance) fun $arg => $x)
        addNonemptyElim w
      ctorArgs := ctorArgs.push arg
  let obj ← `(@$(mkCIdent ctorInfo.name) $ctorArgs:term*)
  return (obj, holeArg, addNonemptyElim)

/--
Given constructor `ctor` with `n` fields and `fieldIdx = i`, returns either
`fun a₁ … aₙ => aᵢ` or `fun a₁ … aₙ => eq_of_heq aᵢ`.
-/
private def mkNoConfusionMotive (ctorInfo : ConstructorVal) (xs : Array Expr) (self : Expr)
    (fieldIdx : Nat) : TermElabM Term := do
  let eqTypes ← noConfusionTypes
  let mut nonPropIdx := 0
  let a ← mkFreshUserName `a
  let mut binders := #[]
  let mut isHEq := false
  for i in [:ctorInfo.numFields] do
    let xTy   ← inferType xs[ctorInfo.numParams + i]!
    let xTyTy ← inferType xTy
    if !xTyTy.isProp then
      if i = fieldIdx then
        binders := binders.push (mkIdent a : Term)
        isHEq := eqTypes[nonPropIdx]!.isHEq
      else
        binders := binders.push (← `(_))
      nonPropIdx := nonPropIdx + 1
    else
      if i = fieldIdx then
        throwError "(internal error) noConfusion has no equality for Prop-valued field{indentD xTy}"

  if isHEq then
    `(fun $binders:term* => $(mkCIdent ``eq_of_heq) $(mkIdent a))
  else
    `(fun $binders:term* => $(mkIdent a))

where
  /-- Return the equality types provided by `noConfusion (_ : ctor xs = ctor xs)`. -/
  noConfusionTypes : TermElabM (Array Expr) := do
    let xsTerm ← xs.mapM Expr.toSyntax
    let obj    ← Term.elabTermEnsuringType (← `(@$(mkCIdent ctorInfo.name) $xsTerm:term*)) self
    let objStx ← obj.toSyntax
    let name   := ctorInfo.induct.str "noConfusionType"
    let type   ← Term.elabTerm (← `($(mkCIdent name) Prop $objStx $objStx)) none
    match ← whnf type with
    | .forallE (binderType := t) .. => do
      forallBoundedTelescope t ctorInfo.numFields fun eqs _ => do
        eqs.mapM fun eq => do
          let t ← inferType eq
          whnf t
    | _ => pure #[]

/--
Try to construct a proof for `Infinite α` by forming an injection from an `Infinite` field to `α`,
and then using `Infinite.of_injective`.
-/
private def mkProofField (ctorInfo : ConstructorVal) (xs : Array Expr) (self : Expr) :
    TermElabM (Option Term) := do
  let mut infiniteField := none
  let mut leaveAsHole := #[]
  for i in [:ctorInfo.numFields] do
    let x := xs[ctorInfo.numParams + i]!
    let xTy ← inferType x
    let usedBySelf ← hasAssignedMVar x <||> exprDependsOn' self x
    let dependedOn ← xs.anyM (start := ctorInfo.numParams + i + 1) fun y => do
      let yTy ← inferType y
      exprDependsOn' yTy x

    -- If `x` is part of `self`, it should be inferred rather than obtained from `Nonempty.elim`.
    if usedBySelf then
      leaveAsHole := leaveAsHole.push i

    -- If some future fields or `self` depend on `x`, then it must be constrained.
    -- Do not consider this field `Infinite`.
    let infinite ← if dependedOn || usedBySelf then pure none
                    else trySynthInstance (← mkAppM ``Infinite #[xTy]) <&> LOption.toOption
    let nonempty ← trySynthInstance (← mkAppM ``Nonempty #[xTy]) <&> LOption.toOption

    let tracePrefix := m!"{ctorInfo.name} field {i}: "
    trace[Elab.Deriving.infinite] tracePrefix ++
      m!"dependedOn={dependedOn} usedBySelf={usedBySelf} infinite={infinite} nonempty={nonempty}"
    if nonempty.isNone then
      trace[Elab.Deriving.infinite] tracePrefix ++ "not Nonempty; giving up on this constructor"
      return none
    else if infiniteField.isNone && infinite.isSome then
      infiniteField := some i

  let some j := infiniteField
    | return none
  let (obj, holeArg, addNonemptyElim) ← mkObj ctorInfo j (leaveAsHole := leaveAsHole.toSubarray)
  let noConfusion := mkCIdent <| ctorInfo.induct.str "noConfusion"
  let noConfusionMotive ← mkNoConfusionMotive ctorInfo xs self j
  let val ←
    `($(mkCIdent ``infinite_of_injective)
        (fun $holeArg:ident => $obj)
        (fun _ _ h => $noConfusion h $noConfusionMotive))
  addNonemptyElim val

/-- Get the constructor of the `default` element of `type`.  -/
private def getDefaultCtor (type : Expr) : TermElabM (Option (Expr × Name)) := do
  try
    let val ← Term.elabTerm (mkCIdent ``default) type
    let val ← whnf val
    let ctor := val.getAppFn
    if let .const ctorName _ := val.getAppFn then
      let ctorInfo ← getConstInfoCtor ctorName
      return some (ctor, ctorInfo.name)
    else
      return none
  catch _ =>
    return none

/--
Try to construct a proof for `Infinite α` by forming an injection from a `α`-valued field to the
subset of `α` created with this constructor, and then using `Infinite.of_injective_to_set`.
To prove that this subset is proper, we show that the `default` element of `α` is not headed by
this constructor (if `default` is headed by this constructor, then this function fails).
-/
private def mkProofSelf (ctorInfo : ConstructorVal) (xs : Array Expr) (self : Expr)
    (defaultCtor : Name) : TermElabM (Option Term) := do
  if ctorInfo.name == defaultCtor then
    return none

  let mut selfField := none
  for i in [:ctorInfo.numFields] do
    let x := xs[ctorInfo.numParams + i]!
    let xTy ← inferType x
    let isSelf ← withNewMCtxDepth (isDefEq self xTy)
    let nonempty ← trySynthInstance (← mkAppM ``Nonempty #[xTy]) <&> LOption.toOption

    let tracePrefix := m!"{ctorInfo.name} field {i}: "
    trace[Elab.Deriving.infinite] tracePrefix ++ m!"isSelf={isSelf} nonempty={nonempty}"

    match selfField, isSelf, nonempty with
    | _, false, none => -- field is neither self nor Nonempty
      trace[Elab.Deriving.infinite] tracePrefix ++
        "not Nonempty or recursive; giving up on this constructor"
      return none
    | none, true, _ => -- first self field found
      selfField := some i
    | _, true, none => -- this field is only self, not Nonempty
      selfField := some i
    | _, _, _ => pure ()

  let some j := selfField
    | return none
  let (obj, holeArg, addNonemptyElim) ← mkObj ctorInfo j
  let noConfusion := mkCIdent <| ctorInfo.induct.str "noConfusion"
  let noConfusionMotive ← mkNoConfusionMotive ctorInfo xs self j
  let val ←
    `(let S := {x | ∃ $holeArg:ident, $obj = x}
      let notUniv : S ≠ $(mkCIdent ``Set.univ) := fun h =>
        (h ▸ show $(mkCIdent ``default) ∉ S from fun ⟨_, h₂⟩ => $noConfusion h₂)
        $(mkCIdent ``trivial)
      let f : _ → S := fun $holeArg:ident => ⟨$obj, $holeArg, rfl⟩
      let inj : $(mkCIdent ``Function.Injective) f := fun _ _ h =>
        $(mkCIdent ``Subtype.noConfusion) h fun h₂ => $noConfusion h₂ $noConfusionMotive
      $(mkCIdent ``infinite_of_injective_to_set) notUniv inj)
  addNonemptyElim val

/--
The `derive_infinite%` term elaborator attempts to derive an instance of `Infinite α`.
The type `α` is obtained from the expected type.

The syntax `derive_infinite% α` is short for `(derive_infinite% : Infinite α)`.
-/
syntax (name := deriveInfinite) "derive_infinite%" (colGt term:arg)? : term

macro_rules | `(derive_infinite% $t) => `((derive_infinite% : Infinite $t))

/--
Extracts `type` from `Infinite type` in the expected type.
Postpones elaboration if the expected type isn't of this form.
-/
private def extractType (expectedType? : Option Expr) :
    TermElabM (Expr × List Level × InductiveVal) := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let throwMustBeKnown {α} : TermElabM α := throwError "\
    expected type must be of the form `Infinite t` where `t` is an inductive type."
  let some expectedType := expectedType?
    | throwMustBeKnown
  let_expr Infinite type := (← whnf expectedType)
    | throwMustBeKnown
  Term.tryPostponeIfMVar type
  let type ← instantiateMVars (← whnf type)
  matchConstInduct type.getAppFn (fun _ => throwMustBeKnown)
    (fun ival us => return (type, us, ival))

@[term_elab deriveInfinite]
private def elabDeriveInfinite : Term.TermElab := fun _ expectedType? => do
  let (type, us, indVal) ← extractType expectedType?
  trace[Elab.Deriving.infinite] "deriving for type {.ofConstName indVal.name},{indentExpr type}"
  let getProof f : TermElabM (Option Term) :=
    indVal.ctors.findSomeM? fun ctorName => do
      let ctorInfo ← getConstInfoCtor ctorName
      let (xs, _, x) ← forallMetaTelescopeReducing (ctorInfo.instantiateTypeLevelParams us)
      if ← isDefEqGuarded type x then
        f ctorInfo xs x
      else
        trace[Elab.Deriving.infinite]
          "{ctorName}: cannot unify{indentExpr type}\nwith{indentExpr x}"
        return none
  let mut proof ← getProof mkProofField
  if proof.isNone then
    if let some (ctor, ctorName) ← getDefaultCtor type then
      trace[Elab.Deriving.infinite]
        "Trying to prove from self (default value uses constructor {ctor})"
      proof ← getProof (mkProofSelf (defaultCtor := ctorName))
  let some proofVal := proof
    | throwError "cannot derive {← mkAppM ``Infinite #[type]}"
  trace[Elab.Deriving.infinite] "elaborated as{indentD proofVal}"
  Term.elabTerm proofVal expectedType?

/-!
### Deriving handler
-/

private def mkInfiniteInstanceCmd (declName : Name) : TermElabM Command := do
  let indVal       ← getConstInfoInduct declName
  if indVal.numIndices ≠ 0 then
    throwError "indexed inductive types are not supported"
  let argNames     ← Deriving.mkInductArgNames indVal
  let binders      ← Deriving.mkImplicitBinders argNames
  let indType      ← Deriving.mkInductiveApp indVal argNames
  let type         ← `($(mkCIdent ``Infinite) $indType)
  let instCmd      ← `(instance $binders:implicitBinder* : $type := derive_infinite%)
  trace[Elab.Deriving.infinite] "{instCmd}"
  return instCmd

/--
Deriving handler for `Infinite`.
Does not support inductive types that have indices or are mutually recursive.

It is essentially equivalent to
```
instance [Infinite α₁] ... [Infinite αₙ] : Infinite (Ty α₁ ... αₙ) :=
  derive_infinite% _
```
and this `derive_infinite%` term elaborator can be used to create instances that need
other assumptions.
-/
def mkInfiniteHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← declNames.allM isInductive) then
    let cmd ← liftTermElabM <| mkInfiniteInstanceCmd declNames[0]!
    elabCommand cmd
    return true
  else
    return false

initialize
  registerDerivingHandler ``Infinite mkInfiniteHandler
  registerTraceClass `Elab.Deriving.infinite

end Mathlib.Deriving.Infinite
