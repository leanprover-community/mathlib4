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

private theorem infinite_of_injective {α β : Sort _} [Infinite α]
    (f : α → β) (hf : Function.Injective f) : Infinite β :=
  Infinite.of_injective f hf

private theorem infinite_of_injective_to_set {α : Type _} {s : Set α} (hs : s ≠ Set.univ)
    {f : α → s} (hf : Function.Injective f) : Infinite α :=
  Infinite.of_injective_to_set hs hf

private theorem infinite_of_proper_injection {α : Sort _}
    {f : α → α} (hf : Function.Injective f) (hf' : ¬ Function.Surjective f) : Infinite α := by
  let f' : PLift α → PLift α := fun x => PLift.up (f x.down)
  let hf : Function.Injective f' := by
    intro x y h
    apply PLift.down_injective
    apply hf
    rw [← PLift.up.injEq]
    exact h
  let hf' : ¬ Function.Surjective f' := by
    contrapose! hf'
    intro y
    obtain ⟨x, hx⟩ := hf' (PLift.up y)
    use x.down
    rw [← PLift.up.injEq]
    exact hx
  rw [← not_finite_iff_infinite]
  by_contra
  have := Finite.surjective_of_injective hf
  exact absurd this hf'

private theorem infinite_of_proper_injection' {α : Sort _}
    {f : α → α} (hf : Function.Injective f)
    (x : α) (hx : ∀ a : α, f a ≠ x) : Infinite α := by
  apply infinite_of_proper_injection hf
  intro h
  specialize h x
  simp [hx] at h

private def fn_of_empty_dom {α : Sort _} [IsEmpty α] {β : α → Sort _} : (x : α) → β x :=
  IsEmpty.elim inferInstance

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
Adds inhabited instances for each expression in `xs`.
Calls `k` with the additional local instance fvars.

Avoids adding `Inhabited (Inhabited α)` instances.
-/
private def withInhabitedInstances {α} (xs : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (insts : Array Expr) : MetaM α := do
    if h : i < xs.size then
      let x := xs[i]
      let xTy ← instantiateMVars (← inferType x)
      if xTy.isAppOf ``Inhabited || xTy.isAppOf ``Nonempty then
        go (i + 1) insts
      else
        let u ← getLevel xTy
        let instTy := mkApp (.const ``Inhabited [u]) xTy
        let instVal := mkApp2 (.const ``Inhabited.mk [u]) xTy x
        withLetDecl `inst instTy instVal fun inst =>
          go (i + 1) (insts.push inst)
    else
      k insts
  go 0 #[]

private def withInhabitedInstances' (xs : Array Expr) (k : MetaM Expr) :
    MetaM Expr := do
  withInhabitedInstances xs fun insts => do
    let val ← k
    mkLetFVars (usedLetOnly := true) insts val

mutual

/--
Find an inhabitant (non)constructively.
1. Looks for instances of Inhabited or Nonempty.
2. Goes under binders, adding parameters as new Inhabited instances.
3. Delta unfolds definitions.
4. Makes use of constructors of inductive types with inhabited fields.
-/
private partial def mkInhabitantForAux (visitedTypes : NameSet) (type : Expr) :
    MetaM Expr := withIncRecDepth do
  -- Is there an `Inhabited` instance?
  if let some val ← observing? (mkDefault type) then
    return val
  -- Is there a `Nonempty` instance?
  else if let some val ← observing? (mkOfNonempty type) then
    return val
  else
    let type ← whnfCore type
    -- Is it a forall we can descend under?
    if type.isForall then
      forallTelescope type fun xs type' => do
        -- If any of these binders are empty, we can eliminate immediately.
        for x in xs do
          try
            let inst ← synthInstance (← mkAppM ``IsEmpty #[← inferType x])
            let val ← mkAppOptM ``IsEmpty.elim' #[none, type', inst, x]
            return ← mkLambdaFVars xs val
          catch _ => pure ()
        -- Otherwise descend.
        withInhabitedInstances xs fun insts => do
          let val ← mkInhabitantForAux visitedTypes type'
          mkLambdaFVars xs (← mkLetFVars (usedLetOnly := true) insts val)
    -- Try doing a step of unfolding
    else if let some type' ← unfoldDefinition? type then
      mkInhabitantForAux visitedTypes type'
    else
      -- If it's an inductive type, try finding a constructor with inhabited fields.
      matchConstInduct type.getAppFn
        (fun _ => failure)
        (fun ival us => do
          guard <| !visitedTypes.contains ival.name
          let visitedTypes := visitedTypes.insert ival.name
          Option.getM <| ← ival.ctors.findSomeM? fun ctorName =>
            observing? (mkInhabitantForCtorAux visitedTypes ctorName us type))

private partial def mkInhabitantForCtorAux
    (visitedTypes : NameSet) (ctorName : Name) (us : List Level) (type : Expr) :
    MetaM Expr := do
  let ctorInfo ← getConstInfoCtor ctorName
  let (args, _, ty) ←
    forallMetaTelescopeReducing (ctorInfo.instantiateTypeLevelParams us)
  guard (← isDefEq type ty)
  for arg in args[ctorInfo.numParams:] do
    -- Assumption: if it was assigned to anything, then a parameter is responsible for it.
    unless ← arg.mvarId!.isAssigned do
      let argVal ← mkInhabitantForAux visitedTypes (← inferType arg)
      guard (← isDefEq arg argVal)
      let arg ← instantiateMVars arg
      if arg.isMVar then
        guard <| ← arg.mvarId!.checkedAssign argVal
  return ← instantiateMVars (mkAppN (.const ctorInfo.name us) args)

end

/-- Tries to synthesize a term of the given type. -/
private def mkInhabitantFor (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  withNewMCtxDepth do
    withInhabitedInstances' (← getLCtx).getFVars do mkInhabitantForAux {} type

/-- Tries to synthesize a term of the given constructor, or throws an exception. -/
private def mkInhabitantForCtor (ctorName : Name) (us : List Level)
    (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  withNewMCtxDepth do
    withInhabitedInstances' (← getLCtx).getFVars do mkInhabitantForCtorAux {} ctorName us type

/--
Constructs an inhabitant for the expected type, if possible.
-/
elab (name := inhabit) "inhabit%" : term <= expectedType => do
  try
    mkInhabitantFor expectedType
  catch _ =>
    throwError "could not construct inhabitant of type{indentExpr expectedType}"

structure A (α : Type) (a : α) where
  a : α
  b : Nat
#check A.mk.inj
#check fun α a => (inhabit% : A α a)

private theorem injective_id (α) : Function.Injective (id : α → α) := Function.injective_id

private theorem injective_insert_pi {α β γ} (g : γ)
    {f : α → β} (hf : Function.Injective f) :
    Function.Injective (fun (x : α) (_ : γ) => f x) := by
  intro x1 x2 h
  exact hf (congr_fun h g)

/--
Tries to make an injection `dom → codom`.
Abstracts `dom` from the `codom` type.

Returns the injectivity proof.
If `h : Expr` is the proof then `(← inferType h).appArg!` is the function.
-/
private partial def mkInj (dom codom : Expr) : MetaM Expr := do
  let dom ← instantiateMVars dom
  let codom ← instantiateMVars codom
  let dom' ← kabstract codom dom
  -- If `dom` does not appear in `codom`, then we don't try to create an injection.
  -- The only way an injection could still exist is if `dom` were defined before `codom`,
  -- but in our case `dom` is always the new type.
  guard dom'.hasLooseBVars
  withLocalDeclD `self (← inferType dom) fun self => do
    let codom' := codom.instantiate1 self
    -- We should make sure that the abstracted codomain is type correct:
    check codom'
    mkInjAux {} self codom'
where
  mkInjAux (visitedTypes : NameSet) (self codom : Expr) : MetaM Expr := do
    let codom ← whnf codom
    -- Base case: `self → self`
    if codom == self then
      mkAppM ``injective_id #[self]
    -- For the `self → α → β` case, we only try making an injection `self → β`
    else if codom.isForall then
      -- Only non-dependent functions are supported
      guard <| codom.isArrow
      let p ← mkInhabitantFor codom.bindingDomain!
      withLocalDeclD codom.bindingName! codom.bindingDomain! fun param => do
        let inj ← mkInjAux visitedTypes self codom
        let pf ← mkAppM ``injective_insert_pi #[p, inj]
        let pf ← mkLambdaFVars #[param] pf
        return pf.bindingBody!.instantiate1 p
    else
      -- Otherwise, try to find a constructor that can be used to create the injection.
      matchConstInduct codom.getAppFn
        (fun _ => failure)
        (fun ival us => do
          guard <| !visitedTypes.contains ival.name
          let visitedTypes := visitedTypes.insert ival.name
          Option.getM <| ← ival.ctors.findSomeM? fun ctorName =>
            observing? (mkInjForCtor visitedTypes self codom ctorName us))
  /--
  Try to create an injection `self -> codom` using the given constructor.
  Strategy: locate a field for which there is an injection,
  and try to inhabit the remaining fields.
  -/
  mkInjForCtor (visitedTypes : NameSet) (self codom : Expr) (ctorName : Name) (us : List Level) :
      MetaM Expr := do
    let injThmName := mkInjectiveTheoremNameFor ctorName
    guard <| (← getEnv).contains injThmName
    let ctorInfo ← getConstInfoCtor ctorName
    let (args, _, ty) ← forallMetaTelescopeReducing (ctorInfo.instantiateTypeLevelParams us)
    guard <| ← withNewMCtxDepth <| isDefEq codom ty
    withLocalDeclD `x self fun x => do
      -- Inhabited values for each field. Note: the values may depend on `x`.
      -- Another note: we won't use the inhabitant for the field that we will use for the injection.
      let mut vals : Array Expr ←
        args[ctorInfo.numParams:].foldlM (init := #[]) fun vals arg => do
          -- Assumption: if it was assigned to anything, then a parameter is responsible for it.
          if ← arg.mvarId!.isAssigned then
            return vals.push arg
          else
            let val ← mkInhabitantFor (← inferType arg)
            return vals.push val
      -- Now look for a field that can be used for injection.
      for i in [0:ctorInfo.numFields] do
        let arg := args[ctorInfo.numParams + i]!
        unless (← arg.mvarId!.isAssigned) do
          if let some inji ← observing? (mkInjAux visitedTypes self (← inferType arg)) then
            -- There is an injectivity proof for this field.
            -- Given that we have inhabitants for all other fields, we now commit to it.
            -- Step 1: get the function from the proof
            let fi := (← inferType inji).appArg!
            -- Step 2: assign `arg` using `fi x`
            guard <| ← arg.mvarId!.checkedAssign (mkApp fi x)
            -- Step 3: assign all other arguments to the values in `vals`
            for j in [0:ctorInfo.numFields] do
              let argj := args[ctorInfo.numParams + j]!
              let valj := vals[ctorInfo.numParams + j]!
              unless ← argj.mvarId!.isAssigned do
                guard (← isDefEq argj valj)
                let argj ← instantiateMVars argj
                if argj.isMVar then
                  guard <| ← argj.mvarId!.checkedAssign valj
            -- Step 4: build the injection function
            let f ← mkLambdaFVars #[x] (mkAppN (.const ctorName us) args)
            -- Step 5: prove that it is an injection
            let injTy ← mkAppM ``Function.Injective #[f]
            let injPf ← mkFreshExprSyntheticOpaqueMVar injTy
            let (eq, g) ← injPf.mvarId!.intro `h
            g.withContext do
              let mut val ← mkAppM injThmName #[Expr.fvar eq]
              for _ in [0:i] do
                val ← mkAppM ``And.right #[val]
              if i + 1 < ctorInfo.numFields then
                val ← mkAppM ``And.left #[val]
              if (← whnf (← inferType val)).isHEq then
                val ← mkEqOfHEq val
              g.assignIfDefEq (← mkAppM' inji #[val])
            return ← mkExpectedTypeHint injPf injTy
      -- No injectivity proof.
      failure

inductive Baz (β : Type) where
  | mk (n : Nat) (b : β) (c : Baz β)

example {β : Type} (fi : Baz β → β) (hfi : Function.Injective fi) :
    let f : Baz β → Baz β := fun x => Baz.mk default (fi x) sorry
    Function.Injective f := by
  intro f a b h
  have := Baz.mk.inj h

  sorry

/--
Tries to use the given constructor for the type `α` to construct an injection `α → α`.
Returns the injection and the proof of injectivity.
-/
private def mkInjOfCtor (ival : InductiveVal) (ctorName : Name) (us : List Level) (type : Expr) :
    MetaM (Expr × Expr) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let (args, _, ty) ← forallMetaTelescopeReducing (ctorInfo.instantiateTypeLevelParams us)
  guard (← isDefEq type ty)
  let type ← instantiateMVars type
  withLocalDeclD `self type fun self => do
    failure

/--
For each constructor, tries to use it to inhabit the type `type`.
-/
private def inhabitCtors (ival : InductiveVal) (us : List Level) (type : Expr) :
    MetaM (List Expr) :=
  ival.ctors.filterMapM fun ctorName =>
    observing? (mkInhabitantForCtor ival ctorName us type)

/--
If there is a constructor with an `Infinite` field, with all other fields inhabited,
returns a proof of `Infinite type`.
-/
private def infiniteOfCtor (ival : InductiveVal) (us : List Level) (type : Expr) :
    MetaM Expr := do
  for ctorName in ival.ctors do
    let state ← saveState
    try
      let ctorInfo ← getConstInfoCtor ctorName
      let (args, _, ty) ←
        forallMetaTelescopeReducing (ctorInfo.instantiateTypeLevelParams us)
      guard (← isDefEq type ty)
      for arg in args[ival.numParams:] do
        let arg ← instantiateMVars arg
        if arg.hasExprMVar then
          let some argVal ← mkInhabitantFor? (← inferType arg)
            | failure
          guard (← isDefEq arg argVal)
          if arg.isMVar then
            arg.mvarId!.assign argVal
      return ← instantiateMVars (mkAppN (.const ctorInfo.name us) args)
    catch _ =>
      restoreState state
  failure

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
  matchConstInduct type.getAppFn
    (fun _ => throwMustBeKnown)
    (fun ival us => return (type, us, ival))

@[term_elab deriveInfinite]
def elabDeriveInfinite : Term.TermElab := fun _ expectedType? => do
  let (type, us, indVal) ← extractType expectedType?
  if indVal.isUnsafe then
    throwError "unsafe inductive types are not supported"
  unless indVal.numIndices = 0 do
    throwError "indexed inductive types are not supported"
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
  if indVal.isUnsafe then
    throwError "unsafe inductive types are not supported"
  unless indVal.numIndices = 0 do
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
