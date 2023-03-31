/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# The `Fintype` derive handler

This file defines a derive handler to automatically generate `Fintype` instances
for structures and inductive types.

The following is a prototypical example of what this can handle:
```
inductive MyOption (α : Type _)
  | none
  | some (x : α)
  deriving Fintype
```

This deriving handler does not attempt to process inductive types that are either
recursive or that have indices.

To get debugging information, do `set_option trace.Elab.Deriving.fintype true`.

## Implementation notes

There are two kinds of `Fintype` instances that we generate, depending on the inductive type.

If it is an enum (an inductive type with only 0-ary constructors), then we generate the
complete `List` of all constructors; see `Mathlib.Deriving.Fintype.mkFintypeEnum` for more
details. The proof has $O(n)$ complexity in the number of constructors.

Otherwise, the strategy we take is to generate a "proxy type", define an equivalence between
our type and the proxy type, and then use `Fintype.ofEquiv` to pull a `Fintype` instance on
the proxy type (if one exists) to our inductive type. For example, with the `MyOption α` type
above, we generate `Unit ⊕ α`. While the proxy type is not a finite type in general, we add
`Fintype` instances for every type parameter of our inductive type (and `Decidable` instances
for every `Prop` parameter). Hence, in our example we get `Fintype (MyOption α)` assuming
`Fintype α`.

There is a source of quadratic complexity in this `Fintype` instance from the fact that an
inductive type with `n` constructors has a proxy type of the form `C₁ ⊕ (C₂ ⊕ (⋯ ⊕ Cₙ))`,
so mapping to and from `Cᵢ` requires looking through `i` levels of `Sum` constructors.
Ignoring this, the construction of `Finset.univ` takes linear time in the cardinality of the type
since the instances involved compute the underlying `List` for the `Finset`
as `l₁ ++ (l₂ ++ (⋯ ++ lₙ))` with right associativity.

This implementation takes some inspiration from the one by Mario Carneiro for Mathlib 3.
A difference is that Mario does not explicitly construct the total proxy type, instead opting to
construct the underlying `Finset` as a disjoint union of the `Finset.univ` for each individual
constructor's proxy type.
-/

namespace Mathlib.Deriving.Fintype
open Lean Elab Lean.Parser.Term
open Meta Command

/-- Returns the portion of the proxy type for the constructor with arguments `xs`,
the list of names used in the pattern, and the pattern for matching an element of this type. -/
def mkCtorType (xs : List Expr) : TermElabM (Expr × List Name × TSyntax `term) :=
  match xs with
  | [] => return (mkConst ``Unit, [], ← `(term| ()))
  | [x] => do
    let a ← mkFreshUserName `a
    return (← inferType x, [a], mkIdent a)
  | x :: xs => do
    let (ty, names, patt) ← mkCtorType xs
    let ty ← mkAppM ``PSigma #[← mkLambdaFVars #[x] ty]
    let a ← mkFreshUserName `a
    return (ty, a :: names, ← `(term| ⟨$(mkIdent a), $patt⟩))

/-- Navigates into the sum type that we create in `mkCType` for the given constructor index. -/
def wrapSumAccess (cidx nctors : Nat) (spatt : TSyntax `term) : TermElabM (TSyntax `term) :=
  match cidx with
  | 0 =>
    if nctors = 1 then
      return spatt
    else
      `(term| Sum.inl $spatt)
  | cidx' + 1 => do
    let spatt ← wrapSumAccess cidx' (nctors - 1) spatt
    `(term| Sum.inr $spatt)

/-- Create a `Sum` of types, mildly optimized to not have a trailing `Empty`.
Returns also the necessary tactic for the `left_inv` proof in the `Equiv` we construct. -/
def mkCType (ctypes : List Expr) : TermElabM (Expr × TSyntax `tactic) :=
  match ctypes with
  | [] => return (mkConst ``Empty, ← `(tactic| cases x))
  | [x] => return (x, ← `(tactic| rfl))
  | x :: xs => do
    let (ty, pf) ← mkCType xs
    let pf ← `(tactic| cases x with | inl _ => rfl | inr x => $pf:tactic)
    return (← mkAppM ``Sum #[x, ty], pf)

/--
Generates a proxy type for the inductive type (defining it at `fintypeProxy` in the
inductive type's namespace).
Creates a `Fintype` instance by creating an equivalence to this proxy type, where we
add additional `Fintype` and `Decidable` instance arguments for every type and prop
parameter of the type.
-/
def mkFintypeInstance (indVal : InductiveVal) : TermElabM (TSyntax `command) := do
  let levels := indVal.levelParams.map Level.param
  let proxyName := indVal.name.mkStr "fintypeProxy"
  forallBoundedTelescope indVal.type indVal.numParams fun params _sort => do
    let mut cdata := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
      cdata := cdata.push <| ←
        forallBoundedTelescope ctorType ctorInfo.numFields fun xs _itype => do
          let mut (ty, names, patt) ← mkCtorType xs.toList
          if ← Meta.isProp ty then
            -- We're using `Sum`, so insert a `PLift`.
            ty ← mkAppM ``PLift #[ty]
            patt ← `(term| ⟨$patt⟩)
          let places := mkArray ctorInfo.numParams (← `(term| _))
          let argNames := (names.map mkIdent).toArray
          let tpatt ← `(term| @$(mkIdent ctorName) $places* $argNames*)
          let spatt ← wrapSumAccess ctorInfo.cidx indVal.numCtors patt
          return (ctorName, ty, tpatt, spatt)
    let mut ctypes := #[]
    let mut toFunAlts := #[]
    let mut invFunAlts := #[]
    for (_, ty, tpatt, spatt) in cdata do
      ctypes := ctypes.push ty
      toFunAlts := toFunAlts.push <| ← `(matchAltExpr| | $spatt => $tpatt)
      invFunAlts := invFunAlts.push <| ← `(matchAltExpr| | $tpatt => $spatt)

    -- Create the proxy type definition
    let (ctype, pf) ← mkCType ctypes.toList
    trace[Elab.Deriving.fintype] "proxy type: {ctype}"
    let ctype' ← mkLambdaFVars params ctype
    addAndCompile <| Declaration.defnDecl
      { name := proxyName
        levelParams := indVal.levelParams
        safety := DefinitionSafety.safe
        hints := ReducibilityHints.abbrev
        type := (← inferType ctype')
        value := ctype' }
    -- Set to be reducible so that typeclass inference can see it's a Fintype
    setReducibleAttribute proxyName
    trace[Elab.Deriving.fintype] "defined {proxyName}"

    -- Create the Fintype instance command
    let mut toFun ← `(term| fun $toFunAlts:matchAlt*)
    let mut invFun ← `(term| fun $invFunAlts:matchAlt*)
    if indVal.numCtors == 0 then
      -- Empty matches don't elaborate, so use `nomatch` here.
      toFun ← `(term| fun x => nomatch x)
      invFun ← `(term| fun x => nomatch x)
    let equivBody ← `(term|
      { toFun := $toFun,
        invFun := $invFun,
        right_inv := by intro x; cases x <;> rfl
        left_inv := by intro x; $pf:tactic })
    let header ← Deriving.mkHeader `Fintype 0 indVal
    let args := header.argNames.map mkIdent
    let binders' ← Deriving.mkInstImplicitBinders `Decidable indVal header.argNames
    let instCmd ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          Fintype $header.targetType :=
        Fintype.ofEquiv (@$(mkIdent proxyName) $args*) $equivBody)
    trace[Elab.Deriving.fintype] "inst: {instCmd}"
    return instCmd

def mkFintype (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  if indVal.isRec then
    throwError
      "deriving Fintype: recursive inductive types are not supported (and are usually infinite)"
  if 0 < indVal.numIndices then
    throwError
      "deriving Fintype: inductive indices are not supported"
  let cmd ← liftTermElabM <| mkFintypeInstance indVal
  elabCommand cmd
  return true

/-- Derive a `Fintype` instance for enum types. These come with a `toCtorIdx` function.
The strategy is to (1) create a list `enumList` of all the constructors, (2) prove that this
is in `toCtorIdx` order, (3) show that `toCtorIdx` maps `enumList` to `List.range numCtors` to show
the list has no duplicates, and (4) give the `Fintype` instance, using 2 for completeness.

The proofs are all linear complexity, and the main computation is that
`enumList.map toCtorIdx = List.range numCtors`, which is true by `refl`. -/
def mkFintypeEnum (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let levels := indVal.levelParams.map Level.param
  let toCtorIdxName := declName.mkStr "toCtorIdx"
  let enumListName := declName.mkStr "enumList"
  let toCtorThmName := declName.mkStr "enumList_get?_to_CtorIdx_eq"
  let enumListNodupName := declName.mkStr "enumList_nodup"
  liftTermElabM <| Term.withoutErrToSorry do
    do -- Define `enumList` enumerating all constructors
      trace[Elab.Deriving.fintype] "defining {enumListName}"
      let type := mkConst declName levels
      let listType ← mkAppM ``List #[type]
      let listNil ← mkAppOptM ``List.nil #[some type]
      let listCons name xs := mkAppM ``List.cons #[mkConst name levels, xs]
      let enumList ← indVal.ctors.foldrM (listCons · ·) listNil
      addAndCompile <| Declaration.defnDecl
        { name := enumListName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := listType
          value := enumList }
    do -- Prove that this list is in `toCtorIdx` order
      trace[Elab.Deriving.fintype] "proving {toCtorThmName}"
      let goalStx ← `(term| ∀ (x : $(← Term.exprToSyntax <| mkConst declName levels)),
        List.get? $(mkIdent enumListName) ($(mkIdent toCtorIdxName) x) = some x)
      let goal ← Term.elabTerm goalStx (mkSort .zero)
      let pf ← Term.elabTerm (← `(term| by intro x; cases x <;> rfl)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      addAndCompile <| Declaration.thmDecl
        { name := toCtorThmName
          levelParams := indVal.levelParams
          type := ← instantiateMVars goal
          value := ← instantiateMVars pf }
    do -- Use this theorem to prove `enumList` has no duplicates
      trace[Elab.Deriving.fintype] "proving {enumListNodupName}"
      let enum ← Term.exprToSyntax <| mkConst enumListName levels
      let goal ← Term.elabTerm (← `(term| List.Nodup $enum)) (mkSort .zero)
      let n : TSyntax `term := quote indVal.numCtors
      let pf ← Term.elabTerm (← `(term| by
                  apply List.Nodup.of_map $(mkIdent toCtorIdxName)
                  have h : List.map $(mkIdent toCtorIdxName) $(mkIdent enumListName)
                            = List.range $n := rfl
                  exact h ▸ List.nodup_range $n)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      addAndCompile <| Declaration.thmDecl
        { name := enumListNodupName
          levelParams := indVal.levelParams
          type := ← instantiateMVars goal
          value := ← instantiateMVars pf }
  -- Make the Fintype instance
  trace[Elab.Deriving.fintype] "defining fintype instance"
  let cmd ← `(command|
    instance : Fintype $(mkIdent declName) where
      elems := Finset.mk $(mkIdent enumListName) $(mkIdent enumListNodupName)
      complete := by
        intro x
        rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_get?]
        exact ⟨$(mkIdent toCtorIdxName) x, $(mkIdent toCtorThmName) x⟩)
  trace[Elab.Deriving.fintype] "instance command:\n{cmd}"
  elabCommand cmd

def mkFintypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported yet
  let declName := declNames[0]!
  if ← isEnumType declName then
    mkFintypeEnum declName
    return true
  else
    mkFintype declName

initialize
  registerDerivingHandler `Fintype mkFintypeInstanceHandler
  registerTraceClass `Elab.Deriving.fintype

end Mathlib.Deriving.Fintype
