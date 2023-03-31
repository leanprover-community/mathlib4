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

There is a term elaborator `derive_fintype%` implementing the derivation of `Fintype` instances.
This can be useful in cases when there are necessary additional assumptions (like `DecidableEq`).

Underlying this is a term elaborator `proxy_equiv%` for creating an equivalence from a
"proxy type" composed of basic type constructors to the inductive type.

## Implementation notes

There are two kinds of `Fintype` instances that we generate, depending on the inductive type.

If it is an enum (an inductive type with only 0-ary constructors), then we generate the
complete `List` of all constructors; see `Mathlib.Deriving.Fintype.mkFintypeEnum` for more
details. The proof has $O(n)$ complexity in the number of constructors.

Otherwise, the strategy we take is to generate a "proxy type", define an equivalence between
our type and the proxy type (see `proxy_equiv%`), and then use `Fintype.ofEquiv` to pull a
`Fintype` instance on the proxy type (if one exists) to our inductive type. For example, with
the `MyOption α` type above, we generate `Unit ⊕ α`. While the proxy type is not a finite type
in general, we add `Fintype` instances for every type parameter of our inductive type (and
`Decidable` instances for every `Prop` parameter). Hence, in our example we get
`Fintype (MyOption α)` assuming `Fintype α`.

There is a source of quadratic complexity in this `Fintype` instance from the fact that an
inductive type with `n` constructors has a proxy type of the form `C₁ ⊕ (C₂ ⊕ (⋯ ⊕ Cₙ))`,
so mapping to and from `Cᵢ` requires looking through `i` levels of `Sum` constructors.
Ignoring time spent looking through these constructors, the construction of `Finset.univ`
contributes linear time with respect to the cardinality of the type since the instances
involved compute the underlying `List` for the `Finset` as `l₁ ++ (l₂ ++ (⋯ ++ lₙ))` with
right associativity.

Note that an alterantive design could be that instead of using `Sum` we could create a
function `C : Fin n → Type _` with `C i = ulift Cᵢ` and then use `(i : Fin n) × C i` for
the proxy type, which would save us from the nested `Sum` constructors.

This implementation takes some inspiration from the one by Mario Carneiro for Mathlib 3.
A difference is that the Mathlib 3 version does not explicitly construct the total proxy type,
and instead it opts to construct the underlying `Finset` as a disjoint union of the `Finset.univ`
for each individual constructor's proxy type.
-/

namespace Mathlib.Deriving.Fintype
open Lean Elab Lean.Parser.Term
open Meta Command

/-- Returns the portion of the proxy type corresponding to a constructor with arguments `xs`.
Also returns data for the pattern for matching an element of this type: the list of names and
the pattern itself.

Always returns a `Type _`. Uses `Unit`, `PLift`, and `Sigma`. Avoids using `PSigma` since
then the `Fintype` instances for it go through `Sigma`s anyway. -/
def mkCtorType (xs : List Expr) : TermElabM (Expr × List Name × TSyntax `term) :=
  match xs with
  | [] => return (mkConst ``Unit, [], ← `(term| ()))
  | [x] => do
    let a ← mkFreshUserName `a
    let xty ← inferType x
    if ← Meta.isProp xty then
      return (← mkAppM ``PLift #[xty], [a], ← `(term| ⟨$(mkIdent a)⟩))
    else
      return (xty, [a], mkIdent a)
  | x :: xs => do
    let (xsty, names, patt) ← mkCtorType xs
    let a ← mkFreshUserName `a
    let xty ← inferType x
    if ← Meta.isProp xty then
      withLocalDeclD `x' (← mkAppM ``PLift #[xty]) fun x' => do
        let xsty' := xsty.replaceFVar x (← mkAppM ``PLift.down #[x'])
        let ty ← mkAppM ``Sigma #[← mkLambdaFVars #[x'] xsty']
        return (ty, a :: names, ← `(term| ⟨⟨$(mkIdent a)⟩, $patt⟩))
    else
      let ty ← mkAppM ``Sigma #[← mkLambdaFVars #[x] xsty]
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
Returns also the necessary tactic for the `left_inv` proof in the `Equiv` we construct.
This proof assumes we start with `intro x`. -/
def mkCType (ctypes : List Expr) : TermElabM (Expr × TSyntax `tactic) :=
  match ctypes with
  | [] => return (mkConst ``Empty, ← `(tactic| cases x))
  | [x] => return (x, ← `(tactic| rfl))
  | x :: xs => do
    let (ty, pf) ← mkCType xs
    let pf ← `(tactic| cases x with | inl _ => rfl | inr x => $pf:tactic)
    return (← mkAppM ``Sum #[x, ty], pf)

/-- Names of the auxiliary definitions created by `mkProxyEquiv`. -/
structure EquivData where
  /-- Name of the declaration for a type that is `Equiv` to the given type. -/
  proxyName : Name
  /-- Name of the declaration for the equivalenec `proxyType ≃ type`. -/
  proxyEquivName : Name

/--
Generates a proxy type for the inductive type and an equivalence from the proxy type to the type.
The resulting declaration names are returned.

If the declarations already exist, there is a check that they are correct.
-/
def mkProxyEquiv (indVal : InductiveVal) : TermElabM EquivData := do
  if indVal.isRec then
    throwError
      "proxy equivalence: recursive inductive types are not supported (and are usually infinite)"
  if 0 < indVal.numIndices then
    throwError "proxy equivalence: inductive indices are not supported"
  let levels := indVal.levelParams.map Level.param
  let proxyName := indVal.name.mkStr "proxyType"
  let proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  forallBoundedTelescope indVal.type indVal.numParams fun params _sort => do
    let mut cdata := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
      cdata := cdata.push <| ←
        forallBoundedTelescope ctorType ctorInfo.numFields fun xs _itype => do
          let (ty, names, patt) ← mkCtorType xs.toList
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
    if let some const := (← getEnv).find? proxyName then
      unless ← isDefEq const.value! ctype' do
        throwError "Declaration {proxyName} already exists and it is not the proxy type."
      trace[Elab.Deriving.fintype] "proxy type already exists"
    else
      addAndCompile <| Declaration.defnDecl
        { name := proxyName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := (← inferType ctype')
          value := ctype' }
      -- Set to be reducible so that typeclass inference can see it's a Fintype
      setReducibleAttribute proxyName
      setProtected proxyName
      trace[Elab.Deriving.fintype] "defined {proxyName}"

    -- Create the `Equiv`
    let mut toFun ← `(term| fun $toFunAlts:matchAlt*)
    let mut invFun ← `(term| fun $invFunAlts:matchAlt*)
    if indVal.numCtors == 0 then
      -- Empty matches don't elaborate, so use `nomatch` here.
      toFun ← `(term| fun x => nomatch x)
      invFun ← `(term| fun x => nomatch x)
    let equivBody ← `(term| { toFun := $toFun,
                              invFun := $invFun,
                              right_inv := by intro x; cases x <;> rfl
                              left_inv := by intro x; $pf:tactic })
    let equivType ← mkAppM ``Equiv #[ctype, mkAppN (mkConst indVal.name levels) params]
    equivType.ensureHasNoMVars
    let equiv ← Term.elabTerm equivBody equivType
    Term.synthesizeSyntheticMVarsNoPostponing
    let equiv ← instantiateMVars equiv
    let equiv' ← mkLambdaFVars params equiv
    equiv'.ensureHasNoMVars
    if let some const := (← getEnv).find? proxyEquivName then
      unless ← isDefEq const.value! equiv' do
        throwError
          "Declaration {proxyEquivName} already exists and it is not the proxy equivalence."
      trace[Elab.Deriving.fintype] "proxy equivalence already exists"
    else
      addAndCompile <| Declaration.defnDecl
        { name := proxyEquivName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := (← inferType equiv')
          value := equiv' }
      setProtected proxyEquivName
    return { proxyName := proxyName
             proxyEquivName := proxyEquivName }

/--
The term elaborator `proxy_equiv% α` for a type `α` elaborates to an equivalence `β ≃ α`
for a "proxy type" `β` composed out of basic type constructors `Unit`, `PLift`, and `Sigma`,
`Empty`, and `Sum`.

This only works for inductive types `α` that are neither recursive nor have indices.
If `α` is an inductive type with name `I`, then as a side effect this elaborator defines
`I.proxyType` and `I.proxyTypeEquiv`.

The elaborator makes use of the expected type, so `(proxy_equiv% _ : _ ≃ α)` works.
-/
elab "proxy_equiv% " t:term : term <= expectedType => do
  let type ← Term.elabType t
  let equivType ← Term.elabType (← `(_ ≃ $(← Term.exprToSyntax type)))
  unless ← isDefEq expectedType equivType do
    throwError "Could not unify expected type{indentExpr expectedType}\nwith{indentExpr equivType}"
  let mut type ← instantiateMVars type
  if type.hasExprMVar then
    Term.synthesizeSyntheticMVars
    type ← instantiateMVars type
    if type.hasExprMVar then
      throwError "Provided type {type} has metavariables"
  type ← whnf type
  let .const declName _ := type.getAppFn
    | throwError "{type} is not a constant or constant application"
  let indVal ← getConstInfoInduct declName
  let data ← mkProxyEquiv indVal
  mkAppOptM data.proxyEquivName (type.getAppArgs.map .some)

/--
The term elaborator `derive_fintype% α` tries to synthesize a `Fintype α` instance
using all the assumptions in the local context; this can be useful, for example, if one
needs an extra `DecidableEq` instance. It only works when `α` is an inductive
type that `proxy_equiv% α` can handle. The elaborator makes use of the
expected type, so `(derive_fintype% _ : Fintype α)` works.

This uses `prox_equiv% α`, so as a side effect it defines `proxyType` and `proxyTypeEquiv` in
the namespace associated to the inductive type `α`.
-/
elab "derive_fintype% " t:term : term <= expectedType => do
  Term.elabTerm (← `(term| Fintype.ofEquiv _ (proxy_equiv% $t))) expectedType

/-
Creates a `Fintype` instance by adding additional `Fintype` and `Decidable` instance arguments
for every type and prop parameter of the type, then use the `derive_fintype%` elaborator.
-/
def mkFintype (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← Deriving.mkHeader `Fintype 0 indVal
    let binders' ← Deriving.mkInstImplicitBinders `Decidable indVal header.argNames
    let instCmd ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          Fintype $header.targetType := derive_fintype% _)
    return instCmd
  trace[Elab.Deriving.fintype] "instance command:\n{cmd}"
  elabCommand cmd
  return true

/-- Derive a `Fintype` instance for enum types. These come with a `toCtorIdx` function.

We generate a more optimized instance than the one produced by `mkFintype`.
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
      setProtected enumListName
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
      setProtected toCtorThmName
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
      setProtected enumListNodupName
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
