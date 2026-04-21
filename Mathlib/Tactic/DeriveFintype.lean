/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.OfMap  -- shake: keep (metaprogram output dependency)
public import Mathlib.Tactic.ProxyType
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual

/-!
# The `Fintype` derive handler

This file defines a derive handler to automatically generate `Fintype` instances
for structures and inductive types.

The following is a prototypical example of what this can handle:
```
inductive MyOption (α : Type*)
  | none
  | some (x : α)
  deriving Fintype
```

This deriving handler does not attempt to process inductive types that are either
recursive or that have indices.

To get debugging information, do `set_option trace.Elab.Deriving.fintype true`
and `set_option Elab.ProxyType true`.

There is a term elaborator `derive_fintype%` implementing the derivation of `Fintype` instances.
This can be useful in cases when there are necessary additional assumptions (like `DecidableEq`).
This is implemented using `Fintype.ofEquiv` and `proxy_equiv%`, which is a term elaborator
that creates an equivalence from a "proxy type" composed of basic type constructors. If Lean
can synthesize a `Fintype` instance for the proxy type, then `derive_fintype%` succeeds.

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
contributes just linear time with respect to the cardinality of the type since the instances
involved compute the underlying `List` for the `Finset` as `l₁ ++ (l₂ ++ (⋯ ++ lₙ))` with
right associativity.

Note that an alternative design could be that instead of using `Sum` we could create a
function `C : Fin n → Type*` with `C i = ULift Cᵢ` and then use `(i : Fin n) × C i` for
the proxy type, which would save us from the nested `Sum` constructors.

This implementation takes some inspiration from the one by Mario Carneiro for Mathlib 3.
A difference is that the Mathlib 3 version does not explicitly construct the total proxy type,
and instead it opts to construct the underlying `Finset` as a disjoint union of the `Finset.univ`
for each individual constructor's proxy type.
-/
set_option backward.defeqAttrib.useBackward true

public meta section

namespace Mathlib.Deriving.Fintype
open Lean Elab Lean.Parser.Term
open Meta Command

/--
The term elaborator `derive_fintype% α` tries to synthesize a `Fintype α` instance
using all the assumptions in the local context; this can be useful, for example, if one
needs an extra `DecidableEq` instance. It works only if `α` is an inductive
type that `proxy_equiv% α` can handle. The elaborator makes use of the
expected type, so `(derive_fintype% _ : Fintype α)` works.

This uses `proxy_equiv% α`, so as a side effect it defines `proxyType` and `proxyTypeEquiv` in
the namespace associated to the inductive type `α`.
-/
macro "derive_fintype% " t:term : term => `(term| Fintype.ofEquiv _ (proxy_equiv% $t))

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

/-- Derive a `Fintype` instance for enum types. These come with a `ctorIdx` function.

We generate a more optimized instance than the one produced by `mkFintype`.
The strategy is to (1) create a list `enumList` of all the constructors, (2) prove that this
is in `ctorIdx` order, (3) show that `ctorIdx` maps `enumList` to `List.range numCtors` to show
the list has no duplicates, and (4) give the `Fintype` instance, using 2 for completeness.

The proofs are all linear complexity, and the main computation is that
`enumList.map ctorIdx = List.range numCtors`, which is true by `refl`. -/
def mkFintypeEnum (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let levels := indVal.levelParams.map Level.param
  let ctorIdxName := declName.mkStr "ctorIdx"
  let enumListName := declName.mkStr "enumList"
  let ctorThmName := declName.mkStr "enumList_getElem?_ctorIdx_eq"
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
      addDocStringCore enumListName s!"A list enumerating every element of the type, \
        which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)"
    do -- Prove that this list is in `ctorIdx` order
      trace[Elab.Deriving.fintype] "proving {ctorThmName}"
      let goalStx ← `(term| ∀ (x : $(← Term.exprToSyntax <| mkConst declName levels)),
        $(mkIdent enumListName)[$(mkIdent ctorIdxName) x]? = some x)
      let goal ← Term.elabTerm goalStx (mkSort .zero)
      let pf ← Term.elabTerm (← `(term| by intro x; cases x <;> rfl)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      addAndCompile <| Declaration.thmDecl
        { name := ctorThmName
          levelParams := indVal.levelParams
          type := ← instantiateMVars goal
          value := ← instantiateMVars pf }
      setProtected ctorThmName
    do -- Use this theorem to prove `enumList` has no duplicates
      trace[Elab.Deriving.fintype] "proving {enumListNodupName}"
      let enum ← Term.exprToSyntax <| mkConst enumListName levels
      let goal ← Term.elabTerm (← `(term| List.Nodup $enum)) (mkSort .zero)
      let n : TSyntax `term := quote indVal.numCtors
      let pf ← Term.elabTerm (← `(term| by
                  apply List.Nodup.of_map $(mkIdent ctorIdxName)
                  have h : List.map $(mkIdent ctorIdxName) $(mkIdent enumListName)
                            = List.range $n := rfl
                  exact h ▸ List.nodup_range)) goal
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
        rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_getElem?]
        exact ⟨$(mkIdent ctorIdxName) x, $(mkIdent ctorThmName) x⟩)
  trace[Elab.Deriving.fintype] "instance command:\n{cmd}"
  elabCommand cmd

def mkFintypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size ≠ 1 then
    return false -- mutually inductive types are not supported
  else
    let declName := declNames[0]
    if ← isEnumType declName then
      mkFintypeEnum declName
      return true
    else
      mkFintype declName

initialize
  registerDerivingHandler ``Fintype mkFintypeInstanceHandler
  registerTraceClass `Elab.Deriving.fintype

end Mathlib.Deriving.Fintype
