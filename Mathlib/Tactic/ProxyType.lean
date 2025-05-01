/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.Core
import Mathlib.Logic.Equiv.Defs

/-!
# Generating "proxy types"

This module gives tools to create an equivalence between a given inductive type and a
"proxy type" constructed from `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum`.
It works for any non-recursive inductive type without indices.

The intended use case is for pulling typeclass instances across this equivalence. This
reduces the problem of generating typeclass instances to that of writing typeclass instances for
the above five types (and whichever additional types appear in the inductive type).

The main interface is the `proxy_equiv%` elaborator, where `proxy_equiv% t` gives an equivalence
between the proxy type for `t` and `t`. See the documentation for `proxy_equiv%` for an example.

For debugging information, do `set_option Elab.ProxyType true`.

It is possible to reconfigure the machinery to generate other types. See `ensureProxyEquiv`
and look at how it is used in `proxy_equiv%`.

## Implementation notes

For inductive types with `n` constructors, the `proxy_equiv%` elaborator creates a proxy
type of the form `C₁ ⊕ (C₂ ⊕ (⋯ ⊕ Cₙ))`. The equivalence then needs to handle `n - 1` levels
of `Sum` constructors, which is a source of quadratic complexity.

An alternative design could be to generate a `C : Fin n → Type*` function for the proxy types
for each constructor and then use `(i : Fin n) × ULift (C i)` for the total proxy type. However,
typeclass inference is not good at finding instances for such a type even if there are instances
for each `C i`. One seems to need to add, for example, an explicit `[∀ i, Fintype (C i)]`
instance given `∀ i, Fintype (C i)`.

-/

namespace Mathlib.ProxyType
open Lean Elab Lean.Parser.Term
open Meta Command

initialize registerTraceClass `Elab.ProxyType

/-- Configuration used by `mkProxyEquiv`. -/
structure ProxyEquivConfig where
  /-- Name to use for the declaration for a type that is `Equiv` to the given type. -/
  proxyName : Name
  /-- Name to use for the declaration for the equivalence `proxyType ≃ type`. -/
  proxyEquivName : Name
  /-- Returns a proxy type for a constructor and a pattern to use to match against it,
  given a list of fvars for the constructor arguments and pattern names to use for the arguments.
  The proxy type is expected to be a `Type*`. -/
  mkCtorProxyType : List (Expr × Name) → TermElabM (Expr × Term)
  /-- Given (constructor name, proxy constructor type, proxy constructor pattern) triples
  constructed using `mkCtorProxyType`, return (1) the total proxy type (a `Type*`),
  (2) patterns to use for each constructor, and (3) a proof to use to prove `left_inv` for
  `proxy_type ≃ type` (this proof starts with `intro x`). -/
  mkProxyType : Array (Name × Expr × Term) → TermElabM (Expr × Array Term × TSyntax `tactic)

/-- Returns a proxy type for a constructor and a pattern to use to match against it.

Input: a list of pairs associated to each argument of the constructor consisting
of (1) an fvar for this argument and (2) a name to use for this argument in patterns.

For example, given `#[(a, x), (b, y)]` with `x : Nat` and `y : Fin x`, then this function
returns `Sigma (fun x => Fin x)` and `⟨a, b⟩`.

Always returns a `Type*`. Uses `Unit`, `PLift`, and `Sigma`. Avoids using `PSigma` since
the `Fintype` instances for it go through `Sigma`s anyway.

The `decorateSigma` function is to wrap the `Sigma` a decorator such as `Lex`.
It should yield a definitionally equal type. -/
def defaultMkCtorProxyType (xs : List (Expr × Name))
    (decorateSigma : Expr → TermElabM Expr := pure) :
    TermElabM (Expr × Term) :=
  match xs with
  | [] => return (mkConst ``Unit, ← `(term| ()))
  | [(x, a)] => do
    let xty ← inferType x
    if ← Meta.isProp xty then
      return (← mkAppM ``PLift #[xty], ← `(term| ⟨$(mkIdent a)⟩))
    else
      return (xty, mkIdent a)
  | (x, a) :: xs => do
    let (xsty, patt) ← defaultMkCtorProxyType xs
    let xty ← inferType x
    if ← Meta.isProp xty then
      withLocalDeclD `x' (← mkAppM ``PLift #[xty]) fun x' => do
        let xsty' := xsty.replaceFVar x (← mkAppM ``PLift.down #[x'])
        let ty ← decorateSigma (← mkAppM ``Sigma #[← mkLambdaFVars #[x'] xsty'])
        return (ty, ← `(term| ⟨⟨$(mkIdent a)⟩, $patt⟩))
    else
      let ty ← decorateSigma (← mkAppM ``Sigma #[← mkLambdaFVars #[x] xsty])
      return (ty, ← `(term| ⟨$(mkIdent a), $patt⟩))

/-- Create a `Sum` of types, mildly optimized to not have a trailing `Empty`.

The `decorateSum` function is to wrap the `Sum` with a function such as `Lex`.
It should yield a definitionally equal type. -/
def defaultMkProxyType (ctors : Array (Name × Expr × Term))
    (decorateSum : Expr → TermElabM Expr := pure) :
    TermElabM (Expr × Array Term × TSyntax `tactic) := do
  let mut types := #[]
  let mut patts := #[]
  for h : i in [0:ctors.size] do
    let (_ctorName, ty, patt) := ctors[i]
    types := types.push ty
    patts := patts.push <| ← wrapSumAccess i ctors.size patt
  let (type, pf) ← mkCType types.toList
  return (type, patts, pf)
where
  /-- Construct the `Sum` expression, using `decorateSum` to adjust each `Sum`. -/
  mkCType (ctypes : List Expr) : TermElabM (Expr × TSyntax `tactic) :=
    match ctypes with
    | [] => return (mkConst ``Empty, ← `(tactic| cases x))
    | [x] => return (x, ← `(tactic| rfl))
    | x :: xs => do
      let (ty, pf) ← mkCType xs
      let pf ← `(tactic| cases x with | inl _ => rfl | inr x => $pf:tactic)
      return (← decorateSum (← mkAppM ``Sum #[x, ty]), pf)
  /-- Navigates into the sum type that we create in `mkCType` for the given constructor index. -/
  wrapSumAccess (cidx nctors : Nat) (spatt : Term) : TermElabM Term :=
    match cidx with
    | 0 =>
      if nctors = 1 then
        return spatt
      else
        `(term| Sum.inl $spatt)
    | cidx' + 1 => do
      let spatt ← wrapSumAccess cidx' (nctors - 1) spatt
      `(term| Sum.inr $spatt)

/-- Default configuration. Defines `proxyType` and `proxyTypeEquiv` in the namespace
of the inductive type. Uses `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum`. -/
def ProxyEquivConfig.default (indVal : InductiveVal) : ProxyEquivConfig where
  proxyName := indVal.name.mkStr "proxyType"
  proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  mkCtorProxyType := defaultMkCtorProxyType
  mkProxyType := defaultMkProxyType

/--
Generates a proxy type for the inductive type and an equivalence from the proxy type to the type.

If the declarations already exist, there is a check that they are correct.
-/
def ensureProxyEquiv (config : ProxyEquivConfig) (indVal : InductiveVal) : TermElabM Unit := do
  if indVal.isRec then
    throwError
      "proxy equivalence: recursive inductive types are not supported (and are usually infinite)"
  if 0 < indVal.numIndices then
    throwError "proxy equivalence: inductive indices are not supported"

  let levels := indVal.levelParams.map Level.param
  forallBoundedTelescope indVal.type indVal.numParams fun params _sort => do
    let mut cdata := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
      cdata := cdata.push <| ←
        forallBoundedTelescope ctorType ctorInfo.numFields fun xs _itype => do
          let names ← xs.mapM (fun _ => mkFreshUserName `a)
          let (ty, ppatt) ← config.mkCtorProxyType (xs.zip names).toList
          let places := .replicate ctorInfo.numParams (← `(term| _))
          let argNames := names.map mkIdent
          let cpatt ← `(term| @$(mkIdent ctorName) $places* $argNames*)
          return (ctorName, ty, ppatt, cpatt)
    let (ctype, ppatts, pf) ← config.mkProxyType <|
      cdata.map (fun (ctorName, ty, ppatt, _) => (ctorName, ty, ppatt))
    let mut toFunAlts := #[]
    let mut invFunAlts := #[]
    for ppatt in ppatts, (_, _, _, cpatt) in cdata do
      toFunAlts := toFunAlts.push <| ← `(matchAltExpr| | $ppatt => $cpatt)
      invFunAlts := invFunAlts.push <| ← `(matchAltExpr| | $cpatt => $ppatt)

    -- Create the proxy type definition
    trace[Elab.ProxyType] "proxy type: {ctype}"
    let ctype' ← mkLambdaFVars params ctype
    if let some const := (← getEnv).find? config.proxyName then
      unless ← isDefEq const.value! ctype' do
        throwError "Declaration {config.proxyName} already exists and it is not the proxy type."
      trace[Elab.ProxyType] "proxy type already exists"
    else
      addAndCompile <| Declaration.defnDecl
        { name := config.proxyName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType ctype'
          value := ctype' }
      -- Set to be reducible so that typeclass inference can see it's a Fintype
      setReducibleAttribute config.proxyName
      setProtected config.proxyName
      -- Add a docstring
      addDocStringCore config.proxyName s!"A \"proxy type\" equivalent to `{indVal.name}` that is \
        constructed from `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum`. \
        See `{config.proxyEquivName}` for the equivalence. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyName}"

    -- Create the `Equiv`
    let equivType ← mkAppM ``Equiv #[ctype, mkAppN (mkConst indVal.name levels) params]
    if let some const := (← getEnv).find? config.proxyEquivName then
      unless ← isDefEq const.type (← mkForallFVars params equivType) do
        throwError "Declaration {config.proxyEquivName} already exists and has the wrong type."
      trace[Elab.ProxyType] "proxy equivalence already exists"
    else
      trace[Elab.ProxyType] "constructing proxy equivalence"
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
      let equiv ← Term.elabTerm equivBody equivType
      Term.synthesizeSyntheticMVarsNoPostponing
      trace[Elab.ProxyType] "elaborated equivalence{indentExpr equiv}"
      let equiv' ← mkLambdaFVars params (← instantiateMVars equiv)
      addAndCompile <| Declaration.defnDecl
        { name := config.proxyEquivName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType equiv'
          value := equiv' }
      setProtected config.proxyEquivName
      addDocStringCore config.proxyEquivName s!"An equivalence between the \"proxy type\" \
        `{config.proxyName}` and `{indVal.name}`. The proxy type is a reducible definition \
        that represents the inductive type using `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum` \
        (and whatever other inductive types appear within the inductive type), and the \
        intended use is to define typeclass instances uses pre-existing instances on these. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyEquivName}"

/-- Helper function for `proxy_equiv% type : expectedType` elaborators.

Elaborate `type` and get its `InductiveVal`. Uses the `expectedType`, where the
expected type should be of the form `_ ≃ type`. -/
def elabProxyEquiv (type : Term) (expectedType? : Option Expr) :
    TermElabM (Expr × InductiveVal) := do
  let type ← Term.elabType type
  if let some expectedType := expectedType? then
    let equivType ← Term.elabType (← `(_ ≃ $(← Term.exprToSyntax type)))
    unless ← isDefEq expectedType equivType do
      throwError
        "Could not unify expected type{indentExpr expectedType}\nwith{indentExpr equivType}"
  let type ← Term.tryPostponeIfHasMVars type "In proxy_equiv% elaborator"
  let type ← whnf type
  let .const declName _ := type.getAppFn
    | throwError "{type} is not a constant or constant application"
  return (type, ← getConstInfoInduct declName)

/--
The term elaborator `proxy_equiv% α` for a type `α` elaborates to an equivalence `β ≃ α`
for a "proxy type" `β` composed out of basic type constructors `Unit`, `PLift`, `Sigma`,
`Empty`, and `Sum`.

This only works for inductive types `α` that are neither recursive nor have indices.
If `α` is an inductive type with name `I`, then as a side effect this elaborator defines
`I.proxyType` and `I.proxyTypeEquiv`.

The elaborator makes use of the expected type, so `(proxy_equiv% _ : _ ≃ α)` works.

For example, given this inductive type
```
inductive foo (n : Nat) (α : Type)
  | a
  | b : Bool → foo n α
  | c (x : Fin n) : Fin x → foo n α
  | d : Bool → α → foo n α
```
the proxy type it generates is `Unit ⊕ Bool ⊕ (x : Fin n) × Fin x ⊕ (_ : Bool) × α` and
in particular we have that
```
proxy_equiv% (foo n α) : Unit ⊕ Bool ⊕ (x : Fin n) × Fin x ⊕ (_ : Bool) × α ≃ foo n α
```
-/
syntax (name := proxy_equiv) "proxy_equiv% " term : term

/-- Elaborator for `proxy_equiv%`. -/
@[term_elab proxy_equiv]
def elab_proxy_equiv : Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(proxy_equiv% $t) => do
    let (type, indVal) ← elabProxyEquiv t expectedType?
    let config : ProxyEquivConfig := ProxyEquivConfig.default indVal
    ensureProxyEquiv config indVal
    mkAppOptM config.proxyEquivName (type.getAppArgs.map .some)
  | _ => throwUnsupportedSyntax

end Mathlib.ProxyType
