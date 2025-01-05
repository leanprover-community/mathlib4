/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.ProxyType
import Mathlib.Order.Basic
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order

/-! # A `LinearOrder` derive handler

Derives a `LinearOrder` for non-recursive inductive types without indices. Uses the
`Mathlib.ProxyType.ensureProxyEquiv` machinery to construct an equivalent "proxy type"
for the inductive type and pulls a `LinearOrder` across the equivalence.

In principle one should be able to define a `LinearOrder` for recursive types as well, but
the current implementation is able to reuse pre-existing constructions.

-/

namespace Mathlib.ProxyType
open Lean Meta Elab Term

def ProxyEquivConfig.lexDefault (indVal : InductiveVal) : ProxyEquivConfig where
  proxyName := indVal.name.mkStr "proxyLexType"
  proxyEquivName := indVal.name.mkStr "proxyLexTypeEquiv"
  mkCtorProxyType := defaultMkCtorProxyType (decorateSigma := fun e => mkAppM ``Lex #[e])
  mkProxyType := defaultMkProxyType (decorateSum := fun e => mkAppM ``Lex #[e])

syntax (name := proxy_lex_equiv) "proxy_lex_equiv% " term : term

@[term_elab proxy_lex_equiv]
def elab_proxy_lex_equiv : Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(proxy_lex_equiv% $t) => do
    let (type, indVal) ← elabProxyEquiv t expectedType?
    let config : ProxyEquivConfig := ProxyEquivConfig.lexDefault indVal
    ensureProxyEquiv config indVal
    mkAppOptM config.proxyEquivName (type.getAppArgs.map .some)
  | _ => throwUnsupportedSyntax

end Mathlib.ProxyType

namespace Mathlib.Deriving.LinearOrder
open Lean Elab Lean.Parser.Term
open Meta Command

macro "derive_linearOrder% " t:term : term =>
  `(term| LinearOrder.lift' (Equiv.symm (proxy_lex_equiv% $t)) (Equiv.injective _))

/-
Creates a `LinearOrder` instance by adding additional `LinearOrder` instance arguments
for every type parameter of the type, then use the `derive_linearOrder%` elaborator.
-/
def mkLinearOrder (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  if indVal.isRec then
    return false -- recursive types are not supported by this handler
  if 0 < indVal.numIndices then
    return false -- indices are not supported by this handler
  let cmd ← liftTermElabM do
    let header ← Deriving.mkHeader `LinearOrder 0 indVal
    let instCmd ← `(command|
      instance $header.binders:bracketedBinder* : LinearOrder $header.targetType :=
        derive_linearOrder% $header.targetType)
    return instCmd
  trace[Elab.Deriving.linearOrder] "instance command:\n{cmd}"
  elabCommand cmd
  return true

def mkLinearOrderInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported
  mkLinearOrder declNames[0]!

initialize
  registerDerivingHandler `LinearOrder mkLinearOrderInstanceHandler
  registerTraceClass `Elab.Deriving.linearOrder

end Mathlib.Deriving.LinearOrder
