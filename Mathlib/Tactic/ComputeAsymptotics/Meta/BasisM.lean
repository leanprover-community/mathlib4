/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Meta.MS

/-!
# TODO
-/

public meta section

open Filter Topology Asymptotics Stream'.Seq

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

/-- State of the `BasisM` monad. -/
structure BasisState where
  /-- Current basis. -/
  basis : Q(Basis)
  /-- Log-basis. -/
  logBasis : Q(LogBasis $basis)
  /-- Proof of well-formedness of the basis. -/
  h_basis : Q(WellFormedBasis $basis)
  /-- Proof of well-formedness of the log-basis. -/
  h_logBasis : Q(LogBasis.WellFormed $logBasis)
  /-- Index of the `id` function in the basis. -/
  n_id : Q(Fin (List.length $basis))

/-- Monad currying the basis. -/
abbrev BasisM := StateT BasisState TacticM

/-- Returns `BasisExtension` creating `basis'` from `basis`. -/
partial def getBasisExtension (basis basis' : Q(Basis)) : MetaM (Q(BasisExtension $basis)) := do
  match basis, basis' with
  | ~q(List.nil), ~q(List.nil) => return q(BasisExtension.nil)
  | ~q(List.cons $basis_hd $basis_tl), ~q(List.nil) => panic! "getBasisExtension: short basis'"
  | ~q(List.nil), ~q(List.cons $basis_hd' $basis_tl') =>
    let ex ← getBasisExtension q([]) basis_tl'
    return q(BasisExtension.insert $basis_hd' $ex)
  | ~q(List.cons $basis_hd $basis_tl), ~q(List.cons $basis_hd' $basis_tl') =>
    if basis_hd == basis_hd' then
      -- they must be just equal. Maybe need to use isDefEq with reducible transparency?
      let ex ← getBasisExtension basis_tl basis_tl'
      return q(BasisExtension.keep $basis_hd $ex)
    else
      let ex ← getBasisExtension basis basis_tl'
      return q(BasisExtension.insert $basis_hd' $ex)
  | _ => panic! "unexpected basis or basis' in getBasisExtension"

/-- Given `ms` immerses it into the current basis. -/
def updateBasis (ms : MS) : BasisM MS := do
  let ex ← getBasisExtension ms.basis (← get).basis
  let ms' ← ms.updateBasis ex (← get).logBasis (← get).h_basis (← get).h_logBasis
  return ms'

/-- MS approximating `c : ℝ` in the current basis. -/
def BasisM.const (c : Q(ℝ)) : BasisM MS := do
  return MS.const (← get).basis (← get).logBasis q($c) (← get).h_basis (← get).h_logBasis

/-- MS approximating `basis[n]` in the current basis. -/
def BasisM.monomial {k : Q(ℕ)} (n : Q(Fin $k)) : BasisM MS := do
  return MS.monomial (← get).basis (← get).logBasis n (← get).h_basis
    (← get).h_logBasis

/-- MS approximating `basis[n] ^ r` in the current basis. -/
def BasisM.monomialRpow {k : Q(ℕ)} (n : Q(Fin $k)) (r : Q(ℝ)) : BasisM MS := do
  return MS.monomialRpow (← get).basis (← get).logBasis n r (← get).h_basis
    (← get).h_logBasis

end ComputeAsymptotics
