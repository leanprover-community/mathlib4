/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Misc

/-!
# Multiseries on meta level
-/

public meta section

open Lean Elab Meta Qq ComputeAsymptotics

namespace ComputeAsymptotics

/-- Multiseries on meta level. It contains
* the basis with the proof of well-formedness
* the log-basis with the proof of well-formedness
* the `PreMS` value with the proof of well-ordering
* the function `f` with the proof that the multiseries approximates it
-/
structure MS where
  /-- Basis of the multiseries. -/
  basis : Q(Basis)
  /-- Log-basis of the multiseries. -/
  logBasis : Q(LogBasis $basis)
  /-- `PreMS` value of the multiseries. -/
  val : Q(PreMS $basis)
  /-- Proof of well-ordering of the multiseries. -/
  h_wo : Q(PreMS.WellOrdered $val)
  /-- Proof of approximation of the multiseries. -/
  h_approx : Q(PreMS.Approximates $val)
  /-- Proof of well-formedness of the basis. -/
  h_basis : Q(WellFormedBasis $basis)
  /-- Proof of well-formedness of the log-basis. -/
  h_logBasis : Q(LogBasis.WellFormed $logBasis)
deriving Inhabited

namespace MS

/-- Multiseries representing a constant function. -/
def const (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (c : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.const $basis $c)
  -- f := q(fun _ ↦ $c)
  h_wo := q(PreMS.const_WellOrdered)
  h_approx := q(PreMS.const_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Multiseries representing `basis[n] ^ r`. -/
def monomialRpow (basis : Q(Basis)) (logBasis : Q(LogBasis $basis))
    (n : Q(Fin (List.length $basis))) (r : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.monomialRpow $basis $n $r)
  -- f := q(fun x ↦ (List.get $basis $n x)^$r)
  h_wo := q(PreMS.monomialRpow_WellOrdered)
  h_approx := q(PreMS.monomialRpow_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Multiseries representing `basis[n]`. -/
def monomial (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (n : Q(Fin (List.length $basis)))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.monomial $basis $n)
  -- f := q(List.get $basis $n)
  h_wo := q(PreMS.monomial_WellOrdered)
  h_approx := q(PreMS.monomial_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `c • f`. -/
def mulConst (x : MS) (c : Q(ℝ)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.mulConst $c $x.val)
  -- f := q($c • $x.f)
  h_wo := q(PreMS.mulConst_WellOrdered $x.h_wo)
  h_approx := q(PreMS.mulConst_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `-f`. -/
def neg (x : MS) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.neg $x.val)
  -- f := q(-$x.f)
  h_wo := q(PreMS.neg_WellOrdered $x.h_wo)
  h_approx := q(PreMS.neg_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f + g`. -/
def add (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(PreMS.add $x.val $y.val)
    -- f := q($x.f + $y.f)
    h_wo := q(PreMS.add_WellOrdered $x.h_wo $y.h_wo)
    h_approx := q(PreMS.add_Approximates $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f - g`. -/
def sub (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(PreMS.add $x.val (PreMS.neg $y.val))
    -- f := q($x.f - $y.f)
    h_wo := q(PreMS.sub_WellOrdered $x.h_wo $y.h_wo)
    h_approx := q(PreMS.sub_Approximates $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f * g`. -/
def mul (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(PreMS.mul $x.val $y.val)
    -- f := q($x.f * $y.f)
    h_wo := q(PreMS.mul_WellOrdered $x.h_wo $y.h_wo)
    h_approx := q(PreMS.mul_Approximates $x.h_basis $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given a multiseries representing `f`, returns the multiseries representing `f⁻¹`. -/
def inv (x : MS) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.inv $x.val)
  -- f := q($x.f⁻¹)
  h_wo := q(PreMS.inv_WellOrdered $x.h_wo)
  h_approx := q(PreMS.inv_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f / g`. -/
def div (x y : MS) (h_trimmed : Q(PreMS.Trimmed $y.val)) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(PreMS.mul $x.val (PreMS.inv $y.val))
    -- f := q($x.f / $y.f)
    h_wo := q(PreMS.div_WellOrdered $x.h_wo $y.h_wo)
    h_approx := q(PreMS.div_Approximates $x.h_basis $y.h_wo $h_trimmed $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given a multiseries representing `f` and constant `a : ℕ`,
returns the multiseries representing `f ^ a`. -/
def npow (x : MS) (a : Q(ℕ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.npow $x.val $a)
  -- f := q($x.f ^ $a)
  h_wo := q(PreMS.npow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.npow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f` and constant `a : ℤ`,
returns the multiseries representing `f ^ a`. -/
def zpow (x : MS) (a : Q(ℤ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.zpow $x.val $a)
  -- f := q($x.f ^ $a)
  h_wo := q(PreMS.zpow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.zpow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f` and constant `a : ℝ`,
returns the multiseries representing `f ^ a`. -/
def rpow (x : MS) (a : Q(ℝ)) (h_trimmed : Q(PreMS.Trimmed $x.val))
    (h_pos : Q(0 < (PreMS.leadingTerm $x.val).coef)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.pow $x.val $a)
  -- f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.pow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed $h_pos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries `ms` and a basis extension `ex`, returns the multiseries representing
the same function on the new basis. -/
def updateBasis (ms : MS) (ex : Q(BasisExtension $ms.basis))
    (logBasis : Q(LogBasis (BasisExtension.getBasis $ex)))
    (h_basis : Q(WellFormedBasis (BasisExtension.getBasis $ex)))
    (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MetaM MS := do
  let basis ← reduceBasis q(BasisExtension.getBasis $ex)
  haveI : $basis =Q BasisExtension.getBasis $ex := ⟨⟩
  return {
    basis := basis
    logBasis := logBasis
    val := q(PreMS.updateBasis $ex $ms.val)
    -- f := ms.f
    h_wo := q(PreMS.updateBasis_WellOrdered $ms.h_wo)
    h_approx := q(PreMS.updateBasis_Approximates $h_basis $ms.h_approx)
    h_basis := h_basis
    h_logBasis := h_logBasis
  }

/-- Given a multiseries `ms`, returns the multiseries representing the same function on the basis
extended by the last `log ∘ basis.getLast` element. -/
def insertLastLog (ms : MS) : MetaM MS := do
  let ~q(List.cons $basis_hd $basis_tl) := ms.basis | panic! "insertLastLog: unexpected basis"
  let .some last ← getLast (α := q(ℝ → ℝ)) ms.basis | panic! "insertLastLog: unexpected basis"
  haveI : List.getLast ($basis_hd :: $basis_tl) (List.cons_ne_nil _ _) =Q $last := ⟨⟩
  let basis := ← reduceBasis q($ms.basis ++ [Real.log ∘ $last])
  haveI : $basis =Q $ms.basis ++ [Real.log ∘ $last] := ⟨⟩
  let logBasis := ← reduceLogBasis q(LogBasis.insertLastLog (basis_hd := $basis_hd)
    (basis_tl := $basis_tl) $ms.logBasis)
  haveI : $logBasis =Q LogBasis.insertLastLog (basis_hd := $basis_hd) (basis_tl := $basis_tl)
    $ms.logBasis := ⟨⟩
  let h_basis : Q(WellFormedBasis $basis) := q(insertLastLog_WellFormedBasis $ms.h_basis)
  let ms' : MS := {
    basis := basis
    val := q(PreMS.extendBasisEnd (Real.log ∘ $last) $ms.val)
    -- f := ms.f
    h_wo := q(PreMS.extendBasisEnd_WellOrdered $ms.h_wo)
    h_approx := q(PreMS.extendBasisEnd_Approximates $h_basis $ms.h_approx)
    h_basis := h_basis
    logBasis := logBasis
    h_logBasis := q(LogBasis.insertLastLog_WellFormed $ms.h_basis $ms.h_logBasis)
  }
  return ms'

/-- Given a multiseries representing `f`, returns the multiseries representing `log ∘ f`. -/
def log (x : MS) (h_trimmed : Q(PreMS.Trimmed $x.val))
    (h_pos : Q(0 < (PreMS.leadingTerm $x.val).coef))
    (h_last : Q(∀ a, (PreMS.leadingTerm $x.val).exps.getLast? = .some a → a = 0)) : MS where
  basis := q($x.basis)
  val := q(PreMS.log $x.logBasis $x.val)
  -- f := q(Real.log ∘ $x.f)
  h_wo := q(PreMS.log_WellOrdered $x.h_logBasis $h_last $x.h_wo)
  h_approx := q(PreMS.log_Approximates $x.h_basis $x.h_logBasis $x.h_wo $x.h_approx
    $h_trimmed $h_pos $h_last)
  h_basis := x.h_basis
  logBasis := q($x.logBasis)
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `exp ∘ f`. -/
def exp (x : MS) (h_nonpos : Q(¬ Term.FirstIsPos (PreMS.leadingTerm $x.val).exps)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.exp $x.val)
  -- f := q(Real.exp ∘ $x.f)
  h_wo := q(PreMS.exp_WellOrdered $x.h_wo $h_nonpos)
  h_approx := q(PreMS.exp_Approximates $x.h_basis $x.h_wo $x.h_approx $h_nonpos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def replaceFun (ms : MS) (f : Q(ℝ → ℝ)) (h : Q(($ms.val).toFun =ᶠ[Filter.atTop] $f)) : MetaM MS := do
  let ~q($basis_hd :: $basis_tl) := ms.basis | panic! "replaceFun: unexpected basis"
  return {ms with
    val := q(PreMS.replaceFun $ms.val $f)
    h_wo := q(PreMS.replaceFun_WellOrdered $ms.h_wo)
    h_approx := q(PreMS.replaceFun_Approximates $h $ms.h_approx)
  }

end MS

end ComputeAsymptotics
