/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries
import Mathlib.Tactic.Tendsto.Meta.LeadingTerm

/-!
# TODO
-/

open Lean Elab Meta Qq TendstoTactic

namespace TendstoTactic

structure MS where
  basis : Q(Basis)
  logBasis : Q(LogBasis $basis)
  val : Q(PreMS $basis)
  f : Q(ℝ → ℝ)
  h_wo : Q(PreMS.WellOrdered $val)
  h_approx : Q(PreMS.Approximates $val $f)
  h_basis : Q(WellFormedBasis $basis)
  h_logBasis : Q(LogBasis.WellFormed $logBasis)

instance : Inhabited MS where
  default := {
    basis := q([])
    val := q(0)
    f := q(fun _ ↦ 0)
    h_wo := q(PreMS.const_WellOrdered)
    h_approx := q(PreMS.const_Approximates WellFormedBasis.nil)
    h_basis := q(WellFormedBasis.nil)
    logBasis := q(LogBasis.nil)
    h_logBasis := q(LogBasis.nil_WellFormed)
  }

namespace MS

def const (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (c : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.const $basis $c)
  f := q(fun _ ↦ $c)
  h_wo := q(PreMS.const_WellOrdered)
  h_approx := q(PreMS.const_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

def monomial_rpow (basis : Q(Basis)) (logBasis : Q(LogBasis $basis))
    (n : Q(Fin (List.length $basis))) (r : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.monomial_rpow $basis $n $r)
  f := q(fun x ↦ (List.get $basis $n x)^$r)
  h_wo := q(PreMS.monomial_rpow_WellOrdered)
  h_approx := q(PreMS.monomial_rpow_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

def monomial (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (n : Q(Fin (List.length $basis)))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(PreMS.monomial $basis $n)
  f := q(List.get $basis $n)
  h_wo := q(PreMS.monomial_WellOrdered)
  h_approx := q(PreMS.monomial_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

def mulConst (x : MS) (c : Q(ℝ)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.mulConst $x.val $c)
  f := q($c • $x.f)
  h_wo := q(PreMS.mulConst_WellOrdered $x.h_wo)
  h_approx := q(PreMS.mulConst_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def neg (x : MS) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.neg $x.val)
  f := q(-$x.f)
  h_wo := q(PreMS.neg_WellOrdered $x.h_wo)
  h_approx := q(PreMS.neg_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

set_option linter.unusedVariables false in
def add (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.add $x.val $y.val)
  f := q($x.f + $y.f)
  h_wo := q(PreMS.add_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.add_Approximates $x.h_approx $y.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

set_option linter.unusedVariables false in
def sub (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.add $x.val (PreMS.neg $y.val))
  f := q($x.f - $y.f)
  h_wo := q(PreMS.sub_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.sub_Approximates $x.h_approx $y.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

set_option linter.unusedVariables false in
def mul (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.mul $x.val $y.val)
  f := q($x.f * $y.f)
  h_wo := q(PreMS.mul_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.mul_Approximates $x.h_basis $x.h_approx $y.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def inv (x : MS) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.inv $x.val)
  f := q($x.f⁻¹)
  h_wo := q(PreMS.inv_WellOrdered $x.h_wo)
  h_approx := q(PreMS.inv_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

set_option linter.unusedVariables false in
def div (x y : MS) (h_trimmed : Q(PreMS.Trimmed $y.val)) (h_basis_eq : $x.basis =Q $y.basis) :
    MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.mul $x.val (PreMS.inv $y.val))
  f := q($x.f / $y.f)
  h_wo := q(PreMS.div_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.div_Approximates $x.h_basis $y.h_wo $h_trimmed $x.h_approx $y.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def npow (x : MS) (a : Q(ℕ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.zpow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def zpow (x : MS) (a : Q(ℤ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.zpow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def rpow (x : MS) (a : Q(ℝ)) (h_trimmed : Q(PreMS.Trimmed $x.val))
    (h_pos : Q(0 < (PreMS.leadingTerm $x.val).coef)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.pow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed $h_pos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

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
    f := ms.f
    h_wo := q(PreMS.updateBasis_WellOrdered $ms.h_wo)
    h_approx := q(PreMS.updateBasis_Approximates $h_basis $ms.h_wo $ms.h_approx)
    h_basis := h_basis
    h_logBasis := h_logBasis
  }

def insertLastLog (ms : MS) : MetaM MS := do
  let ~q(List.cons $basis_hd $basis_tl) := ms.basis | panic! "insertLastLog: unexpected basis"
  let .some last ← getLast (α := q(ℝ → ℝ)) ms.basis | panic! "insertLastLog: unexpected basis"
  haveI : List.getLast ($basis_hd :: $basis_tl) (List.cons_ne_nil _ _) =Q $last := ⟨⟩
  let basis := ← reduceBasis q($ms.basis ++ [Real.log ∘ $last])
  haveI : $basis =Q $ms.basis ++ [Real.log ∘ $last] := ⟨⟩
  let logBasis := ← reduceLogBasis q(LogBasis.insertLastLog (basis_hd := $basis_hd)
    (basis_tl := $basis_tl) $ms.logBasis)
  have : $logBasis =Q LogBasis.insertLastLog (basis_hd := $basis_hd) (basis_tl := $basis_tl)
    $ms.logBasis := ⟨⟩
  let h_basis : Q(WellFormedBasis $basis) := q(insertLastLog_WellFormedBasis $ms.h_basis)
  let ms' : MS := {
    basis := basis
    val := q(PreMS.extendBasisEnd (Real.log ∘ $last) $ms.val)
    f := ms.f
    h_wo := q(PreMS.extendBasisEnd_WellOrdered $ms.h_wo)
    h_approx := q(PreMS.extendBasisEnd_Approximates $h_basis $ms.h_approx)
    h_basis := h_basis
    logBasis := logBasis
    h_logBasis := q(LogBasis.insertLastLog_WellFormed $ms.h_basis $ms.h_logBasis)
  }
  return ms'

def log (x : MS) (h_trimmed : Q(PreMS.Trimmed $x.val))
    (h_pos : Q(0 < (PreMS.leadingTerm $x.val).coef))
    (h_last : Q(∀ a, (PreMS.leadingTerm $x.val).exps.getLast? = .some a → a = 0)) : MS where
  basis := q($x.basis)
  val := q(PreMS.log $x.logBasis $x.val)
  f := q(Real.log ∘ $x.f)
  h_wo := q(PreMS.log_WellOrdered $x.h_logBasis $h_last $x.h_wo)
  h_approx := q(PreMS.log_Approximates $x.h_basis $x.h_logBasis $x.h_wo $x.h_approx
    $h_trimmed $h_pos $h_last)
  h_basis := x.h_basis
  logBasis := q($x.logBasis)
  h_logBasis := x.h_logBasis

def exp (x : MS) (h_nonpos : Q(¬ Term.FirstIsPos (PreMS.leadingTerm $x.val).exps)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.exp $x.val)
  f := q(Real.exp ∘ $x.f)
  h_wo := q(PreMS.exp_WellOrdered $x.h_wo $h_nonpos)
  h_approx := q(PreMS.exp_Approximates $x.h_basis $x.h_wo $x.h_approx $h_nonpos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def cos (x : MS) (h_nonpos : Q(¬ Term.FirstIsPos (PreMS.leadingTerm $x.val).exps)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.cos $x.val)
  f := q(Real.cos ∘ $x.f)
  h_wo := q(PreMS.cos_WellOrdered $x.h_wo $h_nonpos)
  h_approx := q(PreMS.cos_Approximates $x.h_basis $x.h_wo $x.h_approx $h_nonpos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

def sin (x : MS) (h_nonpos : Q(¬ Term.FirstIsPos (PreMS.leadingTerm $x.val).exps)): MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(PreMS.sin $x.val)
  f := q(Real.sin ∘ $x.f)
  h_wo := q(PreMS.sin_WellOrdered $x.h_wo $h_nonpos)
  h_approx := q(PreMS.sin_Approximates $x.h_basis $x.h_wo $x.h_approx $h_nonpos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

end MS

end TendstoTactic
