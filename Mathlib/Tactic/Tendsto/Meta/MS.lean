/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries

/-!
# TODO
-/

open Lean Qq TendstoTactic

namespace TendstoTactic

structure MS where
  basis : Q(Basis)
  val : Q(PreMS $basis)
  f : Q(ℝ → ℝ)
  h_wo : Q(PreMS.WellOrdered $val)
  h_approx : Q(PreMS.Approximates $val $f)
  h_basis : Q(WellFormedBasis $basis)

namespace MS

def const (basis : Q(Basis)) (c : Q(ℝ)) (h_basis : Q(WellFormedBasis $basis))  : MS where
  basis := basis
  val := q(PreMS.const $basis $c)
  f := q(fun _ ↦ $c)
  h_wo := q(PreMS.const_WellOrdered)
  h_approx := q(PreMS.const_Approximates $h_basis)
  h_basis := h_basis

def monomial (basis : Q(Basis)) (n : ℕ) (h : Q($n < List.length $basis))
    (h_basis : Q(WellFormedBasis $basis)) : MS where
  basis := basis
  val := q(PreMS.monomial $basis $n)
  f := q(List.get $basis ⟨$n, $h⟩)
  h_wo := q(PreMS.monomial_WellOrdered)
  h_approx := q(PreMS.monomial_Approximates $h $h_basis)
  h_basis := h_basis

def neg (x : MS) : MS where
  basis := x.basis
  val := q(PreMS.neg $x.val)
  f := q(-$x.f)
  h_wo := q(PreMS.neg_WellOrdered $x.h_wo)
  h_approx := q(PreMS.neg_Approximates $x.h_approx)
  h_basis := x.h_basis

set_option linter.unusedVariables false in
def add (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  val := q(PreMS.add $x.val $y.val)
  f := q($x.f + $y.f)
  h_wo := q(PreMS.add_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.add_Approximates $x.h_approx $y.h_approx)
  h_basis := x.h_basis

set_option linter.unusedVariables false in
def sub (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  val := q(PreMS.add $x.val (PreMS.neg $y.val))
  f := q($x.f - $y.f)
  h_wo := q(PreMS.sub_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.sub_Approximates $x.h_approx $y.h_approx)
  h_basis := x.h_basis

set_option linter.unusedVariables false in
def mul (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  val := q(PreMS.mul $x.val $y.val)
  f := q($x.f * $y.f)
  h_wo := q(PreMS.mul_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.mul_Approximates $x.h_basis $x.h_approx $y.h_approx)
  h_basis := x.h_basis

def inv (x : MS) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  val := q(PreMS.inv $x.val)
  f := q($x.f⁻¹)
  h_wo := q(PreMS.inv_WellOrdered $x.h_wo)
  h_approx := q(PreMS.inv_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis

set_option linter.unusedVariables false in
def div (x y : MS) (h_trimmed : Q(PreMS.Trimmed $y.val)) (h_basis_eq : $x.basis =Q $y.basis) :
    MS where
  basis := x.basis
  val := q(PreMS.mul $x.val (PreMS.inv $y.val))
  f := q($x.f / $y.f)
  h_wo := q(PreMS.div_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.div_Approximates $x.h_basis $y.h_wo $h_trimmed $x.h_approx $y.h_approx)
  h_basis := x.h_basis

def npow (x : MS) (a : Q(ℕ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.zpow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis

def zpow (x : MS) (a : Q(ℤ)) (h_trimmed : Q(PreMS.Trimmed $x.val)) : MS where
  basis := x.basis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.zpow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed)
  h_basis := x.h_basis

def rpow (x : MS) (a : Q(ℝ)) (h_trimmed : Q(PreMS.Trimmed $x.val))
    (h_pos : Q(0 < (PreMS.leadingTerm $x.val).coef)) : MS where
  basis := x.basis
  val := q(PreMS.pow $x.val $a)
  f := q($x.f ^ $a)
  h_wo := q(PreMS.pow_WellOrdered $x.h_wo)
  h_approx := q(PreMS.pow_Approximates $x.h_basis $x.h_wo $x.h_approx $h_trimmed $h_pos)
  h_basis := x.h_basis

end MS

end TendstoTactic
