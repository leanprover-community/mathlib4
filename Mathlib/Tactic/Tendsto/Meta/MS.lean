import Mathlib.Tactic.Tendsto.Multiseries.Main

open Lean Qq TendstoTactic

structure MS where
  basis : Q(Basis)
  val : Q(PreMS $basis)
  F : Q(ℝ → ℝ)
  h_wo : Q(PreMS.WellOrdered $val)
  h_approx : Q(PreMS.Approximates $val $F)
  h_basis : Q(MS.WellOrderedBasis $basis)

-- TODO:
-- 5. inv

namespace MS

section Operations

def const (basis : Q(Basis)) (c : Q(ℝ)) (h_basis : Q(MS.WellOrderedBasis $basis))  : MS where
  basis := basis
  val := q(PreMS.const $basis $c)
  F := q(fun _ ↦ $c)
  h_wo := q(PreMS.const_WellOrdered)
  h_approx := q(PreMS.const_Approximates_const $h_basis)
  h_basis := h_basis

def monomial (basis : Q(Basis)) (n : ℕ) (h : Q($n < List.length $basis))
    (h_basis : Q(MS.WellOrderedBasis $basis)) : MS where
  basis := basis
  val := q(PreMS.monomial $basis $n)
  F := q(List.get $basis ⟨$n, $h⟩)
  h_wo := q(PreMS.monomial_WellOrdered)
  h_approx := q(PreMS.monomial_Approximates $h $h_basis)
  h_basis := h_basis

def neg (x : MS) : MS where
  basis := x.basis
  val := q(PreMS.neg $x.val)
  F := q(-$x.F)
  h_wo := q(PreMS.neg_WellOrdered $x.h_wo)
  h_approx := q(PreMS.neg_Approximates $x.h_approx)
  h_basis := x.h_basis

def add (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  val := q(PreMS.add $x.val $y.val)
  F := q($x.F + $y.F)
  h_wo := q(PreMS.add_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.add_Approximates $x.h_approx $y.h_approx)
  h_basis := x.h_basis

def mul (x y : MS) (h_basis_eq : $x.basis =Q $y.basis) : MS where
  basis := x.basis
  val := q(PreMS.mul $x.val $y.val)
  F := q($x.F * $y.F)
  h_wo := q(PreMS.mul_WellOrdered $x.h_wo $y.h_wo)
  h_approx := q(PreMS.mul_Approximates $x.h_basis $x.h_approx $y.h_approx)
  h_basis := x.h_basis

end Operations

end MS
