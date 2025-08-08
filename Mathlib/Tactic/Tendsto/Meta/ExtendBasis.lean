/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Meta.MS
import Qq

/-!
# TODO
-/

open Filter Asymptotics Stream' Seq TendstoTactic

open Lean Elab Meta Tactic Qq

namespace TendstoTactic

-- TODO: replace `hf_tendsto`, `h_comp_left` and `h_comp_right` with
-- mechanically verifiable assumptions using `logf`.
def MS.extendBasisMiddle (left : Q(Basis)) (f right_hd : Q(ℝ → ℝ)) (right_tl : Q(Basis)) (ms : MS)
    (hf_tendsto : Q(Filter.Tendsto $f atTop atTop))
    (hf_comp_left : Q(∀ g, List.getLast? $left = .some g → (Real.log ∘ $f) =o[atTop] (Real.log ∘ g)))
    (hf_comp_right : Q((Real.log ∘ $right_hd) =o[atTop] (Real.log ∘ $f)))
    (logf : Q(PreMS ($right_hd :: $right_tl)))
    (h_wo : Q(PreMS.WellOrdered $logf))
    (h_approx : Q(PreMS.Approximates $logf (Real.log ∘ $f)))
    (h : $ms.basis =Q $left ++ $right_hd :: $right_tl)
    : MS where
  basis := q($left ++ $f :: $right_hd :: $right_tl)
  logBasis :=
    q(@LogBasis.extendBasisMiddle $right_hd $left $right_tl $f $ms.logBasis $logf $h_wo $h_approx)
  val := q(@PreMS.extendBasisMiddle $left ($right_hd :: $right_tl) $f $ms.val)
  f := ms.f
  h_wo := q(PreMS.extendBasisMiddle_WellOrdered $ms.h_wo)
  h_approx := q(PreMS.extendBasisMiddle_Approximates $ms.h_approx)
  h_basis := q(WellFormedBasis.insert $ms.h_basis $hf_tendsto $hf_comp_left sorry)

def MS.extendBasisEnd (basis_hd : Q(ℝ → ℝ)) (basis_tl : Q(Basis)) (f : Q(ℝ → ℝ)) (ms : MS)
    (hf_tendsto : Q(Filter.Tendsto $f atTop atTop))
    (hf_comp : Q((Real.log ∘ $f) =o[atTop] (Real.log ∘ (List.getLast ($basis_hd :: $basis_tl) (List.cons_ne_nil _ _)))))
    (logf : Q(PreMS [$f]))
    (h_wo : Q(PreMS.WellOrdered $logf))
    (h_approx : Q(PreMS.Approximates $logf (Real.log ∘ (List.getLast ($basis_hd :: $basis_tl) (List.cons_ne_nil _ _)))))
    (h : $ms.basis =Q $basis_hd :: $basis_tl)
    : MS where
  basis := q($basis_hd :: $basis_tl ++ [$f])
  logBasis :=
    q(@LogBasis.extendBasisEnd $basis_hd $basis_tl $f $ms.logBasis $logf $h_wo $h_approx)
  val := q(@PreMS.extendBasisEnd ($basis_hd :: $basis_tl) $f $ms.val)
  f := ms.f
  h_wo := q(PreMS.extendBasisEnd_WellOrdered $ms.h_wo)
  h_approx := q(PreMS.extendBasisEnd_Approximates $ms.h_approx)
  h_basis := q(WellFormedBasis.push $ms.h_basis $hf_tendsto sorry)


end TendstoTactic
