/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic

/-!
# LogBasis
-/

open Asymptotics Filter

namespace TendstoTactic

/-- Approximations of logarithm of all but last basis functions. -/
inductive LogBasis : Basis → Type
| nil : LogBasis []
| single (f : ℝ → ℝ) : LogBasis [f]
| cons (basis_hd basis_tl_hd : ℝ → ℝ) (basis_tl_tl : Basis)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl))
    (ms : PreMS (basis_tl_hd :: basis_tl_tl)) :
    LogBasis (basis_hd :: basis_tl_hd :: basis_tl_tl)

namespace LogBasis

def WellFormed {basis : Basis} (logBasis : LogBasis basis) : Prop :=
  match logBasis with
  | .nil => True
  | .single f => True
  | .cons basis_hd _ _ logBasis_tl ms =>
    ms.WellOrdered ∧
    ms.Approximates (Real.log ∘ basis_hd) ∧
    WellFormed logBasis_tl

theorem nil_WellFormed : WellFormed (.nil) := by simp [WellFormed]

theorem single_WellFormed (f : ℝ → ℝ) : WellFormed (.single f) := by simp [WellFormed]

theorem WellFormed_cons_WellOrdered {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)} {ms : PreMS (basis_tl_hd :: basis_tl_tl)}
    (h : WellFormed (.cons basis_hd _ _ logBasis_tl ms)) :
    ms.WellOrdered := by
  simp [WellFormed] at h
  exact h.left

theorem WellFormed_cons_Approximates {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)} {ms : PreMS (basis_tl_hd :: basis_tl_tl)}
    (h : WellFormed (.cons basis_hd _ _ logBasis_tl ms)) :
    ms.Approximates (Real.log ∘ basis_hd) := by
  simp [WellFormed] at h
  exact h.right.left

@[reducible]
def tail {basis_hd : ℝ → ℝ} {basis_tl : Basis} (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis basis_tl :=
  match logBasis with
  | .single f => .nil
  | .cons _ _ _ logBasis_tl _ => logBasis_tl

theorem tail_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)} (h_wf : logBasis.WellFormed) :
    (logBasis.tail).WellFormed := by
  cases logBasis with
  | single => simp [WellFormed]
  | cons _ _ _ logBasis_tl ms =>
    simp [WellFormed] at h_wf
    simp [tail]
    exact h_wf.right.right

@[reducible]
noncomputable def extendBasisMiddle {right_hd : ℝ → ℝ} {left right_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (left ++ right_hd :: right_tl)) (ms : PreMS (right_hd :: right_tl)) :
    LogBasis (left ++ f :: right_hd :: right_tl) :=
  match left with
  | [] => .cons _ _ _ logBasis ms
  | List.cons _ left_tl =>
    match left_tl with
    | [] =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms'  =>
        .cons _ _ _ (extendBasisMiddle (left := []) f logBasis_tl ms)
          (ms'.extendBasisMiddle (left := []) f)
    | List.cons left_tl_hd left_tl_tl =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms' =>
        .cons _ _ _
          (extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f logBasis_tl ms)
          (ms'.extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f)

@[reducible]
noncomputable def extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (basis_hd :: basis_tl)) (ms : PreMS [f]) :
    LogBasis (basis_hd :: basis_tl ++ [f]) :=
  match logBasis with
  | .single _ => .cons _ _ _ (.single _) ms
  | .cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    .cons _ _ _ (extendBasisEnd f logBasis_tl ms)
      (ms'.extendBasisEnd _)

@[reducible]
noncomputable def insertLastLog {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
  logBasis.extendBasisEnd (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)) (PreMS.monomial _ 0)

theorem extendBasisMiddle_WellFormed {right_hd : ℝ → ℝ} {left right_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (left ++ right_hd :: right_tl)} {ms : PreMS (right_hd :: right_tl)}
    (h_basis : WellFormedBasis (left ++ f :: right_hd :: right_tl))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered) (h_approx : ms.Approximates (Real.log ∘ f)) :
    (logBasis.extendBasisMiddle f ms).WellFormed := by
  cases' left with left_hd left_tl
  · cases logBasis with
    | single => simp [WellFormed, h_wo, h_approx]
    | cons _ right_tl_hd right_tl_tl logBasis_tl ms' =>
      simp [WellFormed] at h_wf
      simp [extendBasisMiddle, WellFormed, h_wo, h_approx, h_wf]
  cases' left_tl with left_tl_hd left_tl_tl
  · cases logBasis with | cons _ _ _ logBasis_tl ms' =>
    simp [WellFormed] at h_wf
    simp [extendBasisMiddle, WellFormed, h_wo, h_approx, h_wf.right]
    constructor
    · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
    · apply PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
  cases logBasis with | cons _ _ _ logBasis_tl ms' =>
  simp [WellFormed] at h_wf
  simp [extendBasisMiddle, WellFormed]
  constructor
  · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
  constructor
  · exact PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
  · exact extendBasisMiddle_WellFormed h_basis.tail h_wf.right.right h_wo h_approx

theorem extendBasisEnd_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (basis_hd :: basis_tl)} {ms : PreMS [f]}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl ++ [f]))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ (basis_hd :: basis_tl).getLast
      (basis_tl.cons_ne_nil basis_hd))) :
    (logBasis.extendBasisEnd f ms).WellFormed := by
  cases logBasis with
  | single => simpa [WellFormed, h_wo] using h_approx
  | cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    simp [WellFormed] at h_wf
    simp [extendBasisEnd, WellFormed, h_wo, h_approx, h_wf]
    constructor
    · exact PreMS.extendBasisEnd_WellOrdered h_wf.left
    constructor
    · exact PreMS.extendBasisEnd_Approximates h_basis.tail h_wf.right.left
    · exact extendBasisEnd_WellFormed h_basis.tail h_wf.right.right h_wo h_approx

theorem insertLastLog_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_wf : logBasis.WellFormed) :
    (logBasis.insertLastLog).WellFormed := by
  simp [insertLastLog]
  apply extendBasisEnd_WellFormed
  · exact insertLastLog_WellFormedBasis h_basis
  · exact h_wf
  · exact PreMS.monomial_WellOrdered
  · have : WellFormedBasis [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)] := by
      apply WellFormedBasis.single
      apply Filter.Tendsto.comp Real.tendsto_log_atTop
      apply h_basis.right
      simp
    exact PreMS.monomial_Approximates this (n := ⟨0, by simp⟩)

end LogBasis

end TendstoTactic
