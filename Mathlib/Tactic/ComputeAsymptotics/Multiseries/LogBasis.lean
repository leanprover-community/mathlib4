/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming

/-!
# LogBasis
-/

open Asymptotics Filter

namespace ComputeAsymptotics

/-- Approximations of logarithm of all but last basis functions. -/
inductive LogBasis : Basis → Type
| nil : LogBasis []
| single (f : ℝ → ℝ) : LogBasis [f]
| cons (basis_hd basis_tl_hd : ℝ → ℝ) (basis_tl_tl : Basis)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl))
    (ms : PreMS (basis_tl_hd :: basis_tl_tl)) :
    LogBasis (basis_hd :: basis_tl_hd :: basis_tl_tl)

namespace LogBasis

/-- Well-formedness predicate for `LogBasis`. It assures that all multiseries in `logBasis` are
well-ordered, approximate the logarithm of the corresponding basis function, and trimmed. -/
def WellFormed {basis : Basis} (logBasis : LogBasis basis) : Prop :=
  match logBasis with
  | .nil => True
  | .single f => True
  | .cons basis_hd _ _ logBasis_tl ms =>
    ms.WellOrdered ∧
    ms.Approximates (Real.log ∘ basis_hd) ∧
    ms.Trimmed ∧
    WellFormed logBasis_tl

theorem nil_WellFormed : WellFormed (.nil) := by simp [WellFormed]

theorem single_WellFormed (f : ℝ → ℝ) : WellFormed (.single f) := by simp [WellFormed]

theorem WellFormed_cons_WellOrdered {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)} {ms : PreMS (basis_tl_hd :: basis_tl_tl)}
    (h : WellFormed (.cons basis_hd _ _ logBasis_tl ms)) :
    ms.WellOrdered := by
  simp only [WellFormed] at h
  exact h.left

theorem WellFormed_cons_Approximates {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)} {ms : PreMS (basis_tl_hd :: basis_tl_tl)}
    (h : WellFormed (.cons basis_hd _ _ logBasis_tl ms)) :
    ms.Approximates (Real.log ∘ basis_hd) := by
  simp only [WellFormed] at h
  exact h.right.left

theorem WellFormed_cons_Trimmed {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)} {ms : PreMS (basis_tl_hd :: basis_tl_tl)}
    (h : WellFormed (.cons basis_hd _ _ logBasis_tl ms)) :
    ms.Trimmed := by
  simp only [WellFormed] at h
  exact h.right.right.left

/-- Tail of a `LogBasis`. -/
abbrev tail {basis_hd : ℝ → ℝ} {basis_tl : Basis} (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis basis_tl :=
  match logBasis with
  | .single f => .nil
  | .cons _ _ _ logBasis_tl _ => logBasis_tl

theorem tail_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)} (h_wf : logBasis.WellFormed) :
    (logBasis.tail).WellFormed := by
  cases logBasis with
  | single => simp [tail, WellFormed]
  | cons _ _ _ logBasis_tl ms =>
    simp only [WellFormed] at h_wf
    simp only [tail]
    exact h_wf.right.right.right

/-- Extends a `LogBasis` along the basis by adding a function to the middle with a multiseries
approximating its logarithm. -/
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

/-- Extends a `LogBasis` along the basis by adding a function to the end with a multiseries
approximating the logarithm of the last function in the current basis. -/
@[reducible]
noncomputable def extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (basis_hd :: basis_tl)) (ms : PreMS [f]) :
    LogBasis (basis_hd :: basis_tl ++ [f]) :=
  match logBasis with
  | .single _ => .cons _ _ _ (.single _) ms
  | .cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    .cons _ _ _ (extendBasisEnd f logBasis_tl ms)
      (ms'.extendBasisEnd _)

/-- Updates a `LogBasis` when the logarithm of the last function in the current basis is added to
the basis. -/
@[reducible]
noncomputable def insertLastLog {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
  logBasis.extendBasisEnd (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)) (PreMS.monomial _ 0)

-- TODO: rename and move
theorem Approximates_log_basis_ne_zero {basis basis' : Basis} {ms : PreMS basis'} {f : ℝ → ℝ}
    (h_basis : WellFormedBasis basis)
    (h_approx : ms.Approximates (Real.log ∘ f))
    (hf : f ∈ basis) :
    ms ≠ PreMS.zero _ := by
  rintro rfl
  rw [PreMS.zero_Approximates_iff] at h_approx
  have h : Tendsto (Real.log ∘ f) atTop atTop := by
    apply Tendsto.comp Real.tendsto_log_atTop
    exact basis_tendsto_top h_basis _ hf
  apply Filter.Tendsto.congr' h_approx at h
  have h' : Tendsto (0 : ℝ → ℝ) atTop (nhds 0) := tendsto_const_nhds
  have := Filter.Tendsto.disjoint h (disjoint_nhds_atTop 0).symm h'
  simp only [disjoint_self] at this
  contrapose! this
  exact Filter.NeBot.ne'

theorem extendBasisMiddle_WellFormed {right_hd : ℝ → ℝ} {left right_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (left ++ right_hd :: right_tl)} {ms : PreMS (right_hd :: right_tl)}
    (h_basis : WellFormedBasis (left ++ f :: right_hd :: right_tl))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered) (h_approx : ms.Approximates (Real.log ∘ f))
    (h_trimmed : ms.Trimmed) :
    (logBasis.extendBasisMiddle f ms).WellFormed := by
  cases left with
  | nil =>
    cases logBasis with
    | single => simp [WellFormed, h_wo, h_approx, h_trimmed]
    | cons _ right_tl_hd right_tl_tl logBasis_tl ms' =>
      simp only [WellFormed] at h_wf
      simp [WellFormed, h_wo, h_approx, h_trimmed, h_wf]
  | cons left_hd left_tl =>
  cases left_tl with
  | nil =>
    cases logBasis with | cons _ _ _ logBasis_tl ms' =>
    simp only [WellFormed] at h_wf
    simp [extendBasisMiddle, WellFormed, h_wo, h_approx, h_wf.right, and_true, true_and]
    constructor
    · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
    constructor
    · apply PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
    constructor
    · apply PreMS.extendBasisMiddle_Trimmed h_wf.right.right.left
      exact Approximates_log_basis_ne_zero h_basis h_wf.right.left (by simp)
    · exact h_trimmed
  | cons left_tl_hd left_tl_tl =>
    cases logBasis with | cons _ _ _ logBasis_tl ms' =>
    simp only [WellFormed, List.append_eq] at h_wf
    simp only [List.append_eq]
    constructor
    · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
    constructor
    · exact PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
    constructor
    · apply PreMS.extendBasisMiddle_Trimmed h_wf.right.right.left
      exact Approximates_log_basis_ne_zero h_basis h_wf.right.left (by simp)
    · exact extendBasisMiddle_WellFormed h_basis.tail h_wf.right.right.right h_wo h_approx h_trimmed

theorem extendBasisEnd_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (basis_hd :: basis_tl)} {ms : PreMS [f]}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl ++ [f]))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ (basis_hd :: basis_tl).getLast
      (basis_tl.cons_ne_nil basis_hd)))
    (h_trimmed : ms.Trimmed) :
    (logBasis.extendBasisEnd f ms).WellFormed := by
  cases logBasis with
  | single =>
    unfold extendBasisEnd
    simpa [WellFormed, h_wo, h_trimmed]
  | cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    simp only [WellFormed] at h_wf
    unfold extendBasisEnd
    simp only [WellFormed, List.append_eq]
    constructor
    · exact PreMS.extendBasisEnd_WellOrdered h_wf.left
    constructor
    · exact PreMS.extendBasisEnd_Approximates h_basis.tail h_wf.right.left
    constructor
    · exact PreMS.extendBasisEnd_Trimmed h_wf.right.right.left
    · exact extendBasisEnd_WellFormed h_basis.tail h_wf.right.right.right h_wo h_approx h_trimmed

theorem insertLastLog_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_wf : logBasis.WellFormed) :
    (logBasis.insertLastLog).WellFormed := by
  simp only [List.cons_append, insertLastLog]
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
  · exact PreMS.monomial_Trimmed (by simp)

end LogBasis

end ComputeAsymptotics
