/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Powser
import Mathlib.Tactic.Tendsto.Multiseries.Trimming
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm

/-!
# Inversion for multiseries

-/

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq

-- 1/(1-t), i.e. ones
def invSeries' : LazySeries :=
  let g : Unit → Option (ℝ × Unit) := fun () => some (1, ())
  Seq.corec g ()

-- 1/(1+t), i.e. [1, -1, 1, -1, ...]
def invSeries : LazySeries :=
  let g : Bool → Option (ℝ × Bool) := fun b => some ((b.casesOn 1 (-1)), !b)
  Seq.corec g false

theorem invSeries'_eq_cons_self : invSeries' = .cons 1 invSeries' := by
  simp [invSeries']
  conv =>
    lhs
    rw [Seq.corec_cons (by rfl)]

theorem invSeries'_get_eq_one {n : ℕ} : invSeries'.get? n = .some 1 := by
  induction n with
  | zero =>
    rw [invSeries'_eq_cons_self]
    simp
  | succ m ih =>
    rw [invSeries'_eq_cons_self]
    simpa using ih

theorem invSeries'_eq_geom :
    invSeries'.toFormalMultilinearSeries = formalMultilinearSeries_geometric ℝ ℝ := by
  ext n f
  simp only [formalMultilinearSeries_geometric, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    toFormalMultilinearSeries_coeff, invSeries'_get_eq_one, smul_eq_mul, Option.getD_some, mul_one,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  exact Eq.symm List.prod_ofFn

theorem invSeries'_analytic : analytic invSeries' := by
  simp [analytic, invSeries'_eq_geom, formalMultilinearSeries_geometric_radius]

-- TODO: rewrite
theorem invSeries'_toFun_eq {x : ℝ} (hx : ‖x‖ < 1) : invSeries'.toFun x = (1 - x)⁻¹ := by
  simp [toFun, invSeries'_eq_geom]
  have := hasFPowerSeriesOnBall_inv_one_sub ℝ ℝ
  have := HasFPowerSeriesOnBall.sum this (y := x)
    (by simpa [edist, PseudoMetricSpace.edist] using hx)
  simp at this
  exact this.symm

-- noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
--   match basis with
--   | [] => ms⁻¹
--   | basis_hd :: basis_tl =>
--     ms.casesOn'
--     (nil := .nil)
--     (cons := fun (exp, coef) tl =>
--       mulMonomial (invSeries.apply (mulMonomial tl coef.inv (-exp))) coef.inv (-exp)
--     )

-- Variant with true geometric series (not alternating one) but with neg.
-- Generaly it's easier to use `inv`, but there is no API for `[1, -1, 1, ...]`,
-- while enough for `[1, 1, 1, ...]`.
noncomputable def inv' {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms⁻¹
  | List.cons _ _ =>
    match destruct ms with
    | none => .nil
    | some ((exp, coef), tl) => mulMonomial
      (invSeries'.apply (mulMonomial (neg tl) coef.inv' (-exp))) coef.inv' (-exp)

theorem inv'_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.inv'.WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · simp [inv']
      apply WellOrdered.nil
    · obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
      simp [inv']
      apply mulMonomial_WellOrdered
      · apply apply_WellOrdered
        · apply mulMonomial_WellOrdered
          · apply neg_WellOrdered h_tl
          · apply inv'_WellOrdered
            exact h_coef
        · simp [HasNegativeLeading]
          generalize leadingExp tl = t at *
          cases t with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply inv'_WellOrdered
        exact h_coef

theorem inv'_Approximates {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : MS.WellOrderedBasis basis) (h_wo : ms.WellOrdered)
    (h_trimmed : ms.Trimmed) (h_approx : ms.Approximates F) : ms.inv'.Approximates (F⁻¹) := by
  cases basis with
  | nil =>
    unfold inv'
    simp only [Approximates] at *
    apply EventuallyEq.inv h_approx
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      simp [inv']
      apply Approximates.nil
      conv =>
        rhs
        ext x
        simp
        rw [← inv_zero]
      apply EventuallyEq.inv h_approx
    · apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have hC_ne_zero : ∀ᶠ x in atTop, C x ≠ 0 :=
        eventually_ne_zero_of_not_FlatZero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed
          (MS.WellOrderedBasis_tail h_basis)
      have h_basis_hd_pos : ∀ᶠ x in atTop, 0 < basis_hd x :=
        MS.basis_head_eventually_pos h_basis
      simp [inv']
      apply Approximates_of_EventuallyEq (F := fun x ↦ C⁻¹ x * (basis_hd x)^(-exp) *
        (C x * (basis_hd x)^(exp) * F⁻¹ x))
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_ne_zero]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply mulMonomial_Approximates h_basis
      swap
      · exact inv'_Approximates (MS.WellOrderedBasis_tail h_basis) h_coef_wo h_coef_trimmed h_coef
      have : ((neg tl).mulMonomial coef.inv' (-exp)).Approximates (fun x ↦ C⁻¹ x *
          (basis_hd x)^(-exp) * -(F x - basis_hd x ^ exp * C x))
          (basis := basis_hd :: basis_tl) := by
        apply mulMonomial_Approximates h_basis
        · exact neg_Approximates h_tl
        · exact inv'_Approximates (MS.WellOrderedBasis_tail h_basis) h_coef_wo h_coef_trimmed h_coef
      apply Approximates_of_EventuallyEq
        (F' := (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-exp) * F x)) at this
      swap
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_ne_zero]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply Approximates_of_EventuallyEq
        (F := (fun x ↦ (1 - x)⁻¹) ∘ (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-exp) * F x))
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨_, h_basis_hd_pos⟩
        simp [Real.rpow_neg h_basis_hd_pos.le]
        ring
      apply Approximates_of_EventuallyEq (F := invSeries'.toFun ∘
          (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-exp) * F x))
      · have : Tendsto (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-exp) * F x) atTop (nhds 0) := by
          rw [show (0 : ℝ) = 1 - 1 by simp]
          apply Tendsto.const_sub
          apply Tendsto.congr' (f₁ := F / (fun k ↦ C k * basis_hd k ^ (exp)))
          · simp only [EventuallyEq]
            apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
            intro x ⟨_, h_basis_hd_pos⟩
            simp [Real.rpow_neg h_basis_hd_pos.le]
            ring
          rw [← isEquivalent_iff_tendsto_one]
          conv => rhs; ext x; rw [mul_comm]
          apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
          intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
          simp
          constructor
          · exact hC_ne_zero
          · rw [Real.rpow_eq_zero_iff_of_nonneg]
            · push_neg
              intro h
              simp [h] at h_basis_hd_pos
            · exact h_basis_hd_pos.le
        have : ∀ᶠ x in atTop, ‖1 - C⁻¹ x * basis_hd x ^ (-exp) * F x‖ < 1 := by
          apply NormedAddCommGroup.tendsto_nhds_zero.mp this
          simp
        simp only [EventuallyEq]
        apply Eventually.mono this
        intro x this
        simp
        rw [invSeries'_toFun_eq]
        · simp
        · simpa using this
      apply apply_Approximates invSeries'_analytic h_basis
      · apply mulMonomial_WellOrdered
        · exact neg_WellOrdered h_tl_wo
        · exact inv'_WellOrdered h_coef_wo
      · simp [HasNegativeLeading]
        generalize leadingExp tl = t at h_comp
        cases t with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
      · exact this

end PreMS

-- noncomputable def MS.inv (x : MS) (h_basis : MS.WellOrderedBasis x.basis) (h_trimmed : x.Trimmed) :
--     MS where
--   basis := x.basis
--   val := x.val.inv'
--   F := x.F⁻¹
--   h_wo := PreMS.inv'_WellOrdered x.h_wo
--   h_approx := PreMS.inv'_Approximates h_basis x.h_wo h_trimmed x.h_approx

end TendstoTactic
