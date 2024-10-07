import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Powser
import Mathlib.Tactic.Tendsto.Multiseries.Trimming
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm

set_option linter.unusedVariables false
set_option linter.style.longLine false

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open LazySeries

-- 1/(1-t), i.e. ones
def invSeries' : LazySeries :=
  let g : Unit → CoList.OutType ℝ Unit := fun () => .cons 1 ()
  CoList.corec g ()

-- 1/(1+t), i.e. [1, -1, 1, -1, ...]
def invSeries : LazySeries :=
  let g : Bool → CoList.OutType ℝ Bool := fun b => .cons (b.casesOn 1 (-1)) !b
  CoList.corec g false

theorem invSeries'_eq_cons_self : invSeries' = .cons 1 invSeries' := by
  simp [invSeries']
  conv =>
    lhs
    rw [CoList.corec_cons (by rfl)]

theorem invSeries'_get_eq_one {n : ℕ} : invSeries'.get n = .some 1 := by
  induction n with
  | zero =>
    rw [invSeries'_eq_cons_self]
    simp
  | succ m ih =>
    rw [invSeries'_eq_cons_self]
    simpa using ih

theorem invSeries'_eq_geom : invSeries'.toFormalMultilinearSeries = formalMultilinearSeries_geometric ℝ ℝ := by
  ext n f
  simp only [formalMultilinearSeries_geometric, FormalMultilinearSeries.apply_eq_prod_smul_coeff, toFormalMultilinearSeries_coeff, invSeries'_get_eq_one, smul_eq_mul, Option.getD_some, _root_.mul_one, ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  exact Eq.symm List.prod_ofFn

theorem invSeries'_analytic : analytic invSeries' := by
  simp [analytic, invSeries'_eq_geom, formalMultilinearSeries_geometric_radius]

-- TODO: rewrite
theorem invSeries'_toFun_eq {x : ℝ} (hx : ‖x‖ < 1) : invSeries'.toFun x = (1 - x)⁻¹ := by
  simp [toFun, invSeries'_eq_geom]
  have := hasFPowerSeriesOnBall_inv_one_sub ℝ ℝ
  have := HasFPowerSeriesOnBall.sum this (y := x) (by simpa [edist, PseudoMetricSpace.edist] using hx)
  simp at this
  exact this.symm

-- variant with true geometric series (not alternating one) but with neg
noncomputable def inv' {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms⁻¹
  | basis_hd :: basis_tl =>
    ms.casesOn'
    (nil := .nil) -- 0⁻¹ = 0
    (cons := fun (deg, coef) tl =>
      mulMonomial (invSeries'.apply (mulMonomial (neg tl) coef.inv' (-deg))) coef.inv' (-deg)
    )

theorem inv'_wellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.wellOrdered) : ms.inv'.wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    revert h_wo
    apply ms.casesOn
    · intro h_wo
      simp [inv']
      apply wellOrdered.nil
    · intro (deg, coef) tl h_wo
      obtain ⟨h_coef, h_comp, h_tl⟩ := wellOrdered_cons h_wo
      simp [inv']
      apply mulMonomial_wellOrdered
      · apply apply_wellOrdered invSeries'_analytic
        · apply mulMonomial_wellOrdered
          · apply neg_wellOrdered h_tl
          · apply inv'_wellOrdered
            exact h_coef
        · simp [hasNegativeLeading]
          generalize leadingExp tl = t at *
          cases t with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply inv'_wellOrdered
        exact h_coef

theorem inv'_isApproximation {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : MS.wellOrderedBasis basis) (h_wo : ms.wellOrdered)
    (h_trimmed : ms.isTrimmed) (h_approx : ms.isApproximation F basis) : ms.inv'.isApproximation (F⁻¹) basis := by
  cases basis with
  | nil =>
    unfold inv'
    simp only [isApproximation] at *
    apply EventuallyEq.inv h_approx
  | cons basis_hd basis_tl =>
    revert h_trimmed h_wo h_approx
    apply ms.casesOn
    · intro h_trimmed h_wo h_approx
      replace h_approx := isApproximation_nil h_approx
      simp [inv']
      apply isApproximation.nil
      conv =>
        rhs
        ext x
        simp
        rw [← inv_zero]
      apply EventuallyEq.inv h_approx
    · intro (deg, coef) tl h_wo h_trimmed h_approx
      replace h_trimmed := isTrimmed_cons h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp_wo, h_tl_wo⟩ := wellOrdered_cons h_wo
      replace h_approx := isApproximation_cons h_approx
      obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
      have hC_ne_zero : ∀ᶠ x in atTop, C x ≠ 0 :=
        eventually_ne_zero_of_not_isFlatZero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed
          (MS.wellOrderedBasis_tail h_basis)
      have h_basis_hd_pos : ∀ᶠ x in atTop, 0 < basis_hd x :=
        MS.basis_head_eventually_pos h_basis
      simp [inv']
      apply isApproximation_of_EventuallyEq (F := fun x ↦ C⁻¹ x * (basis_hd x)^(-deg) * (C x * (basis_hd x)^(deg) * F⁻¹ x))
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_ne_zero]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply mulMonomial_isApproximation h_basis
      swap
      · exact inv'_isApproximation (MS.wellOrderedBasis_tail h_basis) h_coef_wo h_coef_trimmed h_coef
      focus
      have : ((neg tl).mulMonomial coef.inv' (-deg)).isApproximation (fun x ↦ C⁻¹ x * (basis_hd x)^(-deg) * -(F x - basis_hd x ^ deg * C x)) (basis_hd :: basis_tl) := by
        apply mulMonomial_isApproximation h_basis
        · exact neg_isApproximation h_tl
        · exact inv'_isApproximation (MS.wellOrderedBasis_tail h_basis) h_coef_wo h_coef_trimmed h_coef
      apply isApproximation_of_EventuallyEq (F' := (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-deg) * F x)) at this
      swap
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_ne_zero]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply isApproximation_of_EventuallyEq (F := (fun x ↦ (1 - x)⁻¹) ∘ (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-deg) * F x))
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
        intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp [Real.rpow_neg h_basis_hd_pos.le]
        ring
      apply isApproximation_of_EventuallyEq (F := invSeries'.toFun ∘ (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-deg) * F x))
      · have : Tendsto (fun x ↦ 1 - C⁻¹ x * basis_hd x ^ (-deg) * F x) atTop (nhds 0) := by
          rw [show (0 : ℝ) = 1 - 1 by simp]
          apply Tendsto.const_sub
          apply Tendsto.congr' (f₁ := F / (fun k ↦ C k * basis_hd k ^ (deg)))
          · simp only [EventuallyEq]
            apply Eventually.mono <| hC_ne_zero.and h_basis_hd_pos
            intro x ⟨hC_ne_zero, h_basis_hd_pos⟩
            simp [Real.rpow_neg h_basis_hd_pos.le]
            ring
          rw [← isEquivalent_iff_tendsto_one]
          conv => rhs; ext x; rw [mul_comm]
          apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp_wo h_basis
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
        have : ∀ᶠ x in atTop, ‖1 - C⁻¹ x * basis_hd x ^ (-deg) * F x‖ < 1 := by
          apply NormedAddCommGroup.tendsto_nhds_zero.mp this
          simp
        simp only [EventuallyEq]
        apply Eventually.mono this
        intro x this
        simp
        rw [invSeries'_toFun_eq]
        · simp
        · simpa using this
      apply apply_isApproximation invSeries'_analytic h_basis
      · apply mulMonomial_wellOrdered
        · exact neg_wellOrdered h_tl_wo
        · exact inv'_wellOrdered h_coef_wo
      · simp [hasNegativeLeading]
        generalize leadingExp tl = t at h_comp_wo
        cases t with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp_wo
      · exact this

noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms⁻¹
  | basis_hd :: basis_tl =>
    ms.casesOn'
    (nil := .nil)
    (cons := fun (deg, coef) tl =>
      mulMonomial (invSeries.apply (mulMonomial tl coef.inv (-deg))) coef.inv (-deg)
    )

end PreMS

end TendstoTactic
