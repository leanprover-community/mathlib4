import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.BasicNew
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Powser
import Mathlib.Tactic.Tendsto.Multiseries.TrimmingNew

set_option linter.unusedVariables false
set_option linter.style.longLine false

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS


-- 1/(1-t), i.e. ones
def LazySeries.inv' : LazySeries :=
  let g : Unit → CoList.OutType ℝ Unit := fun () => .cons 1 ()
  CoList.corec g ()

-- 1/(1+t), i.e. [1, -1, 1, -1, ...]
def LazySeries.inv : LazySeries :=
  let g : Bool → CoList.OutType ℝ Bool := fun b => .cons (b.casesOn 1 (-1)) !b
  CoList.corec g false

theorem LazySeries.inv'_eq_cons_self : LazySeries.inv' = .cons 1 LazySeries.inv' := by
  simp [inv']
  conv =>
    lhs
    rw [CoList.corec_cons (by rfl)]

example (x : ℝ) (hx : |x| < 1) : LazySeries.inv'.toFun x = 1/(1 - x) := by
  simp [toFun]
  have h_inv' : inv'.toFormalMultilinearSeries = formalMultilinearSeries_geometric ℝ ℝ := by
    have h_inv'_get : ∀ n, inv'.get n = .some 1 := by
      intro n
      induction n with
      | zero =>
        rw [inv'_eq_cons_self]
        simp
      | succ m ih =>
        simp at ih ⊢
        rw [inv'_eq_cons_self]
        simpa
    ext n f
    simp only [toFormalMultilinearSeries, h_inv'_get, one_smul, formalMultilinearSeries_geometric]
  rw [h_inv']
  have := (hasFPowerSeriesOnBall_inv_one_sub ℝ ℝ).hasSum (show x ∈ _ by
    apply EMetric.mem_ball.mpr
    simp [edist, PseudoMetricSpace.edist]
    exact hx
  )
  simp at this
  simp [FormalMultilinearSeries.sum]
  exact HasSum.tsum_eq this

#eval! LazySeries.inv.take 10

noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms⁻¹
  | basis_hd :: basis_tl =>
    ms.casesOn'
    (nil := .nil)
    (cons := fun (deg, coef) tl =>
      mulMonomial (LazySeries.inv.apply (mulMonomial tl coef.inv (-deg))) coef.inv (-deg)
    )

theorem inv_toFun (x : ℝ) (hx : |x| < 1) : LazySeries.inv.toFun x = (1 + x)⁻¹ := by
  sorry


theorem inv_analytic : AnalyticAt ℝ (toFun LazySeries.inv) 0 := by
  sorry

theorem inv_isApproximation {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : MS.wellOrderedBasis basis) (h_wo : ms.wellOrdered)
    (h_trimmed : ms.isTrimmed) (h_approx : ms.isApproximation F basis) : ms.inv.isApproximation (F⁻¹) basis := by
  cases basis with
  | nil =>
    unfold inv
    simp only [isApproximation] at *
    apply EventuallyEq.inv h_approx
  | cons basis_hd basis_tl =>
    unfold inv
    revert h_trimmed h_approx
    apply ms.casesOn
    · intro h_trimmed h_approx
      replace h_approx := isApproximation_nil h_approx
      simp
      apply isApproximation.nil
      conv =>
        rhs
        ext x
        simp
        rw [← inv_zero]
      apply EventuallyEq.inv h_approx
    · intro (deg, coef) tl h_trimmed h_approx
      replace h_trimmed := isTrimmed_cons h_trimmed
      obtain ⟨h_coef_trimmed, h_ne_zero⟩ := h_trimmed
      replace h_approx := isApproximation_cons h_approx
      obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
      simp only [CoList.casesOn_cons]
      have hC_ne_zero : ∀ᶠ x in atTop, C x ≠ 0 := by

        apply
      let X : PreMS (basis_hd :: basis_tl) := mulMonomial tl coef.inv (-deg)
      let g : ℝ → ℝ := fun x ↦ (C x)⁻¹ * basis_hd x ^ (-deg) * (F x - basis_hd x ^ deg * C x)
      have hg_tendsto : Tendsto g atTop (nhds 0) := by
        sorry
      have hg_lt : ∀ᶠ x in atTop, |g x| < 1 := by
        have := LinearOrderedAddCommGroup.tendsto_nhds.mp hg_tendsto 1 (by linarith)
        simpa only [sub_zero] using this
      have hg : (LazySeries.inv.toFun ∘ g) =ᶠ[atTop] fun x ↦ (1 + g x)⁻¹ := by
        simp only [EventuallyEq]
        apply Eventually.mono hg_lt
        intro x h
        simp
        rw [inv_toFun]
        exact h
      have hX_approx : X.isApproximation g := by
        sorry
      have := apply_isApproximation inv_analytic (h_approx := hX_approx)
      specialize this h_wo
      specialize this (by
        focus
        sorry -- X has negative leading because of well-order
      )
      specialize this (by
        sorry -- mulMonomial keeps trimmed
      )
      replace this := isApproximation_of_EventuallyEq this hg
      have : F⁻¹ = fun x ↦ (C x)⁻¹ * (basis_hd x)^(-deg) * (1 + g x)⁻¹ := by
        have h_pos : ∀ x, 0 ≤ basis_hd x := by sorry
        ext x
        simp [g]
        conv =>
          rhs
          arg 1
          arg 2
          rw [Real.rpow_neg (h_pos _)]
        rw [← mul_inv, ← mul_inv]
        congr
        rw [mul_add]
        simp
        conv =>
        rhs; rhs
        rw [show C x * basis_hd x ^ deg * ((C x)⁻¹ * basis_hd x ^ (-deg) * (F x - basis_hd x ^ deg * C x)) =
          C x * basis_hd x ^ deg * (C x)⁻¹ * basis_hd x ^ (-deg) * (F x - basis_hd x ^ deg * C x) by ring]
        lhs
        lhs
        rw [show C x * basis_hd x ^ deg * (C x)⁻¹ = C x * (C x)⁻¹ * basis_hd x ^ deg by ring]
        rw [mul_inv_cancel₀]



      unfold Function.comp at this
      simp at this

      conv at this =>
        arg 1
        ext x
        rw [inv_toFun]



      apply isApproximation_mul

end PreMS

end TendstoTactic
