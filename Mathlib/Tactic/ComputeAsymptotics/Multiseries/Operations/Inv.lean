/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Powser
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.LeadingTerm

set_option linter.style.multiGoal false

/-!
# Inversion for multiseries

-/

@[expose] public section

-- TODO: refactor using Pow.lean

open Filter Asymptotics
open scoped Topology

namespace ComputeAsymptotics

namespace PreMS

open LazySeries Stream'

/-- Taylor series for 1 / (1 - t), i.e.
```
1 / (1 - t) = 1 + t + t^2 + t^3 + ...
```
-/
def invSeries : LazySeries :=
  let g : Unit → Option (ℝ × Unit) := fun () => some (1, ())
  Seq.corec g ()

theorem invSeries_eq_cons_self : invSeries = .cons 1 invSeries := by
  simp only [invSeries]
  conv =>
    lhs
    rw [Seq.corec_cons (by rfl)]

theorem invSeries_get_eq_one {n : ℕ} : invSeries.get? n = .some 1 := by
  induction n with
  | zero =>
    rw [invSeries_eq_cons_self]
    simp
  | succ m ih =>
    rw [invSeries_eq_cons_self]
    simpa using ih

theorem invSeries_eq_geom :
    invSeries.toFormalMultilinearSeries = formalMultilinearSeries_geometric ℝ ℝ := by
  ext n
  simp only [formalMultilinearSeries_geometric, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    toFormalMultilinearSeries_coeff, invSeries_get_eq_one, smul_eq_mul, Option.getD_some, mul_one,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  exact Eq.symm List.prod_ofFn

theorem invSeries_analytic : Analytic invSeries := by
  simp [Analytic, invSeries_eq_geom, formalMultilinearSeries_geometric_radius]

-- TODO: rewrite
theorem invSeries_toFun_eq {t : ℝ} (ht : |t| < 1) : invSeries.toFun t = (1 - t)⁻¹ := by
  simp only [toFun, invSeries_eq_geom]
  have := hasFPowerSeriesOnBall_inv_one_sub ℝ ℝ
  have := HasFPowerSeriesOnBall.sum this (y := t)
    (by simpa [edist, PseudoMetricSpace.edist] using ht)
  simp only [zero_add] at this
  exact this.symm

/-- If `ms` approximates `f`, then `ms.inv` approximates `f⁻¹`. -/
noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Inv.inv (α := ℝ) ms.toReal
  | List.cons _ _ =>
    match destruct ms with
    | none => .nil
    | some (exp, coef, tl) => mulMonomial
      (invSeries.apply (mulMonomial (neg tl) coef.inv (-exp))) coef.inv (-exp)

/-- If `X` and `Y` are multiseries, then `X.div Y` approximates `X / Y`. -/
noncomputable def div {basis : Basis} (X Y : PreMS basis) : PreMS basis :=
  X.mul (Y.inv)

theorem neg_inv_comm {basis : Basis} {ms : PreMS basis} :
    ms.neg.inv = ms.inv.neg := by
  cases basis with
  | nil => simp [neg, inv, mulConst]
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => simp [inv]
    | cons exp coef tl =>
      simp only [inv, neg_cons, destruct_cons, neg_neg]
      rw [neg_inv_comm, mulMonomial_neg_left]
      congr 3
      simp [mulMonomial_neg_left, mulMonomial_neg_right]

theorem inv_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.inv.WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      simp only [inv, destruct_nil]
      apply WellOrdered.nil
    | cons exp coef tl =>
      obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
      simp only [inv, destruct_cons]
      apply mulMonomial_WellOrdered
      · apply apply_WellOrdered
        · apply mulMonomial_WellOrdered
          · apply neg_WellOrdered h_tl
          · apply inv_WellOrdered
            exact h_coef
        · simp only [mulMonomial_leadingExp, neg_leadingExp]
          generalize leadingExp tl = w at *
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply inv_WellOrdered
        exact h_coef

-- TODO: do we need `ms.WellOrdered`?
theorem inv_Approximates {basis : Basis} {f : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed) : ms.inv.Approximates (f⁻¹) := by
  cases basis with
  | nil =>
    unfold inv
    simp at h_approx ⊢
    exact h_approx.inv
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      apply Approximates_nil at h_approx
      simp only [inv, destruct_nil]
      apply Approximates.nil
      conv =>
        rhs
        ext
        rw [Pi.zero_apply, ← inv_zero]
      apply EventuallyEq.inv h_approx
    | cons exp coef tl =>
      apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have hC_ne_zero : ∀ᶠ t in atTop, fC t ≠ 0 :=
        eventually_ne_zero_of_not_zero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed
          (h_basis.tail)
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      simp only [inv, destruct_cons]
      apply Approximates_of_EventuallyEq (f := fun t ↦ fC⁻¹ t * (basis_hd t)^(-exp) *
        (fC t * (basis_hd t)^(exp) * f⁻¹ t))
      · simp only [EventuallyEq]
        apply (hC_ne_zero.and h_basis_hd_pos).mono
        intro t ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp only [Pi.inv_apply]
        ring_nf
        simp only [mul_inv_cancel₀ hC_ne_zero, one_mul, ← Real.rpow_add h_basis_hd_pos,
          neg_add_cancel, Real.rpow_zero]
      apply mulMonomial_Approximates h_basis
      swap
      · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      have : ((neg tl).mulMonomial coef.inv (-exp)).Approximates (fun t ↦ fC⁻¹ t *
          (basis_hd t)^(-exp) * -(f t - basis_hd t ^ exp * fC t))
          (basis := basis_hd :: basis_tl) := by
        apply mulMonomial_Approximates h_basis
        · exact neg_Approximates h_tl
        · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      apply Approximates_of_EventuallyEq
        (f' := (fun t ↦ 1 - fC⁻¹ t * basis_hd t ^ (-exp) * f t)) at this
      swap
      · simp only [EventuallyEq]
        apply (hC_ne_zero.and h_basis_hd_pos).mono
        intro t ⟨hC_ne_zero, h_basis_hd_pos⟩
        simp only [Pi.inv_apply, neg_sub]
        ring_nf
        simp [mul_inv_cancel₀ hC_ne_zero, ← Real.rpow_add h_basis_hd_pos]
      apply Approximates_of_EventuallyEq
        (f := (fun t ↦ (1 - t)⁻¹) ∘ (fun t ↦ 1 - fC⁻¹ t * basis_hd t ^ (-exp) * f t))
      · simp only [EventuallyEq]
        apply h_basis_hd_pos.mono
        intro t h_basis_hd_pos
        simp only [Pi.inv_apply, Function.comp_apply, Real.rpow_neg h_basis_hd_pos.le,
          sub_sub_cancel, mul_inv_rev, inv_inv]
        ring
      apply Approximates_of_EventuallyEq (f := invSeries.toFun ∘
          (fun t ↦ 1 - fC⁻¹ t * basis_hd t ^ (-exp) * f t))
      · have : Tendsto (fun t ↦ 1 - fC⁻¹ t * basis_hd t ^ (-exp) * f t) atTop (𝓝 0) := by
          rw [show (0 : ℝ) = 1 - 1 by simp]
          apply Tendsto.const_sub
          apply Tendsto.congr' (f₁ := f / (fun k ↦ fC k * basis_hd k ^ (exp)))
          · simp only [EventuallyEq]
            apply h_basis_hd_pos.mono
            intro t h_basis_hd_pos
            simp only [Pi.div_apply, Pi.inv_apply, Real.rpow_neg h_basis_hd_pos.le]
            ring
          rw [← isEquivalent_iff_tendsto_one]
          conv_rhs => ext t; rw [mul_comm]
          apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          apply (hC_ne_zero.and h_basis_hd_pos).mono
          intro t ⟨hC_ne_zero, h_basis_hd_pos⟩
          simp only [ne_eq, mul_eq_zero, not_or]
          constructor
          · exact hC_ne_zero
          · rw [Real.rpow_eq_zero_iff_of_nonneg]
            · push_neg
              intro h
              simp [h] at h_basis_hd_pos
            · exact h_basis_hd_pos.le
        have : ∀ᶠ t in atTop, ‖1 - fC⁻¹ t * basis_hd t ^ (-exp) * f t‖ < 1 := by
          apply NormedAddCommGroup.tendsto_nhds_zero.mp this
          simp
        simp only [EventuallyEq]
        apply this.mono
        intro t this
        simp only [Pi.inv_apply, Function.comp_apply, sub_sub_cancel, mul_inv_rev, inv_inv]
        rw [invSeries_toFun_eq]
        · simp
        · simpa using this
      apply apply_Approximates invSeries_analytic h_basis
      · simp only [mulMonomial_leadingExp, neg_leadingExp]
        generalize leadingExp tl = w at h_comp
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
      · exact this

theorem div_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X.div Y).WellOrdered := by
  apply mul_WellOrdered hX_wo
  exact inv_WellOrdered hY_wo

theorem div_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (h_basis : WellFormedBasis basis)
    (hY_wo : Y.WellOrdered)
    (hY_trimmed : Y.Trimmed)
    (hX_approx : X.Approximates fX) (hY_approx : Y.Approximates fY) :
    (X.div Y).Approximates (fX / fY) := by
  apply mul_Approximates h_basis hX_approx
  exact inv_Approximates h_basis hY_wo hY_approx hY_trimmed

end PreMS

end ComputeAsymptotics
