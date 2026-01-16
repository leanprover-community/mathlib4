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

/-!
# Inversion for multiseries

-/

set_option linter.flexible false
set_option linter.style.longLine false

set_option linter.style.multiGoal false

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
  simp only [LazySeries.toFun, invSeries_eq_geom]
  have := hasFPowerSeriesOnBall_inv_one_sub ℝ ℝ
  have := HasFPowerSeriesOnBall.sum this (y := t)
    (by simpa [edist, PseudoMetricSpace.edist] using ht)
  simp only [zero_add] at this
  exact this.symm

theorem invSeries_toFun_eq' : invSeries.toFun =ᶠ[𝓝 0] (fun t ↦ (1 - t)⁻¹) := by
  apply Filter.eventuallyEq_of_mem (s := Metric.ball 0 1)
  · apply Metric.ball_mem_nhds
    simp
  intro t h
  rw [invSeries_toFun_eq]
  simpa using h

mutual

/-- If `ms` approximates `f`, then `ms.inv` approximates `f⁻¹`. -/
noncomputable def SeqMS.inv {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) => SeqMS.mulMonomial
    (SeqMS.apply invSeries (tl.neg.mulMonomial coef.inv (-exp))) coef.inv (-exp)

/-- If `ms` approximates `f`, then `ms.inv` approximates `f⁻¹`. -/
noncomputable def inv {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Inv.inv (α := ℝ) ms.toReal
  | List.cons _ _ =>
    mk (SeqMS.inv ms.seq) ms.toFun⁻¹

end

/-- If `X` and `Y` are multiseries, then `X.div Y` approximates `X / Y`. -/
noncomputable def div {basis : Basis} (X Y : PreMS basis) : PreMS basis :=
  X.mul (Y.inv)

@[simp]
theorem inv_toFun {basis : Basis} {ms : PreMS basis} :
    ms.inv.toFun = ms.toFun⁻¹ := by
  cases basis with
  | nil => simp [inv, toReal]; rfl
  | cons basis_hd basis_tl => simp [inv]

@[simp]
theorem inv_seq {basis_hd basis_tl} {ms : PreMS (basis_hd :: basis_tl)} :
    ms.inv.seq = SeqMS.inv ms.seq := by
  simp [inv]

mutual

theorem SeqMS.neg_inv_comm {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} :
    ms.neg.inv = ms.inv.neg := by
  cases ms with
  | nil => simp [SeqMS.inv]
  | cons exp coef tl =>
    simp [SeqMS.inv]
    rw [neg_inv_comm, SeqMS.mulMonomial_neg_left]
    congr 3
    simp [SeqMS.mulMonomial_neg_left, SeqMS.mulMonomial_neg_right]


theorem neg_inv_comm {basis : Basis} {ms : PreMS basis} :
    ms.neg.inv = ms.inv.neg := by
  cases basis with
  | nil => simp [neg, inv, mulConst, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp [ms_eq_ms_iff_mk_eq_mk]
    exact SeqMS.neg_inv_comm

end

mutual

theorem SeqMS.inv_WellOrdered {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl}
    (h_wo : ms.WellOrdered) : ms.inv.WellOrdered := by
  cases ms with
  | nil =>
    simp only [SeqMS.inv, SeqMS.destruct_nil]
    apply WellOrdered.nil
  | cons exp coef tl =>
    obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
    simp only [SeqMS.inv, SeqMS.destruct_cons]
    apply SeqMS.mulMonomial_WellOrdered
    · apply SeqMS.apply_WellOrdered
      · apply SeqMS.mulMonomial_WellOrdered
        · apply SeqMS.neg_WellOrdered h_tl
        · apply inv_WellOrdered
          exact h_coef
      · simp only [SeqMS.mulMonomial_leadingExp, SeqMS.neg_leadingExp]
        generalize tl.leadingExp = w at *
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
    · apply inv_WellOrdered
      exact h_coef

theorem inv_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.inv.WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp at *
    exact SeqMS.inv_WellOrdered h_wo

end

theorem tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero
    {basis_hd basis_tl} {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    {f : ℝ → ℝ}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_wo : WellOrdered (mk (.cons exp coef tl) f))
    (h_approx : (mk (.cons exp coef tl) f).Approximates)
    (h_trimmed : Trimmed (mk (.cons exp coef tl) f)) :
    Tendsto ((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial coef.inv (-exp)).toFun atTop (𝓝 0) := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
  have := IsEquivalent_coef h_approx h_wo h_coef_trimmed h_coef_ne_zero h_basis
  obtain ⟨φ, hφ, hf⟩ := this.exists_eq_mul
  simp
  have h_basis_hd_pos := basis_head_eventually_pos h_basis
  have h_coef_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 :=
    eventually_ne_zero_of_not_zero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed h_basis.tail
  apply Filter.Tendsto.congr' (f₁ := φ - 1)
  · apply (hf.and (h_basis_hd_pos.and h_coef_ne_zero)).mono
    intro t ⟨hf, h_basis_hd_pos, h_coef_ne_zero⟩
    simp [hf]
    rw [Real.rpow_neg h_basis_hd_pos.le]
    field_simp
  convert hφ.sub (tendsto_const_nhds (x := 1)) using 1
  simp

-- TODO: do we need `ms.WellOrdered`?
theorem inv_Approximates {basis : Basis} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) : ms.inv.Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    cases ms with
    | nil f =>
      apply Approximates_nil at h_approx
      simp [inv, SeqMS.inv]
      grw [h_approx]
      apply EventuallyEq.of_eq
      ext t
      simp
    | cons exp coef tl f =>
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have h_coef_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 :=
        eventually_ne_zero_of_not_zero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed
          (h_basis.tail)
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      simp [inv, SeqMS.inv]
      let ms : PreMS (basis_hd :: basis_tl) := (PreMS.apply invSeries ((mk tl (f - basis_hd ^ exp * coef.toFun)).neg.mulMonomial coef.inv (-exp))).mulMonomial coef.inv (-exp)
      have h : ms.Approximates := by
        simp [ms]
        apply mulMonomial_Approximates h_basis
        swap
        · apply inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
        apply apply_Approximates invSeries_analytic h_basis
        · simp
          generalize tl.leadingExp = w at h_comp
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
        · simp
          apply SeqMS.mulMonomial_WellOrdered
          · apply SeqMS.neg_WellOrdered h_tl_wo
          · apply inv_WellOrdered h_coef_wo
        apply mulMonomial_Approximates h_basis
        · apply neg_Approximates h_tl
        · apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      convert replaceFun_Approximates _ h
      have h_tendsto_zero : Tendsto ((basis_hd ^ exp * coef.toFun - f) * basis_hd ^ (-exp) * coef.toFun⁻¹) atTop (𝓝 0) := by
        convert (tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx h_trimmed).neg.congr' _
        · simp
        simp
        apply (h_coef_ne_zero.and h_basis_hd_pos).mono
        intro t ⟨h_coef_ne_zero, h_basis_hd_pos⟩
        simp
        field
      simp [ms]
      set g := (basis_hd ^ exp * coef.toFun - f) * basis_hd ^ (-exp) * coef.toFun⁻¹
      apply invSeries_toFun_eq'.comp_tendsto at h_tendsto_zero
      grw [h_tendsto_zero]
      apply (h_coef_ne_zero.and h_basis_hd_pos).mono
      intro t ⟨h_coef_ne_zero, h_basis_hd_pos⟩
      simp [g]
      rw [Real.rpow_neg h_basis_hd_pos.le]
      field_simp
      congr
      ring

theorem div_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X.div Y).WellOrdered := by
  apply mul_WellOrdered hX_wo
  exact inv_WellOrdered hY_wo

theorem div_Approximates {basis : Basis} {X Y : PreMS basis}
    (h_basis : WellFormedBasis basis)
    (hY_wo : Y.WellOrdered)
    (hY_trimmed : Y.Trimmed)
    (hX_approx : X.Approximates) (hY_approx : Y.Approximates) :
    (X.div Y).Approximates := by
  apply mul_Approximates h_basis hX_approx
  exact inv_Approximates h_basis hY_wo hY_approx hY_trimmed

end PreMS
end ComputeAsymptotics
