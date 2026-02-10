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

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open LazySeries Stream'

/-- Alternating series [1, -1, 1, -1, ...] starting with `(-1) ^ b` -/
def invSeriesFrom (b : Bool) : LazySeries :=
  let g : Bool → Option (ℝ × Bool) := fun b => some (if b then -1 else 1, !b)
  Seq.corec g b

/-- Taylor series for 1 / (1 + t), i.e.
```
1 / (1 + t) = 1 - t + t^2 - t^3 + ...
```
-/
def invSeries : LazySeries :=
  invSeriesFrom false

theorem invSeriesFrom_eq_cons (b : Bool) :
    invSeriesFrom b = .cons (if b then -1 else 1) (invSeriesFrom !b) := by
  rw [invSeriesFrom, Seq.corec_cons (by rfl)]
  rfl

theorem invSeriesFrom_true_eq_cons :
    invSeriesFrom true = .cons (-1) (invSeriesFrom false) := by
  rw [invSeriesFrom_eq_cons]
  simp

theorem invSeriesFrom_false_eq_cons :
    invSeriesFrom false = .cons 1 (invSeriesFrom true) := by
  rw [invSeriesFrom_eq_cons]
  simp

theorem invSeries_eq_cons :
    invSeries = .cons 1 (invSeriesFrom true) := by
  rw [invSeries, invSeriesFrom_eq_cons]
  simp

theorem invSeriesFrom_get_eq {b : Bool} {n : ℕ} :
    (invSeriesFrom b).get? n = .some (if b then (-1) ^ (n + 1) else (-1) ^ n) := by
  induction n generalizing b with
  | zero =>
    rw [invSeriesFrom_eq_cons]
    simp
  | succ m ih =>
    rw [invSeriesFrom_eq_cons]
    simp [ih]
    cases b <;> simp
    ring

theorem invSeries_get_eq {n : ℕ} : invSeries.get? n = .some ((-1) ^ n) := by
  simp [invSeries, invSeriesFrom_get_eq]

theorem invSeries_eq_geom :
    invSeries.toFormalMultilinearSeries = formalMultilinearSeries_geometric_alternating ℝ ℝ := by
  ext n
  simp [formalMultilinearSeries_geometric_alternating, invSeries_get_eq]

theorem invSeries_convergent : Convergent invSeries := by
  simp [Convergent, invSeries_eq_geom, formalMultilinearSeries_geometric_alternating_radius]

-- TODO: rewrite
theorem invSeries_toFun_eq {t : ℝ} (ht : |t| < 1) : invSeries.toFun t = (1 + t)⁻¹ := by
  simp only [LazySeries.toFun, invSeries_eq_geom]
  have := hasFPowerSeriesOnBall_inv_one_add ℝ ℝ
  have := HasFPowerSeriesOnBall.sum this (y := t)
    (by simpa [edist, PseudoMetricSpace.edist] using ht)
  simp only [zero_add] at this
  exact this.symm

theorem invSeries_toFun_eq' : invSeries.toFun =ᶠ[𝓝 0] (fun t ↦ (1 + t)⁻¹) := by
  apply Filter.eventuallyEq_of_mem (s := Metric.ball 0 1)
  · apply Metric.ball_mem_nhds
    simp
  intro t h
  rw [invSeries_toFun_eq]
  simpa using h

mutual

/-- If `ms` approximates `f`, then `ms.inv` approximates `f⁻¹`. -/
noncomputable def Multiseries.inv {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) => Multiseries.mulMonomial
    (Multiseries.powser invSeries (tl.mulMonomial coef.inv (-exp))) coef.inv (-exp)

/-- If `ms` approximates `f`, then `ms.inv` approximates `f⁻¹`. -/
noncomputable def inv {basis : Basis} (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal <| ms.toReal⁻¹
  | List.cons _ _ =>
    mk (Multiseries.inv ms.seq) ms.toFun⁻¹

end

/-- If `X` and `Y` are multiseries, then `X.div Y` approximates `X / Y`. -/
noncomputable def div {basis : Basis} (X Y : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  X.mul (Y.inv)

@[simp]
theorem inv_toFun {basis : Basis} {ms : MultiseriesExpansion basis} :
    ms.inv.toFun = ms.toFun⁻¹ := by
  cases basis with
  | nil => simp [inv, toReal]; rfl
  | cons basis_hd basis_tl => simp [inv]

@[simp]
theorem inv_seq {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.inv.seq = Multiseries.inv ms.seq := by
  simp [inv]

mutual

theorem Multiseries.neg_inv_comm {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl} :
    ms.neg.inv = ms.inv.neg := by
  cases ms with
  | nil => simp [Multiseries.inv]
  | cons exp coef tl =>
    simp only [Multiseries.neg_cons, Multiseries.inv, Multiseries.destruct_cons]
    rw [neg_inv_comm, Multiseries.mulMonomial_neg_left]
    congr 3
    simp [Multiseries.mulMonomial_neg_left, Multiseries.mulMonomial_neg_right]


theorem neg_inv_comm {basis : Basis} {ms : MultiseriesExpansion basis} :
    ms.neg.inv = ms.inv.neg := by
  cases basis with
  | nil => simp [neg, inv, mulConst, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp only [ms_eq_ms_iff_mk_eq_mk, inv_seq, neg_seq, inv_toFun, neg_toFun, inv_neg, and_true]
    exact Multiseries.neg_inv_comm

end

mutual

theorem Multiseries.inv_Sorted {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl}
    (h_wo : ms.Sorted) : ms.inv.Sorted := by
  cases ms with
  | nil =>
    simp only [Multiseries.inv, Multiseries.destruct_nil]
    apply Sorted.nil
  | cons exp coef tl =>
    obtain ⟨h_coef, h_comp, h_tl⟩ := Sorted_cons h_wo
    simp only [Multiseries.inv, Multiseries.destruct_cons]
    apply Multiseries.mulMonomial_Sorted
    · apply Multiseries.powser_Sorted
      · apply Multiseries.mulMonomial_Sorted
        · apply h_tl
        · apply inv_Sorted
          exact h_coef
      · simp only [Multiseries.mulMonomial_leadingExp]
        generalize tl.leadingExp = w at *
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
    · apply inv_Sorted
      exact h_coef

theorem inv_Sorted {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_wo : ms.Sorted) : ms.inv.Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp only [Sorted_iff_Seq_Sorted, inv_seq] at *
    exact Multiseries.inv_Sorted h_wo

end

theorem tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero
    {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_wo : Sorted (mk (.cons exp coef tl) f))
    (h_approx : (mk (.cons exp coef tl) f).Approximates)
    (h_trimmed : Trimmed (mk (.cons exp coef tl) f)) :
    Tendsto ((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial
      coef.inv (-exp)).toFun atTop (𝓝 0) := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := Sorted_cons h_wo
  obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
  have := IsEquivalent_coef h_approx h_wo h_coef_trimmed h_coef_ne_zero h_basis
  obtain ⟨φ, hφ, hf⟩ := this.exists_eq_mul
  simp only [mulMonomial_toFun, mk_toFun, inv_toFun]
  have h_basis_hd_pos := basis_head_eventually_pos h_basis
  have h_coef_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 :=
    eventually_ne_zero_of_not_zero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed h_basis.tail
  apply Filter.Tendsto.congr' (f₁ := φ - 1)
  · apply (hf.and (h_basis_hd_pos.and h_coef_ne_zero)).mono
    intro t ⟨hf, h_basis_hd_pos, h_coef_ne_zero⟩
    simp only [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, hf, Pi.pow_apply, Pi.inv_apply]
    rw [Real.rpow_neg h_basis_hd_pos.le]
    field_simp
  convert hφ.sub (tendsto_const_nhds (x := 1)) using 1
  simp

-- TODO: do we need `ms.Sorted`?
theorem inv_Approximates {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) : ms.inv.Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    cases ms with
    | nil f =>
      apply Approximates_nil at h_approx
      simp only [inv, mk_seq, Multiseries.inv, Multiseries.destruct_nil, mk_toFun,
        Approximates_nil_iff]
      grw [h_approx]
      apply EventuallyEq.of_eq
      ext t
      simp
    | cons exp coef tl f =>
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := Sorted_cons h_wo
      obtain ⟨h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have h_coef_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 :=
        eventually_ne_zero_of_not_zero h_coef_ne_zero h_coef_wo h_coef h_coef_trimmed
          (h_basis.tail)
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      simp only [inv, mk_seq, Multiseries.inv, Multiseries.destruct_cons, mk_toFun]
      let ms : MultiseriesExpansion (basis_hd :: basis_tl) :=
        (((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial
          coef.inv (-exp)).powser invSeries).mulMonomial coef.inv (-exp)
      have h : ms.Approximates := by
        simp only [ms]
        apply mulMonomial_Approximates h_basis
        swap
        · apply inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
        apply powser_Approximates invSeries_convergent h_basis
        · simp only [leadingExp_def, mulMonomial_seq, mk_seq, Multiseries.mulMonomial_leadingExp]
          generalize tl.leadingExp = w at h_comp
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
        · simp only [Sorted_iff_Seq_Sorted, mulMonomial_seq, mk_seq]
          apply Multiseries.mulMonomial_Sorted h_tl_wo (inv_Sorted h_coef_wo)
        apply mulMonomial_Approximates h_basis h_tl
        apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      convert replaceFun_Approximates _ h
      have h_tendsto_zero : Tendsto ((f - basis_hd ^ exp * coef.toFun) * basis_hd ^ (-exp) *
          coef.toFun⁻¹) atTop (𝓝 0) := by
        convert (tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx
          h_trimmed).congr' _
        simp
      simp only [mulMonomial_toFun, powser_toFun, mk_toFun, inv_toFun, ms]
      set g := (f - basis_hd ^ exp * coef.toFun) * basis_hd ^ (-exp) * coef.toFun⁻¹
      apply invSeries_toFun_eq'.comp_tendsto at h_tendsto_zero
      grw [h_tendsto_zero]
      apply (h_coef_ne_zero.and h_basis_hd_pos).mono
      intro t ⟨h_coef_ne_zero, h_basis_hd_pos⟩
      simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, g]
      rw [Real.rpow_neg h_basis_hd_pos.le]
      field_simp
      congr
      ring

theorem div_Sorted {basis : Basis} {X Y : MultiseriesExpansion basis}
    (hX_wo : X.Sorted) (hY_wo : Y.Sorted) : (X.div Y).Sorted := by
  apply mul_Sorted hX_wo
  exact inv_Sorted hY_wo

theorem div_Approximates {basis : Basis} {X Y : MultiseriesExpansion basis}
    (h_basis : WellFormedBasis basis)
    (hY_wo : Y.Sorted)
    (hY_trimmed : Y.Trimmed)
    (hX_approx : X.Approximates) (hY_approx : Y.Approximates) :
    (X.div Y).Approximates := by
  apply mul_Approximates h_basis hX_approx
  exact inv_Approximates h_basis hY_wo hY_approx hY_trimmed

end MultiseriesExpansion
end Tactic.ComputeAsymptotics
