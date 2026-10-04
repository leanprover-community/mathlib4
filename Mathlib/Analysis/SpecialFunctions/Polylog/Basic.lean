/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib

/-!
# Polylog

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

public noncomputable section

open Set Filter Topology MeasureTheory

namespace Complex

variable {s z : ℂ} {t : ℝ} {n : ℕ}

theorem notMem_Ici_one_reProdIm_of_norm_lt_one (hz : ‖z‖ < 1) : z ∉ Set.Ici 1 ×ℂ {0} := by
  contrapose! hz
  exact hz.left.trans <| re_le_norm z

theorem compl_Ici_one_reProdIm_mem_nhds_of_notMem
    (hz : z ∉ Set.Ici 1 ×ℂ {0}) : (Ici 1 ×ℂ {0})ᶜ ∈ 𝓝 z :=
  ClosedIciTopology.isClosed_Ici 1 |>.reProdIm (T1Space.t1 0) |>.compl_mem_nhds hz

private abbrev mem_of_notMem := compl_Ici_one_reProdIm_mem_nhds_of_notMem (z := z)

/-- TODO: doc -/
@[pp_nodot] def polylogKernel (z : ℂ) (t : ℝ) : ℂ :=
  z / (cexp t - z)

private theorem mul_deriv_polylogKernel (ht : 0 ≤ t) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (fun z => polylogKernel z t) z = - deriv (fun t => polylogKernel z t) t := by
  have : cexp t - z ≠ 0 := by
    intro nh
    simp [← sub_eq_zero.mp nh, mem_reProdIm, exp_ofReal_re, ht.not_gt] at hz
  have : deriv ofReal t = 1 := hasDerivAt_id (t : ℂ) |>.comp_ofReal.deriv
  unfold polylogKernel
  simp (disch := first | assumption | fun_prop | simp) [this]
  ring

/-- TODO: doc -/
@[expose] def polylogIntegral (s z : ℂ) : ℂ :=
  1 / Gamma s * mellin (polylogKernel z) s

theorem mul_deriv_polylogIntegral_add_one (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (polylogIntegral (s + 1)) z = polylogIntegral s z := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  have hΓs₀ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  unfold polylogIntegral mellin
  simp only [deriv_const_mul_field', Gamma_add_one s hs₀, field, add_sub_cancel_right, smul_eq_mul]
  calc
    _ = z * (∫ t : ℝ in Ioi 0, deriv (fun z : ℂ => t ^ s * polylogKernel z t) z) := by
      congr 1
      sorry
    _ = ∫ t : ℝ in Ioi 0, t ^ s * (z * deriv (fun z : ℂ => polylogKernel z t) z) := by
      simp only [deriv_const_mul_field', ← integral_const_mul]
      ring_nf
    _ = ∫ t : ℝ in Ioi 0, t ^ s * - deriv (fun t : ℝ => polylogKernel z t) t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        congr_arg _ <| mul_deriv_polylogKernel ht.le hz
    _ = - ∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t : ℝ => polylogKernel z t) t := by
      simp [integral_neg]
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t := by
      sorry
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * (s * t ^ (s - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => congr(polylogKernel z t * $(?_))--$
      exact deriv_ofReal_cpow_const ht.ne' hs₀
    _ = ∫ t : ℝ in Ioi 0, s * t ^ (s - 1) * polylogKernel z t:=
      congr(∫ t : ℝ in Ioi 0, $(by ring))--$
    _ = s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t := by
      rw [← integral_const_mul]
      ring_nf

/-- TODO: doc -/
private def polylogAux1 : ℕ -> ℂ -> ℂ -> ℂ
  | 0 => polylogIntegral
  | n + 1 => fun s z : ℂ => z * deriv (polylogAux1 n (s + 1)) z

/-- TODO: doc -/
private def polylogAux2 (s z : ℂ) : ℂ :=
  polylogAux1 ⌊1 - s.re⌋₊ s z

open Classical in
/-- TODO: doc -/
@[irreducible, pp_nodot] def polylog (s z : ℂ) : ℂ :=
  if z ∉ Set.Ici 1 ×ℂ {0} then polylogAux2 s z else
    limUnder (𝓝[>] (0 : ℝ)) (fun y => polylogAux2 s (z.re - y * I))

private theorem polylogAux1_zero : polylogAux1 0 = polylogIntegral := rfl

private theorem polylogAux1_rec (n : ℕ) :
    polylogAux1 (n + 1) = fun s z : ℂ => z * deriv (polylogAux1 n (s + 1)) z := rfl

private theorem polylogAux2_of_re_pos (hs : 0 < s.re) : polylogAux2 s = polylogIntegral s := by
  unfold polylogAux2
  convert congrFun polylogAux1_zero s
  refine Nat.floor_eq_zero.mpr ?_
  simpa

private theorem polylog_of_notMem (hz : z ∉ Set.Ici 1 ×ℂ {0}) : polylog s z = polylogAux2 s z := by
  simp [polylog, hz]

private theorem deriv_polylog_of_notMem (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    deriv (polylog s) z = deriv (polylogAux2 s) z := by
  apply EventuallyEq.deriv_eq
  filter_upwards [mem_of_notMem hz] with z hz using polylog_of_notMem hz

-- main property theorem
-- TODO: for `s` a non-positive integers i.e. `{..., -3, -2, -1, 0}`,
-- there is no branch cut but only a pole `z = 1` and `Li_s` is a rational function
-- so we prove this under `hs : s ∈ {..., -2, -1}` and `hz : z ≠ 1`,
-- call it `mul_deriv_polylog_add_one'`?
theorem mul_deriv_polylog_add_one (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (polylog (s + 1)) z = polylog s z := by
  rw [polylog_of_notMem hz, deriv_polylog_of_notMem hz]
  unfold polylogAux2
  by_cases hs : 0 < s.re
  · rw [Nat.floor_eq_zero.mpr, Nat.floor_eq_zero.mpr]
    · simp only [polylogAux1_zero, ← mul_deriv_polylogIntegral_add_one hs hz]
    · simpa
    · grind [add_re, one_re]
  · suffices ⌊1 - s.re⌋₊ = ⌊1 - (s + 1).re⌋₊ + 1 by
      rw [this]
      rfl
    rw [← Nat.floor_add_one] <;> simp_all [neg_add_eq_sub]

/-- TODO: doc -/
def polylogSeries (s z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s

theorem mul_deriv_polylogSeries_add_one (hz : ‖z‖ < 1) :
    z * deriv (polylogSeries (s + 1)) z = polylogSeries s z := calc
  z * deriv (fun z : ℂ => ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ (s + 1)) z
    = z * ∑' n : ℕ, deriv (fun z : ℂ => z ^ (n + 1) / (n + 1) ^ (s + 1)) z := by
    congr 1
    sorry
  _ = ∑' n : ℕ, z * deriv (fun z : ℂ => z ^ (n + 1)) z / (n + 1) ^ (s + 1) := by
    simp only [deriv_div_const, ← tsum_mul_left]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := tsum_congr fun n => by
    simp [field, cpow_add (x := n + 1) _ _ (mod_cast by simp), cpow_one]
    ring

private theorem polylogKernel_eq_tsum (ht : 0 < t) (hz : ‖z‖ < 1) :
    polylogKernel z t = ∑' n : ℕ, z ^ (n + 1) * cexp (-t * (n + 1)) := by
  have : ‖z * cexp (-↑t)‖ < 1 := by
    simp only [Complex.norm_mul, norm_exp, neg_re, ofReal_re]
    grw [hz, one_mul]
    grind [Real.exp_le_one_iff]
  conv_rhs =>
    enter [1, n]
    rw [mul_comm (-t : ℂ), ← Nat.cast_add_one, ← nsmul_eq_mul, exp_nsmul, ← mul_pow, pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one this]
  simp [exp_neg, field]
  rfl

private lemma polylogIntegral_eq_polylogSeries_aux (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    ∑' n : ℕ, ∫ t : ℝ in Ioi 0, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) =
      ∫ t : ℝ in Ioi 0, ∑' n : ℕ, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by
  sorry

-- main auxiliary theorem
/-- TODO: doc -/
theorem polylogIntegral_eq_polylogSeries (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylogIntegral s z = polylogSeries s z := calc
  1 / Gamma s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t
    = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      t ^ (s - 1) * (z ^ (n + 1) * cexp (-t * (n + 1))) := by
    refine congr(1 / Gamma s * $(setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_))--$
    rw [tsum_mul_left, polylogKernel_eq_tsum ht hz]
  _ = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by ac_rfl
  _ = 1 / Gamma s * ∑' n : ℕ, ∫ t : ℝ in Ioi 0,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) :=
    congrArg _ <| polylogIntegral_eq_polylogSeries_aux hs hz |>.symm
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * ∫ t : ℝ in Ioi 0,
      t ^ (s - 1) * cexp (-t * (n + 1)) := by
    simp_rw [← tsum_mul_left, ← integral_const_mul]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * (Gamma s / (n + 1) ^ s) := tsum_congr fun n => by
    congr 1
    have hn : (0 : ℝ) < n + 1 := mod_cast Nat.zero_lt_succ n
    simpa [field, arg_eq_pi_iff, hn.not_gt, mul_comm, inv_cpow_eq_ite] using
      integral_cpow_mul_exp_neg_mul_Ioi hs hn
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := by
    field_simp [Gamma_ne_zero_of_re_pos hs]

private theorem polylog_eq_tsum_add_one_aux (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylog s z = polylogSeries s z := by
  rw [polylog_of_notMem <| notMem_Ici_one_reProdIm_of_norm_lt_one hz,
    polylogAux2_of_re_pos hs, polylogIntegral_eq_polylogSeries hs hz]

-- main theorem
/-- TODO: doc -/
theorem polylog_eq_polylogIntegral (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    polylog s z = polylogIntegral s z := by
  rw [polylog_of_notMem hz, polylogAux2_of_re_pos hs]

-- main theorem
/-- TODO: doc -/
theorem polylog_eq_tsum_add_one (hz : ‖z‖ < 1) :
    polylog s z = polylogSeries s z := by
  revert z
  suffices ∀ z, ‖z‖ < 1 -> polylog (s + ⌊1 - s.re⌋₊) z = polylogSeries (s + ⌊1 - s.re⌋₊) z by
    generalize ⌊1 - s.re⌋₊ = n at *
    induction n with
    | zero => simpa
    | succ n ih =>
      refine fun _ _ => ih (fun z hz => ?_) ‹_›
      rw [← mul_deriv_polylogSeries_add_one hz,
        ← mul_deriv_polylog_add_one <| notMem_Ici_one_reProdIm_of_norm_lt_one hz]
      refine congr(z * $(EventuallyEq.deriv_eq ?_))
      filter_upwards [IsOpen.mem_nhds (Metric.isOpen_ball (x := 0)) (by simpa)] with z hz
      simpa [add_assoc] using this z (by simpa using hz)
  refine fun z hz => polylog_eq_tsum_add_one_aux ?_ hz
  simp only [add_re, natCast_re]
  rcases le_total 0 (1 - s.re) with (_ | _) <;> grind [Nat.lt_floor_add_one (1 - s.re)]

/-- TODO: doc -/
theorem polylog_eq_tsum_pnat (hz : ‖z‖ < 1) :
    polylog s z = ∑' n : ℕ+, z ^ n.val / n ^ s := by
  simp [polylog_eq_tsum_add_one hz, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => z ^ n / n ^ s)]
  rfl

theorem hasSum_polylog (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s) (polylog s z) := by
  refine Summable.hasSum_iff ?_ |>.mpr <| polylog_eq_tsum_add_one hz |>.symm
  obtain ⟨k, hk⟩ := exists_nat_ge (-s.re)
  have hg : Summable fun n : ℕ => (n + 1 : ℕ) ^ k * ‖z‖ ^ (n + 1) :=
    summable_nat_add_iff (f := fun n => n ^ k * ‖z‖ ^ n) 1 |>.mpr <|
      summable_pow_mul_geometric_of_norm_lt_one k (by simpa)
  refine Summable.of_norm_bounded hg fun n => ?_
  rw [norm_div, norm_pow, ← Nat.cast_add_one, Complex.norm_natCast_cpow_of_pos n.add_one_pos,
    div_eq_mul_inv, mul_comm, ← Real.rpow_neg (mod_cast Nat.zero_le _)]
  grw [Real.rpow_le_rpow_of_exponent_le (mod_cast n.succ_pos) hk, Real.rpow_natCast]

end Complex

#lint
