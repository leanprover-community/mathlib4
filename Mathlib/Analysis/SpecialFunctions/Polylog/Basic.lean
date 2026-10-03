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

open scoped ComplexConjugate LSeries.notation

namespace Complex

variable {s z : ℂ} {t : ℝ}

theorem notMem_Ici_one_reProdIm_of_norm_lt_one (hz : ‖z‖ < 1) : z ∉ Set.Ici 1 ×ℂ {0} := by
  contrapose! hz
  obtain ⟨hzre, hzim⟩ : 1 ≤ z.re ∧ z.im = 0 := hz
  simp only [← one_le_normSq_iff, normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  nlinarith

/-- TODO: doc -/
def polylogKernel (z : ℂ) (t : ℝ) : ℂ :=
  z / (cexp t - z)

theorem mul_deriv_polylogKernel :
    z * deriv (fun z => polylogKernel z t) z = - deriv (fun t => polylogKernel z t) t := by
  sorry

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
    z * deriv (fun z : ℂ => ∫ t : ℝ in Ioi 0, t ^ s * polylogKernel z t) z
      = z * (∫ t : ℝ in Ioi 0, deriv (fun z : ℂ => t ^ s * polylogKernel z t) z) := by
        congr 1
        sorry
    _ = ∫ t : ℝ in Ioi 0, t ^ s * (z * deriv (fun z : ℂ => polylogKernel z t) z) := by
        simp only [deriv_const_mul_field', ← integral_const_mul]
        ring_nf
    _ = ∫ t : ℝ in Ioi 0, t ^ s * - deriv (fun t : ℝ => polylogKernel z t) t :=
        congr(∫ t : ℝ in Ioi 0, t ^ s * $(mul_deriv_polylogKernel))--$
    _ = - ∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t : ℝ => polylogKernel z t) t := by
        simp [integral_neg]
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t := by
        sorry
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * (s * t ^ (s - 1)) := by
        congr; ext t; congr
        sorry
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

private theorem polylogAux2_of_re_pos (hs : 0 < s.re) : polylogAux2 s = polylogIntegral s := by
  unfold polylogAux2
  convert congrFun polylogAux1_zero s
  refine Nat.floor_eq_zero.mpr ?_
  simpa

private theorem polylog_of_notMem (hz : z ∉ Set.Ici 1 ×ℂ {0}) : polylog s z = polylogAux2 s z := by
  simp [polylog, hz]

-- main property theorem
-- TODO: for `s` a non-positive integers i.e. `{..., -3, -2, -1, 0}`,
-- there is no branch cut but only a pole `z = 1` and `Li_s` is a rational function
-- so we prove this under `hs : s ∈ {..., -2, -1}` and `hz : z ≠ 1`,
-- call it `mul_deriv_polylog_add_one'`?
theorem mul_deriv_polylog_add_one (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (polylog (s + 1)) z = polylog s z := by
  sorry

/-- TODO: doc -/
def polylogSeries (s z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s

theorem mul_deriv_polylogSeries_add_one (hz : ‖z‖ < 1) :
    z * deriv (polylogSeries (s + 1)) z = polylogSeries s z := by
  sorry

-- main auxiliary theorem
/-- TODO: doc -/
theorem polylogIntegral_eq_polylogSeries (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylogIntegral s z = polylogSeries s z := by
  sorry

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
  simp
  sorry

/-- TODO: doc -/
theorem polylog_eq_tsum_pnat (hz : ‖z‖ < 1) :
    polylog s z = ∑' n : ℕ+, z ^ n.val / n ^ s := by
  simp [polylog_eq_tsum_add_one hz, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => z ^ n / n ^ s)]
  rfl

end Complex

#lint
