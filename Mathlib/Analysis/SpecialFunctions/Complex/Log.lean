/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/

@[expose] public section

noncomputable section

namespace Complex

open Set Filter Bornology

open scoped Real Topology ComplexConjugate

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0` -/
@[pp_nodot]
noncomputable def log (x : ℂ) : ℂ :=
  Real.log ‖x‖ + arg x * I

theorem log_re (x : ℂ) : x.log.re = Real.log ‖x‖ := by simp [log]

theorem log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]

theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]

theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
  rw [log, exp_add_mul_I, ← ofReal_sin, sin_arg, ← ofReal_cos, cos_arg hx, ← ofReal_exp,
    Real.exp_log (norm_pos_iff.mpr hx), mul_add, ofReal_div, ofReal_div,
    mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx), ← mul_assoc,
    mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx), re_add_im]

@[simp]
theorem range_exp : Set.range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩

theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x := by
  rw [log, norm_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← ofReal_exp,
    arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]

theorem log_exp_eq_re_add_toIocMod (x : ℂ) :
    log (exp x) = x.re + (toIocMod Real.two_pi_pos (-π) x.im) * I := by
  rw [log, norm_exp, Real.log_exp, arg_exp]

theorem log_exp_eq_sub_toIocDiv (x : ℂ) :
    log (exp x) = x - (toIocDiv Real.two_pi_pos (-π) x.im) * (2 * π * I) := by
  rw [log_exp_eq_re_add_toIocMod, toIocMod, ofReal_sub, sub_mul, ← add_sub_assoc]
  simp [mul_assoc]

theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im)
    (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]

theorem ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])

@[simp, norm_cast]
lemma natCast_log {n : ℕ} : Real.log n = log n := ofReal_natCast n ▸ ofReal_log n.cast_nonneg

@[simp]
lemma ofNat_log {n : ℕ} [n.AtLeastTwo] :
    Real.log ofNat(n) = log (OfNat.ofNat n) :=
  natCast_log

theorem log_ofReal_re (x : ℝ) : (log (x : ℂ)).re = Real.log x := by simp [log_re]

theorem log_ofReal_mul {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) :
    log (r * x) = Real.log r + log x := by
  replace hx := norm_ne_zero_iff.mpr hx
  simp_rw [log, norm_mul, norm_real, arg_real_mul _ hr, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' hx, ofReal_add, add_assoc]

theorem log_mul_ofReal (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
    log (x * r) = Real.log r + log x := by rw [mul_comm, log_ofReal_mul hr hx]

lemma log_mul_eq_add_log_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    log (x * y) = log x + log y ↔ arg x + arg y ∈ Set.Ioc (-π) π := by
  refine Complex.ext_iff.trans <| Iff.trans ?_ <| arg_mul_eq_add_arg_iff hx₀ hy₀
  simp_rw [add_re, add_im, log_re, log_im, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

alias ⟨_, log_mul⟩ := log_mul_eq_add_log_iff

@[simp]
theorem log_zero : log 0 = 0 := by simp [log]

@[simp]
theorem log_one : log 1 = 0 := by simp [log]

/-- This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `log 0 = 0`. -/
@[simp] lemma log_div_self (x : ℂ) : log (x / x) = 0 := by simp [log]

theorem log_neg_one : log (-1) = π * I := by simp [log]

theorem log_I : log I = π / 2 * I := by simp [log]

theorem log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

theorem log_conj_eq_ite (x : ℂ) : log (conj x) = if x.arg = π then log x else conj (log x) := by
  simp_rw [log, norm_conj, arg_conj, map_add, map_mul, conj_ofReal]
  split_ifs with hx
  · rw [hx]
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]

theorem log_conj (x : ℂ) (h : x.arg ≠ π) : log (conj x) = conj (log x) := by
  rw [log_conj_eq_ite, if_neg h]

theorem log_inv_eq_ite (x : ℂ) : log x⁻¹ = if x.arg = π then -conj (log x) else -log x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def, log_mul_ofReal, Real.log_inv, ofReal_neg, ← sub_eq_neg_add, log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_norm_sq, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_neg]
    norm_num
    grind
  · rwa [inv_pos, Complex.normSq_pos]
  · rwa [map_ne_zero]

theorem log_inv (x : ℂ) (hx : x.arg ≠ π) : log x⁻¹ = -log x := by rw [log_inv_eq_ite, if_neg hx]

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I) := by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im ∈ Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one]
  · rintro ⟨n, rfl⟩
    exact (exp_periodic.int_mul n).eq.trans exp_zero

theorem exp_eq_one_iff_of_im_nonneg {x : ℂ} (hx : 0 ≤ x.im) :
    exp x = 1 ↔ ∃ n : ℕ, x = n * (2 * π * I) := by
  rw [exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨n, by rw [hn]; norm_cast⟩⟩
  have : 0 ≤ n * (2 * π) := by simpa [hn] using hx
  lift n to ℕ using by exact_mod_cast nonneg_of_mul_nonneg_left this (by positivity)
  exact ⟨n, hn⟩

theorem exp_two_pi_mul_I_mul_div_eq_one_iff {k N : ℕ} (hN : N ≠ 0) :
    exp (2 * π * I * k / N) = 1 ↔ N ∣ k := by
  rw [exp_eq_one_iff]
  conv in _ = _ => rw [← mul_comm (2 * π * I), mul_div_assoc, mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast
  simp [← dvd_def, Int.ofNat_dvd]

theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[grind .] lemma re_eq_re_of_cexp_eq_cexp {x y : ℂ} (h : cexp x = cexp y) :
    x.re = y.re := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]

theorem log_exp_exists (z : ℂ) :
    ∃ n : ℤ, log (exp z) = z + n * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_log]
  exact exp_ne_zero z

@[simp]
theorem countable_preimage_exp {s : Set ℂ} : (exp ⁻¹' s).Countable ↔ s.Countable := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine ((hs.image exp).insert 0).mono ?_
    rw [Set.image_preimage_eq_inter_range, range_exp, ← Set.diff_eq, ← Set.union_singleton,
        Set.diff_union_self]
    exact Set.subset_union_left
  · rw [← Set.biUnion_preimage_singleton]
    refine hs.biUnion fun z hz => ?_
    by_cases! h : ∃ w, exp w = z
    · rcases h with ⟨w, rfl⟩
      simp only [Set.preimage, Set.mem_singleton_iff, exp_eq_exp_iff_exists_int, Set.setOf_exists]
      exact Set.countable_iUnion fun m => Set.countable_singleton _
    · simp [Set.preimage, h]

alias ⟨_, _root_.Set.Countable.preimage_cexp⟩ := countable_preimage_exp

theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 <| Real.log ‖z‖ - π * I) := by
  convert
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
            (continuous_norm.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  · simp [sub_eq_add_neg]
  · lift z to ℝ using him
    simpa using hre.ne

theorem continuousWithinAt_log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : ℂ | 0 ≤ z.im } z := by
  convert
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
            (continuous_norm.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  lift z to ℝ using him
  simpa using hre.ne

theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 <| Real.log ‖z‖ + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto

@[simp]
theorem map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[≠] 0 := by
  rw [← comap_exp_nhds_zero, map_comap, range_exp, nhdsWithin]

@[simp]
theorem map_exp_comap_re_atTop : map exp (comap re atTop) = cobounded ℂ := by
  rw [← comap_exp_cobounded, map_comap, range_exp, inf_eq_left, le_principal_iff]
  exact eventually_ne_cobounded _

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type*}

theorem continuousAt_clog {x : ℂ} (h : x ∈ slitPlane) : ContinuousAt log x := by
  refine ContinuousAt.add ?_ ?_
  · refine continuous_ofReal.continuousAt.comp ?_
    refine (Real.continuousAt_log ?_).comp continuous_norm.continuousAt
    exact norm_ne_zero_iff.mpr <| slitPlane_ne_zero h
  · have h_cont_mul : Continuous fun x : ℂ => x * I := by fun_prop
    refine h_cont_mul.continuousAt.comp (continuous_ofReal.continuousAt.comp ?_)
    exact continuousAt_arg h

theorem _root_.Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : x ∈ slitPlane) : Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuousAt_clog hx).tendsto.comp h

variable [TopologicalSpace α]

nonrec
theorem _root_.ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : f x ∈ slitPlane) : ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂

nonrec
theorem _root_.ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ slitPlane) :
    ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂

nonrec
theorem _root_.ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, f x ∈ slitPlane) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

nonrec
theorem _root_.Continuous.clog {f : α → ℂ} (h₁ : Continuous f)
    (h₂ : ∀ x, f x ∈ slitPlane) : Continuous fun t => log (f t) :=
  continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)

end LogDeriv

namespace Complex

open Set
open scoped Real

/-- `Complex.exp` as an `OpenPartialHomeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}` (a.k.a. `slitPlane`).
This definition is used to prove that `Complex.log`
is complex differentiable at all points but the negative real semi-axis.
-/
noncomputable def expOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
  toFun := exp
  invFun := log
  source := {z : ℂ | z.im ∈ Ioo (-π) π}
  target := slitPlane
  map_source' := by
    rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
    simp [exp_mem_slitPlane, h₂.ne,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h₁, by simpa [two_mul] using h₂.le⟩]
  map_target' z h := by
    simp only [mem_setOf, log_im, mem_Ioo, neg_pi_lt_arg, arg_lt_pi_iff, true_and]
    exact h.imp_left le_of_lt
  left_inv' _x hx := log_exp hx.1 (le_of_lt hx.2)
  right_inv' _x hx := exp_log <| slitPlane_ne_zero hx
  open_source := isOpen_Ioo.preimage continuous_im
  open_target := isOpen_slitPlane
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_id.clog fun _ ↦ id

@[deprecated (since := "2026-01-13")]
alias expPartialHomeomorph := expOpenPartialHomeomorph

end Complex
