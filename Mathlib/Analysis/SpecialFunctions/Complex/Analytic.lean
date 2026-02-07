/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

public import Mathlib.Tactic.MoveAdd

/-!
# Various complex special functions are analytic

`log`, and `cpow` are analytic, since they are differentiable.
-/

public section

open Complex Set
open scoped Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
theorem analyticAt_clog (m : z ∈ slitPlane) : AnalyticAt ℂ log z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
theorem AnalyticAt.clog (fa : AnalyticAt ℂ f x) (m : f x ∈ slitPlane) :
    AnalyticAt ℂ (fun z ↦ log (f z)) x :=
  (analyticAt_clog m).comp fa

theorem AnalyticWithinAt.clog (fa : AnalyticWithinAt ℂ f s x) (m : f x ∈ slitPlane) :
    AnalyticWithinAt ℂ (fun z ↦ log (f z)) s x :=
  (analyticAt_clog m).comp_analyticWithinAt fa

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticOnNhd.clog (fs : AnalyticOnNhd ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).comp (fs z n)

theorem AnalyticOn.clog (fs : AnalyticOn ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOn ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
theorem AnalyticWithinAt.cpow (fa : AnalyticWithinAt ℂ f s x) (ga : AnalyticWithinAt ℂ g s x)
    (m : f x ∈ slitPlane) : AnalyticWithinAt ℂ (fun z ↦ f z ^ g z) s x := by
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z ↦ exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact ((fa.clog m).mul ga).cexp

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
@[fun_prop]
theorem AnalyticAt.cpow (fa : AnalyticAt ℂ f x) (ga : AnalyticAt ℂ g x)
    (m : f x ∈ slitPlane) : AnalyticAt ℂ (fun z ↦ f z ^ g z) x := by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
theorem AnalyticOn.cpow (fs : AnalyticOn ℂ f s) (gs : AnalyticOn ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOn ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
theorem AnalyticOnNhd.cpow (fs : AnalyticOnNhd ℂ f s) (gs : AnalyticOnNhd ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOnNhd ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

section ReOfReal

variable {f : ℂ → ℂ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
lemma AnalyticAt.re_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]
lemma AnalyticAt.im_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).im) x :=
  (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

lemma AnalyticWithinAt.re_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).re) s x :=
  ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

lemma AnalyticWithinAt.im_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).im) s x :=
  ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

lemma AnalyticOn.re_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

lemma AnalyticOn.im_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

lemma AnalyticOnNhd.re_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

lemma AnalyticOnNhd.im_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

end ReOfReal

section Real

variable {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
lemma analyticAt_log (hx : 0 < x) : AnalyticAt ℝ Real.log x := by
  have : Real.log = fun x : ℝ ↦ (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
  refine AnalyticAt.re_ofReal <| analyticAt_clog ?_
  simp [hx]

lemma analyticOnNhd_log : AnalyticOnNhd ℝ Real.log (Set.Ioi 0) := fun _ hx ↦ analyticAt_log hx

lemma analyticOn_log : AnalyticOn ℝ Real.log (Set.Ioi 0) := analyticOnNhd_log.analyticOn

@[fun_prop]
lemma AnalyticAt.log (fa : AnalyticAt ℝ f x) (m : 0 < f x) :
    AnalyticAt ℝ (fun z ↦ Real.log (f z)) x :=
  (analyticAt_log m).comp fa

lemma AnalyticWithinAt.log (fa : AnalyticWithinAt ℝ f s x) (m : 0 < f x) :
    AnalyticWithinAt ℝ (fun z ↦ Real.log (f z)) s x :=
  (analyticAt_log m).comp_analyticWithinAt fa

lemma AnalyticOnNhd.log (fs : AnalyticOnNhd ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOnNhd ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).comp (fs z n)

lemma AnalyticOn.log (fs : AnalyticOn ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOn ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m

-- TODO: refactor
theorem hasFPowerSeriesAt_log : HasFPowerSeriesAt (fun t ↦ Real.log (1 + t))
    (.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) 0 := by
  suffices HasFPowerSeriesAt Real.log (.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) 1 by
    rw [show (0 : ℝ) = 1 + (-1) by simp]
    conv => arg 1; ext t; rw [show 1 + t = t - (-1) by ring]
    exact HasFPowerSeriesAt.comp_sub this _
  suffices ((FormalMultilinearSeries.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) =
      FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ iteratedDeriv n Real.log 1 / (n.factorial : ℝ))) by
    convert AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analyticAt_log (by simp)
  ext n
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  obtain _ | n := n
  · simp
  rw [Nat.factorial_succ, pow_succ]
  field_simp
  push_cast
  move_mul [((n : ℝ) + 1)]
  simp only [mul_eq_mul_right_iff]
  left
  suffices iteratedDeriv (n + 1) Real.log =
      fun (x : ℝ) ↦ (-1 : ℝ) ^ n * n.factorial * x ^ (-(n : ℤ) - 1) by
    rw [this]
    simp
  induction n with
  | zero =>
    simp only [zero_add, iteratedDeriv_one, Real.deriv_log', pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, CharP.cast_eq_zero, neg_zero, zero_sub, Int.reduceNeg, zpow_neg,
      zpow_one, one_mul]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg]
    rw [iteratedDeriv_succ, ih]
    ext x
    simp only [deriv_const_mul_field', deriv_zpow', Int.cast_sub,
      Int.cast_neg, Int.cast_natCast, Int.cast_one, pow_succ, mul_neg, mul_one, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, neg_mul, Int.reduceNeg]
    ring_nf

end Real
