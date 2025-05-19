/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Various complex special functions are analytic

`log`, and `cpow` are analytic, since they are differentiable.
-/

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

/-- The function `Real.cos` is real analytic. -/
@[fun_prop]
lemma analyticAt_cos : AnalyticAt ℝ Real.cos x :=
  Real.contDiff_cos.contDiffAt.analyticAt

/-- The function `Real.cos` is real analytic. -/
lemma analyticWithinAt_cos :  AnalyticWithinAt ℝ Real.cos s x :=
  Real.contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cos` is real analytic. -/
theorem analyticOnNhd_cos : AnalyticOnNhd ℝ Real.cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Real.cos` is real analytic. -/
lemma analyticOn_cos :  AnalyticOn ℝ Real.cos s :=
  Real.contDiff_cos.contDiffOn.analyticOn

/-- The function `Real.cosh` is real analytic. -/
@[fun_prop]
lemma analyticAt_cosh : AnalyticAt ℝ Real.cosh x :=
  Real.contDiff_cosh.contDiffAt.analyticAt

/-- The function `Real.cosh` is real analytic. -/
lemma analyticWithinAt_cosh :  AnalyticWithinAt ℝ Real.cosh s x :=
  Real.contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cosh` is real analytic. -/
theorem analyticOnNhd_cosh : AnalyticOnNhd ℝ Real.cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Real.cosh` is real analytic. -/
lemma analyticOn_cosh :  AnalyticOn ℝ Real.cosh s :=
  Real.contDiff_cosh.contDiffOn.analyticOn

/-- The function `Real.sin` is real analytic. -/
@[fun_prop]
lemma analyticAt_sin : AnalyticAt ℝ Real.sin x :=
  Real.contDiff_sin.contDiffAt.analyticAt

/-- The function `Real.sin` is real analytic. -/
lemma analyticWithinAt_sin :  AnalyticWithinAt ℝ Real.sin s x :=
  Real.contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sin` is real analytic. -/
theorem analyticOnNhd_sin : AnalyticOnNhd ℝ Real.sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Real.sin` is real analytic. -/
lemma analyticOn_sin :  AnalyticOn ℝ Real.sin s :=
  Real.contDiff_sin.contDiffOn.analyticOn

/-- The function `Real.sinh` is real analytic. -/
@[fun_prop]
lemma analyticAt_sinh : AnalyticAt ℝ Real.sinh x :=
  Real.contDiff_sinh.contDiffAt.analyticAt

/-- The function `Real.sinh` is real analytic. -/
lemma analyticWithinAt_sinh :  AnalyticWithinAt ℝ Real.sinh s x :=
  Real.contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sinh` is real analytic. -/
theorem analyticOnNhd_sinh : AnalyticOnNhd ℝ Real.sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Real.sinh` is real analytic. -/
lemma analyticOn_sinh :  AnalyticOn ℝ Real.sinh s :=
  Real.contDiff_sinh.contDiffOn.analyticOn

/-- The function `Real.exp` is real analytic. -/
@[fun_prop]
lemma analyticAt_exp : AnalyticAt ℝ Real.exp x :=
  Real.contDiff_exp.contDiffAt.analyticAt

/-- The function `Real.exp` is real analytic. -/
lemma analyticWithinAt_exp :  AnalyticWithinAt ℝ Real.exp s x :=
  Real.contDiff_exp.contDiffWithinAt.analyticWithinAt

/-- The function `Real.exp` is real analytic. -/
theorem analyticOnNhd_exp : AnalyticOnNhd ℝ Real.exp s :=
  fun _ _ ↦ analyticAt_exp

/-- The function `Real.exp` is real analytic. -/
lemma analyticOn_exp :  AnalyticOn ℝ Real.exp s :=
  Real.contDiff_exp.contDiffOn.analyticOn

end Real

namespace Complex

variable {s : Set ℂ} {x : ℂ}

/-- The function `Complex.cos` is complex analytic. -/
@[fun_prop]
lemma analyticAt_cos : AnalyticAt ℂ Complex.cos x :=
  Complex.contDiff_cos.contDiffAt.analyticAt

/-- The function `Complex.cos` is complex analytic. -/
lemma analyticWithinAt_cos :  AnalyticWithinAt ℂ Complex.cos s x :=
  Complex.contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cos` is complex analytic. -/
theorem analyticOnNhd_cos : AnalyticOnNhd ℂ Complex.cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Complex.cos` is complex analytic. -/
lemma analyticOn_cos :  AnalyticOn ℂ Complex.cos s :=
  Complex.contDiff_cos.contDiffOn.analyticOn

/-- The function `Complex.cosh` is complex analytic. -/
@[fun_prop]
lemma analyticAt_cosh : AnalyticAt ℂ Complex.cosh x :=
  Complex.contDiff_cosh.contDiffAt.analyticAt

/-- The function `Complex.cosh` is complex analytic. -/
lemma analyticWithinAt_cosh :  AnalyticWithinAt ℂ Complex.cosh s x :=
  Complex.contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cosh` is complex analytic. -/
theorem analyticOnNhd_cosh : AnalyticOnNhd ℂ Complex.cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Complex.cosh` is complex analytic. -/
lemma analyticOn_cosh :  AnalyticOn ℂ Complex.cosh s :=
  Complex.contDiff_cosh.contDiffOn.analyticOn

/-- The function `Complex.sin` is complex analytic. -/
@[fun_prop]
lemma analyticAt_sin : AnalyticAt ℂ Complex.sin x :=
  Complex.contDiff_sin.contDiffAt.analyticAt

/-- The function `Complex.sin` is complex analytic. -/
lemma analyticWithinAt_sin :  AnalyticWithinAt ℂ Complex.sin s x :=
  Complex.contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sin` is complex analytic. -/
theorem analyticOnNhd_sin : AnalyticOnNhd ℂ Complex.sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Complex.sin` is complex analytic. -/
lemma analyticOn_sin :  AnalyticOn ℂ Complex.sin s :=
  Complex.contDiff_sin.contDiffOn.analyticOn

/-- The function `Complex.sinh` is complex analytic. -/
@[fun_prop]
lemma analyticAt_sinh : AnalyticAt ℂ Complex.sinh x :=
  Complex.contDiff_sinh.contDiffAt.analyticAt

/-- The function `Complex.sinh` is complex analytic. -/
lemma analyticWithinAt_sinh :  AnalyticWithinAt ℂ Complex.sinh s x :=
  Complex.contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sinh` is complex analytic. -/
theorem analyticOnNhd_sinh : AnalyticOnNhd ℂ Complex.sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Complex.sinh` is complex analytic. -/
lemma analyticOn_sinh :  AnalyticOn ℂ Complex.sinh s :=
  Complex.contDiff_sinh.contDiffOn.analyticOn

/-- The function `Complex.exp` is complex analytic. -/
@[fun_prop]
lemma analyticAt_exp : AnalyticAt ℂ Complex.exp x :=
  Complex.contDiff_exp.contDiffAt.analyticAt

/-- The function `Complex.exp` is complex analytic. -/
lemma analyticWithinAt_exp :  AnalyticWithinAt ℂ Complex.exp s x :=
  Complex.contDiff_exp.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.exp` is complex analytic. -/
theorem analyticOnNhd_exp : AnalyticOnNhd ℂ Complex.exp s :=
  fun _ _ ↦ analyticAt_exp

/-- The function `Complex.exp` is complex analytic. -/
lemma analyticOn_exp :  AnalyticOn ℂ Complex.exp s :=
  Complex.contDiff_exp.contDiffOn.analyticOn

end Complex
