/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `Real.arsinh`: The inverse function of `Real.sinh`.

- `Real.sinhEquiv`, `Real.sinhOrderIso`, `Real.sinhHomeomorph`: `Real.sinh` as an `Equiv`,
  `OrderIso`, and `Homeomorph`, respectively.

## Main Results

- `Real.sinh_surjective`, `Real.sinh_bijective`: `Real.sinh` is surjective and bijective;

- `Real.arsinh_injective`, `Real.arsinh_surjective`, `Real.arsinh_bijective`: `Real.arsinh` is
  injective, surjective, and bijective;

- `Real.continuous_arsinh`, `Real.differentiable_arsinh`, `Real.contDiff_arsinh`: `Real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `Filter.Tendsto.arsinh` and `ContDiffAt.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/

@[expose] public section

noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + √(1 + x^2))`. -/
@[informal "inverse hyperbolic trigonometric functions", pp_nodot]
def arsinh (x : ℝ) :=
  log (x + √(1 + x ^ 2))

theorem exp_arsinh (x : ℝ) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

@[simp]
theorem arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

@[simp]
theorem arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x := by
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq, neg_add_eq_sub, add_comm x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp]
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := by
  rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq]; simp

@[simp]
theorem cosh_arsinh (x : ℝ) : cosh (arsinh x) = √(1 + x ^ 2) := by
  rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

@[simp]
theorem tanh_arsinh (x : ℝ) : tanh (arsinh x) = x / √(1 + x ^ 2) := by
  rw [tanh_eq_sinh_div_cosh, sinh_arsinh, cosh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
theorem sinh_surjective : Surjective sinh :=
  LeftInverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
theorem sinh_bijective : Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp]
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

/-- `Real.sinh` as an `Equiv`. -/
@[simps]
def sinhEquiv : ℝ ≃ ℝ where
  toFun := sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

/-- `Real.sinh` as an `OrderIso`. -/
@[simps! -fullyApplied]
def sinhOrderIso : ℝ ≃o ℝ where
  toEquiv := sinhEquiv
  map_rel_iff' := @sinh_le_sinh

/-- `Real.sinh` as a `Homeomorph`. -/
@[simps! -fullyApplied]
def sinhHomeomorph : ℝ ≃ₜ ℝ :=
  sinhOrderIso.toHomeomorph

theorem arsinh_bijective : Bijective arsinh :=
  sinhEquiv.symm.bijective

theorem arsinh_injective : Injective arsinh :=
  sinhEquiv.symm.injective

theorem arsinh_surjective : Surjective arsinh :=
  sinhEquiv.symm.surjective

theorem arsinh_strictMono : StrictMono arsinh :=
  sinhOrderIso.symm.strictMono

@[simp]
theorem arsinh_inj : arsinh x = arsinh y ↔ x = y :=
  arsinh_injective.eq_iff

@[simp, gcongr]
theorem arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y :=
  sinhOrderIso.symm.le_iff_le

@[simp]
theorem arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y :=
  sinhOrderIso.symm.lt_iff_lt

@[simp]
theorem arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
  arsinh_injective.eq_iff' arsinh_zero

@[simp]
theorem arsinh_nonneg_iff : 0 ≤ arsinh x ↔ 0 ≤ x := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
theorem arsinh_nonpos_iff : arsinh x ≤ 0 ↔ x ≤ 0 := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]
theorem arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

theorem hasStrictDerivAt_arsinh (x : ℝ) : HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x := by
  convert sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
    (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm

theorem hasDerivAt_arsinh (x : ℝ) : HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x :=
  (hasStrictDerivAt_arsinh x).hasDerivAt

@[fun_prop]
theorem differentiable_arsinh : Differentiable ℝ arsinh := fun x =>
  (hasDerivAt_arsinh x).differentiableAt

@[fun_prop]
theorem contDiff_arsinh {n : WithTop ℕ∞} : ContDiff ℝ n arsinh :=
  sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

@[continuity]
theorem continuous_arsinh : Continuous arsinh :=
  sinhHomeomorph.symm.continuous

/-- The function `Real.arsinh` is real analytic. -/
@[fun_prop]
lemma analyticAt_arsinh : AnalyticAt ℝ arsinh x :=
  contDiff_arsinh.contDiffAt.analyticAt

/-- The function `Real.arsinh` is real analytic. -/
lemma analyticWithinAt_arsinh {s : Set ℝ} : AnalyticWithinAt ℝ arsinh s x :=
  contDiff_arsinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.arsinh` is real analytic. -/
theorem analyticOnNhd_arsinh {s : Set ℝ} : AnalyticOnNhd ℝ arsinh s :=
  fun _ _ ↦ analyticAt_arsinh

/-- The function `Real.arsinh` is real analytic. -/
lemma analyticOn_arsinh {s : Set ℝ} : AnalyticOn ℝ arsinh s :=
  contDiff_arsinh.contDiffOn.analyticOn

end Real

open Real

theorem Filter.Tendsto.arsinh {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a)) :=
  (continuous_arsinh.tendsto _).comp h

section Continuous

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {a : X}

nonrec theorem ContinuousAt.arsinh (h : ContinuousAt f a) :
    ContinuousAt (fun x => arsinh (f x)) a :=
  h.arsinh

nonrec theorem ContinuousWithinAt.arsinh (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => arsinh (f x)) s a :=
  h.arsinh

theorem ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

theorem Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x) :=
  continuous_arsinh.comp h

end Continuous

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {a : E}
  {f' : StrongDual ℝ E} {n : ℕ∞}

theorem HasStrictFDerivAt.arsinh (hf : HasStrictFDerivAt f f' a) :
    HasStrictFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf

theorem HasFDerivAt.arsinh (hf : HasFDerivAt f f' a) :
    HasFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp_hasFDerivAt a hf

theorem HasFDerivWithinAt.arsinh (hf : HasFDerivWithinAt f f' s a) :
    HasFDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

@[fun_prop]
theorem DifferentiableAt.arsinh (h : DifferentiableAt ℝ f a) :
    DifferentiableAt ℝ (fun x => arsinh (f x)) a :=
  (differentiable_arsinh _).comp a h

@[fun_prop]
theorem DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt ℝ f s a) :
    DifferentiableWithinAt ℝ (fun x => arsinh (f x)) s a :=
  (differentiable_arsinh _).comp_differentiableWithinAt a h

@[fun_prop]
theorem DifferentiableOn.arsinh (h : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => arsinh (f x)) s := fun x hx => (h x hx).arsinh

@[fun_prop]
theorem Differentiable.arsinh (h : Differentiable ℝ f) : Differentiable ℝ fun x => arsinh (f x) :=
  differentiable_arsinh.comp h

@[fun_prop]
theorem ContDiffAt.arsinh (h : ContDiffAt ℝ n f a) : ContDiffAt ℝ n (fun x => arsinh (f x)) a :=
  contDiff_arsinh.contDiffAt.comp a h

@[fun_prop]
theorem ContDiffWithinAt.arsinh (h : ContDiffWithinAt ℝ n f s a) :
    ContDiffWithinAt ℝ n (fun x => arsinh (f x)) s a :=
  contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

@[fun_prop]
theorem ContDiff.arsinh (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arsinh (f x) :=
  contDiff_arsinh.comp h

@[fun_prop]
theorem ContDiffOn.arsinh (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

end fderiv

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {a f' : ℝ}

theorem HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) :
    HasStrictDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp a hf

theorem HasDerivAt.arsinh (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp a hf

theorem HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) :
    HasDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

end deriv
