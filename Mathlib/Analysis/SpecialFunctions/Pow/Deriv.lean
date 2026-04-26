/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

public section


noncomputable section

open scoped Real Topology NNReal ENNReal
open Filter

namespace Complex

theorem hasStrictFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  have A : p.1 ≠ 0 := slitPlane_ne_zero hp
  have : (fun x : ℂ × ℂ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul]
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm, smul_add] using
    ((hasStrictFDerivAt_fst.clog hp).mul hasStrictFDerivAt_snd).cexp

theorem hasStrictFDerivAt_cpow' {x y : ℂ} (hp : x ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ) (x, y) :=
  @hasStrictFDerivAt_cpow (x, y) hp

theorem hasStrictDerivAt_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y := by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero, mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one] using
      ((hasStrictDerivAt_id y).const_mul (log x)).cexp

theorem hasFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
  (hasStrictFDerivAt_cpow hp).hasFDerivAt

end Complex

section fderiv

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {f' g' : StrongDual ℂ E}
  {x : E} {s : Set E} {c : ℂ}

theorem HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x :=
  (hasStrictFDerivAt_cpow (p := (f x, g x)) h0).comp x (hf.prodMk hg)

theorem HasStrictFDerivAt.const_cpow (hf : HasStrictFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prodMk hg)

theorem HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x := by
  convert (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x
    (hf.prodMk hg)

theorem HasFDerivWithinAt.const_cpow (hf : HasFDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

@[fun_prop]
theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : f x ∈ slitPlane) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

@[fun_prop]
theorem DifferentiableAt.const_cpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    DifferentiableAt ℂ (fun x => c ^ f x) x :=
  (hf.hasFDerivAt.const_cpow h0).differentiableAt

@[fun_prop]
theorem DifferentiableAt.cpow_const (hf : DifferentiableAt ℂ f x) (h0 : f x ∈ slitPlane) :
    DifferentiableAt ℂ (fun x => f x ^ c) x :=
  hf.cpow (differentiableAt_const c) h0

@[fun_prop]
theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : c ≠ 0 ∨ f x ≠ 0) : DifferentiableWithinAt ℂ (fun x => c ^ f x) s x :=
  (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.cpow_const (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ c) s x :=
  hf.cpow (differentiableWithinAt_const c) h0

@[fun_prop]
theorem DifferentiableOn.cpow (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn ℂ (fun x ↦ f x ^ g x) s :=
  fun x hx ↦ (hf x hx).cpow (hg x hx) (h0 hx)

@[fun_prop]
theorem DifferentiableOn.const_cpow (hf : DifferentiableOn ℂ f s)
    (h0 : c ≠ 0 ∨ ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℂ (fun x ↦ c ^ f x) s :=
  fun x hx ↦ (hf x hx).const_cpow (h0.imp_right fun h ↦ h x hx)

@[fun_prop]
theorem DifferentiableOn.cpow_const (hf : DifferentiableOn ℂ f s)
    (h0 : ∀ x ∈ s, f x ∈ slitPlane) :
    DifferentiableOn ℂ (fun x => f x ^ c) s :=
  hf.cpow (differentiableOn_const c) h0

@[fun_prop]
theorem Differentiable.cpow (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h0 : ∀ x, f x ∈ slitPlane) : Differentiable ℂ (fun x ↦ f x ^ g x) :=
  fun x ↦ (hf x).cpow (hg x) (h0 x)

@[fun_prop]
theorem Differentiable.const_cpow (hf : Differentiable ℂ f)
    (h0 : c ≠ 0 ∨ ∀ x, f x ≠ 0) : Differentiable ℂ (fun x ↦ c ^ f x) :=
  fun x ↦ (hf x).const_cpow (h0.imp_right fun h ↦ h x)

@[fun_prop]
lemma differentiable_const_cpow_of_neZero (z : ℂ) [NeZero z] :
    Differentiable ℂ fun s : ℂ ↦ z ^ s :=
  differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]
lemma differentiableAt_const_cpow_of_neZero (z : ℂ) [NeZero z] (t : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ ↦ z ^ s) t :=
  differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

end fderiv

section deriv

open Complex

variable {f g : ℂ → ℂ} {s : Set ℂ} {f' g' x c : ℂ}

/-- A private lemma that rewrites the output of lemmas like `HasFDerivAt.cpow` to the form
expected by lemmas like `HasDerivAt.cpow`. -/
private theorem aux : ((g x * f x ^ (g x - 1)) • (1 : ℂ →L[ℂ] ℂ).smulRight f' +
    (f x ^ g x * log (f x)) • (1 : ℂ →L[ℂ] ℂ).smulRight g') 1 =
      g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g' := by
  simp only [smul_eq_mul, one_mul, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_smul']

nonrec theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.hasStrictFDerivAt.cpow hg h0).hasStrictDerivAt

theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h).comp x hf

theorem Complex.hasStrictDerivAt_cpow_const (h : x ∈ slitPlane) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : f x ∈ slitPlane) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa [aux] using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf

theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x ∈ slitPlane) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasDerivWithinAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x := by
  simpa [aux] using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf

theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : f x ∈ slitPlane) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

theorem Complex.derivWithin_const_cpow (hf : DifferentiableWithinAt ℂ f s x) (c : ℂ) :
    derivWithin (fun x ↦ c ^ f x) s x = log c * derivWithin f s x * c ^ f x := by
  by_cases h : UniqueDiffWithinAt ℂ s x; swap
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt h,
      derivWithin_zero_of_not_uniqueDiffWithinAt h, mul_zero, zero_mul]
  by_cases hc : c = 0; swap
  · rw [mul_comm, ← mul_assoc]
    exact (hf.hasDerivWithinAt.const_cpow (Or.inl hc)).derivWithin h
  rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin] at h
  simp only [hc, log_zero, zero_mul]
  apply derivWithin_zero_of_frequently_mem {0, 1} (mt Set.Infinite.of_accPt (by simp))
  simpa [zero_cpow_eq_iff, em']

theorem Complex.deriv_const_cpow (hf : DifferentiableAt ℂ f x) (c : ℂ) :
    deriv (fun x ↦ c ^ f x) x = log c * deriv f x * c ^ f x := by
  rw [← derivWithin_univ, derivWithin_const_cpow, derivWithin_univ]
  rwa [differentiableWithinAt_univ]

set_option backward.isDefEq.respectTransparency false in
/-- Although `fun x => x ^ r` for fixed `r` is *not* complex-differentiable along the negative real
line, it is still real-differentiable, and the derivative is what one would formally expect.
See `hasDerivAt_ofReal_cpow_const` for an alternate formulation. -/
theorem hasDerivAt_ofReal_cpow_const' {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ -1) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x := by
  rw [Ne, ← add_eq_zero_iff_eq_neg, ← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    apply HasDerivAt.comp_ofReal (e := fun y => (y : ℂ) ^ (r + 1) / (r + 1))
    convert HasDerivAt.div_const (𝕜 := ℂ) ?_ (r + 1) using 1
    · exact (mul_div_cancel_right₀ _ hr).symm
    · convert HasDerivAt.cpow_const ?_ ?_ using 1
      · rw [add_sub_cancel_right, mul_comm]; exact (mul_one _).symm
      · exact hasDerivAt_id (x : ℂ)
      · simp [hx]
  · -- harder case : `x < 0`
    have : ∀ᶠ y : ℝ in 𝓝 x,
        (y : ℂ) ^ (r + 1) / (r + 1) = (-y : ℂ) ^ (r + 1) * exp (π * I * (r + 1)) / (r + 1) := by
      refine Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => ?_
      rw [ofReal_cpow_of_nonpos (le_of_lt hy)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ this
    rw [ofReal_cpow_of_nonpos (le_of_lt hx)]
    suffices HasDerivAt (fun y : ℝ => (-↑y) ^ (r + 1) * exp (↑π * I * (r + 1)))
        ((r + 1) * (-↑x) ^ r * exp (↑π * I * r)) x by
      convert this.div_const (r + 1) using 1
      conv_rhs => rw [mul_assoc, mul_comm, mul_div_cancel_right₀ _ hr]
    rw [mul_add ((π : ℂ) * _), mul_one, exp_add, exp_pi_mul_I, mul_comm (_ : ℂ) (-1 : ℂ),
      neg_one_mul]
    simp_rw [mul_neg, ← neg_mul, ← ofReal_neg]
    suffices HasDerivAt (fun y : ℝ => (↑(-y) : ℂ) ^ (r + 1)) (-(r + 1) * ↑(-x) ^ r) x by
      convert this.neg.mul_const _ using 1; ring
    suffices HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) (-x) by
      convert @HasDerivAt.scomp ℝ _ ℂ _ _ x ℝ _ _ _ _ _ _ _ _ this (hasDerivAt_neg x) using 1
      rw [real_smul, ofReal_neg 1, ofReal_one]; ring
    suffices HasDerivAt (fun y : ℂ => y ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) ↑(-x) by
      exact this.comp_ofReal
    conv in ↑_ ^ _ => rw [(by ring : r = r + 1 - 1)]
    convert HasDerivAt.cpow_const ?_ ?_ using 1
    · rw [add_sub_cancel_right, add_sub_cancel_right]; exact (mul_one _).symm
    · exact hasDerivAt_id ((-x : ℝ) : ℂ)
    · simp [hx]

/-- An alternate formulation of `hasDerivAt_ofReal_cpow_const'`. -/
theorem hasDerivAt_ofReal_cpow_const {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * x ^ (r - 1)) x := by
  have := HasDerivAt.const_mul r <| hasDerivAt_ofReal_cpow_const' hx
    (by rwa [ne_eq, sub_eq_neg_self])
  simpa [sub_add_cancel, mul_div_cancel₀ _ hr] using this

/-- A version of `DifferentiableAt.cpow_const` for a real function. -/
theorem DifferentiableAt.ofReal_cpow_const {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (h0 : f x ≠ 0) (h1 : c ≠ 0) :
    DifferentiableAt ℝ (fun (y : ℝ) => (f y : ℂ) ^ c) x :=
  (hasDerivAt_ofReal_cpow_const h0 h1).differentiableAt.comp x hf

theorem Complex.deriv_cpow_const (hx : x ∈ Complex.slitPlane) :
    deriv (fun (x : ℂ) ↦ x ^ c) x = c * x ^ (c - 1) :=
  (hasStrictDerivAt_cpow_const hx).hasDerivAt.deriv

/-- A version of `Complex.deriv_cpow_const` for a real variable. -/
theorem Complex.deriv_ofReal_cpow_const {x : ℝ} (hx : x ≠ 0) (hc : c ≠ 0) :
    deriv (fun x : ℝ ↦ (x : ℂ) ^ c) x = c * x ^ (c - 1) :=
  (hasDerivAt_ofReal_cpow_const hx hc).deriv

theorem deriv_cpow_const (hf : DifferentiableAt ℂ f x) (hx : f x ∈ Complex.slitPlane) :
    deriv (fun (x : ℂ) ↦ f x ^ c) x = c * f x ^ (c - 1) * deriv f x :=
  (hf.hasDerivAt.cpow_const hx).deriv

theorem isTheta_deriv_ofReal_cpow_const_atTop {c : ℂ} (hc : c ≠ 0) :
    deriv (fun (x : ℝ) => (x : ℂ) ^ c) =Θ[atTop] fun x => x ^ (c.re - 1) := by
  calc
    _ =ᶠ[atTop] fun x : ℝ ↦ c * x ^ (c - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx using by rw [deriv_ofReal_cpow_const hx hc]
    _ =Θ[atTop] fun x : ℝ ↦ ‖(x : ℂ) ^ (c - 1)‖ :=
      (Asymptotics.IsTheta.of_norm_eventuallyEq EventuallyEq.rfl).const_mul_left hc
    _ =ᶠ[atTop] fun x ↦ x ^ (c.re - 1) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

theorem isBigO_deriv_ofReal_cpow_const_atTop (c : ℂ) :
    deriv (fun (x : ℝ) => (x : ℂ) ^ c) =O[atTop] fun x => x ^ (c.re - 1) := by
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [cpow_zero, deriv_const', Asymptotics.isBigO_zero]
  · exact (isTheta_deriv_ofReal_cpow_const_atTop hc).1

end deriv

namespace Real

variable {x y z : ℝ}

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
theorem hasStrictFDerivAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert ((hasStrictFDerivAt_fst.log hp.ne').fun_mul hasStrictFDerivAt_snd).exp using 1
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
theorem hasStrictFDerivAt_rpow_of_neg (p : ℝ × ℝ) (hp : p.1 < 0) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert ((hasStrictFDerivAt_fst.log hp.ne).fun_mul hasStrictFDerivAt_snd).exp.fun_mul
    (hasStrictFDerivAt_snd.mul_const π).cos using 1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv, add_comm]; congr 2 <;> ring

/-- The function `fun (x, y) => x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
theorem contDiffAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  rcases hp.lt_or_gt with hneg | hpos
  exacts
    [(((contDiffAt_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (contDiffAt_snd.mul contDiffAt_const).cos).congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((contDiffAt_fst.log hpos.ne').mul contDiffAt_snd).exp.congr_of_eventuallyEq
      ((continuousAt_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]

theorem differentiableAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  (contDiffAt_rpow_of_ne p hp).differentiableAt one_ne_zero

theorem _root_.HasStrictDerivAt.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) : HasStrictDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  convert (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
    (hf.prodMk hg) using 1
  simp [mul_assoc, mul_comm]

theorem hasStrictDerivAt_rpow_const_of_ne {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases hx.lt_or_gt with hx | hx
  · have := (hasStrictFDerivAt_rpow_of_neg (x, p) hx).comp_hasStrictDerivAt x
      ((hasStrictDerivAt_id x).prodMk (hasStrictDerivAt_const x p))
    convert this using 1; simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx

theorem hasStrictDerivAt_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha

lemma differentiableAt_rpow_const_of_ne (p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun x => x ^ p) x :=
  (hasStrictDerivAt_rpow_const_of_ne hx p).hasStrictFDerivAt.differentiableAt

theorem not_differentiableAt_rpow_const_zero {r : ℝ} (hr : r < 1) (hr' : r ≠ 0) :
    ¬ DifferentiableAt ℝ (fun x ↦ x ^ r) (0 : ℝ) := by
  by_contra h
  set y := deriv (fun x ↦ x ^ r) (0 : ℝ)
  -- If `x ^ r` was differentiable at `0`, then `x ^ (r - 1)` would have a finite limit at `0`.
  have h : Filter.Tendsto (fun t ↦ t ^ (r - 1)) (𝓝[>] 0) (𝓝 y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_right
    intro x (hx : 0 < x)
    simp only [zero_add, ne_eq, hr', not_false_eq_true, Real.zero_rpow, sub_zero, smul_eq_mul]
    field_simp
    nth_rw 1 [← add_sub_cancel 1 r, Real.rpow_add hx]
    simp
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero (by simp [hr])) y h

lemma differentiableOn_rpow_const (p : ℝ) :
    DifferentiableOn ℝ (fun x => (x : ℝ) ^ p) {0}ᶜ :=
  fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

/-- This lemma says that `fun x => a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
theorem hasStrictDerivAt_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prodMk (hasStrictDerivAt_id _))

end Real

namespace Real

variable {z x y : ℝ}

theorem hasDerivAt_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (hasStrictDerivAt_rpow_const_of_ne hx _).hasDerivAt
  replace h : 1 ≤ p := h.neg_resolve_left rfl
  apply hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
    (hasStrictDerivAt_rpow_const_of_ne hx p).hasDerivAt
  exacts [continuousAt_id.rpow_const (Or.inr (zero_le_one.trans h)),
    ContinuousAt.const.mul (continuousAt_id.rpow_const (Or.inr (sub_nonneg.2 h)))]

theorem differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x ^ p :=
  fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt

theorem deriv_rpow_const (x p : ℝ) : deriv (fun x ↦ x ^ p) x = p * x ^ (p - 1) := by
  by_cases! h : p = 0
  · simp [h]
  by_cases! h' : x ≠ 0 ∨ 1 ≤ p
  · apply (Real.hasDerivAt_rpow_const h').deriv
  have h'' := deriv_zero_of_not_differentiableAt (not_differentiableAt_rpow_const_zero h'.2 h ·)
  grind [Real.zero_rpow]

theorem deriv_rpow_const' (p : ℝ) :
    (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext (deriv_rpow_const · p)

theorem contDiffAt_rpow_const_of_ne {x p : ℝ} {n : WithTop ℕ∞} (h : x ≠ 0) :
    ContDiffAt ℝ n (fun x => x ^ p) x :=
  (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)

theorem contDiff_rpow_const_of_le {p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiff ℝ n fun x : ℝ => x ^ p := by
  induction n generalizing p with
  | zero => exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  | succ n ihn =>
    have h1 : 1 ≤ p := le_trans (by simp) h
    rw [Nat.cast_add_one, ← le_sub_iff_add_le] at h
    rw [Nat.cast_add_one, contDiff_succ_iff_deriv, deriv_rpow_const' p]
    simp only [WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff, true_and]
    exact ⟨differentiable_rpow_const h1, contDiff_const.mul (ihn h)⟩

theorem contDiffAt_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  (contDiff_rpow_const_of_le h).contDiffAt

theorem contDiffAt_rpow_const {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le

theorem iter_deriv_rpow_const (r x : ℝ) (k : ℕ) :
    deriv^[k] (fun (x : ℝ) ↦ x ^ r) x = (descPochhammer ℝ k).eval r * x ^ (r - k) := by
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one, IH]
    ext y
    simp only [deriv_const_mul_field, deriv_rpow_const, ← mul_assoc, descPochhammer_succ_right,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
      mul_eq_mul_left_iff, mul_eq_zero]
    grind

theorem hasStrictDerivAt_rpow_const {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  ContDiffAt.hasStrictDerivAt' (contDiffAt_rpow_const (by rwa [← Nat.cast_one] at hx))
    (hasDerivAt_rpow_const hx) one_ne_zero

end Real

section Differentiability

open Real

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {f' g' : StrongDual ℝ E}
  {x : E} {s : Set E} {c p : ℝ} {n : WithTop ℕ∞}

theorem HasFDerivWithinAt.rpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h : 0 < f x) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') s x := by
  -- `by exact` to deal with tricky unification.
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prodMk hg)

theorem HasFDerivAt.rpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 0 < f x) :
    HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x := by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prodMk hg)

theorem HasStrictFDerivAt.rpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h : 0 < f x) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x :=
  (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (h : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiableWithinAt x (hf.prodMk hg)

@[fun_prop]
theorem DifferentiableAt.rpow (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h : f x ≠ 0) : DifferentiableAt ℝ (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
theorem DifferentiableOn.rpow (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (h : ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℝ (fun x => f x ^ g x) s := fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
theorem Differentiable.rpow (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => f x ^ g x := fun x => (hf x).rpow (hg x) (h x)

@[fun_prop]
theorem HasFDerivWithinAt.rpow_const (hf : HasFDerivWithinAt f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFDerivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivWithinAt x hf

@[fun_prop]
theorem HasFDerivAt.rpow_const (hf : HasFDerivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.rpow_const (hf : HasStrictFDerivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasStrictFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasStrictDerivAt_rpow_const h).comp_hasStrictFDerivAt x hf

@[fun_prop]
theorem DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt ℝ f s x)
    (h : f x ≠ 0 ∨ 1 ≤ p) : DifferentiableWithinAt ℝ (fun x => f x ^ p) s x :=
  (hf.hasFDerivWithinAt.rpow_const h).differentiableWithinAt

@[simp]
theorem DifferentiableAt.rpow_const (hf : DifferentiableAt ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableAt ℝ (fun x => f x ^ p) x :=
  (hf.hasFDerivAt.rpow_const h).differentiableAt

@[fun_prop]
theorem DifferentiableOn.rpow_const (hf : DifferentiableOn ℝ f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableOn ℝ (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)

@[fun_prop]
theorem Differentiable.rpow_const (hf : Differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
    Differentiable ℝ fun x => f x ^ p := fun x => (hf x).rpow_const (h x)

theorem HasFDerivWithinAt.const_rpow (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') s x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.const_rpow (hf : HasFDerivAt f f' x) (hc : 0 < c) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.const_rpow (hf : HasStrictFDerivAt f f' x) (hc : 0 < c) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

@[fun_prop]
theorem ContDiffWithinAt.rpow (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (h : f x ≠ 0) : ContDiffWithinAt ℝ n (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp_contDiffWithinAt x (hf.prodMk hg)

@[fun_prop]
theorem ContDiffAt.rpow (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
theorem ContDiffOn.rpow (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ g x) s := fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
theorem ContDiff.rpow (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ g x :=
  contDiff_iff_contDiffAt.mpr fun x => hf.contDiffAt.rpow hg.contDiffAt (h x)

@[fun_prop]
theorem ContDiffWithinAt.rpow_const_of_ne (hf : ContDiffWithinAt ℝ n f s x) (h : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => f x ^ p) s x :=
  hf.rpow contDiffWithinAt_const h

@[fun_prop]
theorem ContDiffAt.rpow_const_of_ne (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ p) x :=
  hf.rpow contDiffAt_const h

@[fun_prop]
theorem ContDiffOn.rpow_const_of_ne (hf : ContDiffOn ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

@[fun_prop]
theorem ContDiff.rpow_const_of_ne (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ p :=
  hf.rpow contDiff_const h

variable {m : ℕ}

@[fun_prop]
theorem ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt ℝ m f s x) (h : ↑m ≤ p) :
    ContDiffWithinAt ℝ m (fun x => f x ^ p) s x :=
  (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

@[fun_prop]
theorem ContDiffAt.rpow_const_of_le (hf : ContDiffAt ℝ m f x) (h : ↑m ≤ p) :
    ContDiffAt ℝ m (fun x => f x ^ p) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

@[fun_prop]
theorem ContDiffOn.rpow_const_of_le (hf : ContDiffOn ℝ m f s) (h : ↑m ≤ p) :
    ContDiffOn ℝ m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_le h

@[fun_prop]
theorem ContDiff.rpow_const_of_le (hf : ContDiff ℝ m f) (h : ↑m ≤ p) :
    ContDiff ℝ m fun x => f x ^ p :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

end fderiv

section deriv

variable {f g : ℝ → ℝ} {f' g' x y p : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h : 0 < f x) : HasDerivWithinAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) s x := by
  convert (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  dsimp; ring

theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h

theorem HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x := by
  convert (hasDerivAt_rpow_const hx).comp_hasDerivWithinAt x hf using 1
  ring

theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx

theorem derivWithin_rpow_const (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => f x ^ p) s x = derivWithin f s x * p * f x ^ (p - 1) :=
  (hf.hasDerivWithinAt.rpow_const hx).derivWithin hxs

@[simp]
theorem deriv_rpow_const (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    deriv (fun x => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  (hf.hasDerivAt.rpow_const hx).deriv

theorem deriv_norm_ofReal_cpow (c : ℂ) {t : ℝ} (ht : 0 < t) :
    (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ c‖) t = c.re * t ^ (c.re - 1) := by
  rw [EventuallyEq.deriv_eq (f := fun x ↦ x ^ c.re)]
  · rw [Real.deriv_rpow_const t]
  · filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

lemma isTheta_deriv_rpow_const_atTop {p : ℝ} (hp : p ≠ 0) :
    deriv (fun (x : ℝ) ↦ x ^ p) =Θ[atTop] fun x => x ^ (p - 1) := by
  calc deriv (fun (x : ℝ) ↦ x ^ p) = fun x => p * x ^ (p - 1) := Real.deriv_rpow_const' p
    _ =Θ[atTop] fun x ↦ x ^ (p - 1) :=
      Asymptotics.IsTheta.const_mul_left hp Asymptotics.isTheta_rfl

lemma isBigO_deriv_rpow_const_atTop (p : ℝ) :
    deriv (fun (x : ℝ) => x ^ p) =O[atTop] fun x => x ^ (p - 1) := by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

variable {a : ℝ}

theorem HasDerivWithinAt.const_rpow (ha : 0 < a) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a ^ f x) s x := by
  convert (hasDerivWithinAt_const x s a).rpow hf ha using 1
  ring

theorem HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDerivAt f f' x) :
    HasDerivAt (a ^ f ·) (Real.log a * f' * a ^ f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.const_rpow ha

theorem derivWithin_const_rpow (ha : 0 < a) (hf : DifferentiableWithinAt ℝ f s x) :
    derivWithin (a ^ f ·) s x = Real.log a * derivWithin f s x * a ^ f x := by
  by_cases hxs : UniqueDiffWithinAt ℝ s x
  · exact (hf.hasDerivWithinAt.const_rpow ha).derivWithin hxs
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      mul_zero, zero_mul]

@[simp]
theorem deriv_const_rpow (ha : 0 < a) (hf : DifferentiableAt ℝ f x) :
    deriv (a ^ f ·) x = Real.log a * deriv f x * a ^ f x :=
  (hf.hasDerivAt.const_rpow ha).deriv


end deriv

end Differentiability
