/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Anatole Dedecker, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Derivative of `f x * g x`

In this file we prove formulas for `(f x * g x)'` and `(f x • g x)'`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, multiplication
-/

universe u v w

noncomputable section

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter 𝕜}

/-! ### Derivative of bilinear maps -/

namespace ContinuousLinearMap

variable {B : E →L[𝕜] F →L[𝕜] G} {u : 𝕜 → E} {v : 𝕜 → F} {u' : E} {v' : F}

theorem hasDerivWithinAt_of_bilinear
    (hu : HasDerivWithinAt u u' s x) (hv : HasDerivWithinAt v v' s x) :
    HasDerivWithinAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) s x := by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt

theorem hasDerivAt_of_bilinear (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  simpa using (B.hasFDerivAt_of_bilinear hu.hasFDerivAt hv.hasFDerivAt).hasDerivAt

theorem hasStrictDerivAt_of_bilinear (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x) :
    HasStrictDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt

theorem derivWithin_of_bilinear
    (hu : DifferentiableWithinAt 𝕜 u s x) (hv : DifferentiableWithinAt 𝕜 v s x) :
    derivWithin (fun y => B (u y) (v y)) s x =
      B (u x) (derivWithin v s x) + B (derivWithin u s x) (v x) := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_of_bilinear (hu : DifferentiableAt 𝕜 u x) (hv : DifferentiableAt 𝕜 v x) :
    deriv (fun y => B (u y) (v y)) x = B (u x) (deriv v x) + B (deriv u x) (v x) :=
  (B.hasDerivAt_of_bilinear hu.hasDerivAt hv.hasDerivAt).deriv

end ContinuousLinearMap

section SMul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c y • f y) (c x • f' + c' • f x) s x := by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt

theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf

nonrec theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  simpa using (hc.smul hf).hasStrictDerivAt

theorem derivWithin_smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv

theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x := by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this

theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x := by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this

theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
    HasDerivAt (fun y => c y • f) (c' • f) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f

theorem derivWithin_smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.smul_const f).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.hasDerivAt.smul_const f).deriv

end SMul

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

nonrec theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c • f y) (c • f') x := by
  simpa using (hf.const_smul c).hasStrictDerivAt

nonrec theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c • f y) (c • f') x L := by
  simpa using (hf.const_smul c).hasDerivAtFilter

nonrec theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c • f y) (c • f') s x :=
  hf.const_smul c

nonrec theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c • f y) (c • f') x :=
  hf.const_smul c

theorem derivWithin_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hf.hasDerivWithinAt.const_smul c).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv

/-- A variant of `deriv_const_smul` without differentiability assumption when the scalar
multiplication is by field elements. -/
lemma deriv_const_smul' {f : 𝕜 → F} {x : 𝕜} {R : Type*} [DivisionRing R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (c : R) :
    deriv (fun y ↦ c • f y) x = c • deriv f x := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact deriv_const_smul c hf
  · rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul, deriv_const']
    · have H : ¬DifferentiableAt 𝕜 (fun y ↦ c • f y) x := by
        contrapose! hf
        conv => enter [2, y]; rw [← inv_smul_smul₀ hc (f y)]
        exact DifferentiableAt.const_smul hf c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt H, smul_zero]

end ConstSMul

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type*} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸]
  {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c y * d y) (c' * d x + c x * d') s x := by
  have := (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this

theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul hd

theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  have := (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this

theorem derivWithin_mul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

@[simp]
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv

theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x := by
  convert hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero, add_zero]

theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
    HasDerivAt (fun y => c y * d) (c' * d) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d

theorem hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c

theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x := by
  convert hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero, add_zero]

theorem derivWithin_mul_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = derivWithin c s x * d := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.mul_const d).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

lemma derivWithin_mul_const_field (u : 𝕜') :
    derivWithin (fun y => v y * u) s x = derivWithin v s x * u := by
  by_cases hv : DifferentiableWithinAt 𝕜 v s x
  · rw [derivWithin_mul_const hv u]
  by_cases hu : u = 0
  · simp [hu]
  rw [derivWithin_zero_of_not_differentiableWithinAt hv, zero_mul,
      derivWithin_zero_of_not_differentiableWithinAt]
  have : v = fun x ↦ (v x * u) * u⁻¹ := by ext; simp [hu]
  exact fun h_diff ↦ hv <| this ▸ h_diff.mul_const _

theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
    deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.hasDerivAt.mul_const d).deriv

theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v := by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine deriv_zero_of_not_differentiableAt (mt (fun H => ?_) hu)
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹

@[simp]
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v

theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x := by
  convert (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul, zero_add]

theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c

theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x := by
  convert (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul, zero_add]

theorem derivWithin_const_mul (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hd.hasDerivWithinAt.const_mul c).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

lemma derivWithin_const_mul_field (u : 𝕜') :
    derivWithin (fun y => u * v y) s x = u * derivWithin v s x := by
  simp_rw [mul_comm u]
  exact derivWithin_mul_const_field u

theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.hasDerivAt.const_mul c).deriv

theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simp only [mul_comm u, deriv_mul_const_field]

@[simp]
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun _ => deriv_const_mul_field u

end Mul

section Prod

section HasDeriv

variable {ι : Type*} [DecidableEq ι] {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → 𝕜 → 𝔸'} {f' : ι → 𝔸'}

theorem HasDerivAt.finset_prod (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasFDerivAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivAt)).hasDerivAt

theorem HasDerivWithinAt.finset_prod (hf : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) s x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasFDerivWithinAt.finset_prod (fun i hi ↦ (hf i hi).hasFDerivWithinAt)).hasDerivWithinAt

theorem HasStrictDerivAt.finset_prod (hf : ∀ i ∈ u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using
    (HasStrictFDerivAt.finset_prod (fun i hi ↦ (hf i hi).hasStrictFDerivAt)).hasStrictDerivAt

theorem deriv_finset_prod (hf : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i ∈ u, f i ·) x = ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.finset_prod fun i hi ↦ (hf i hi).hasDerivAt).deriv

theorem derivWithin_finset_prod
    (hf : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i ∈ u, f i ·) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • derivWithin (f i) s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (HasDerivWithinAt.finset_prod fun i hi ↦ (hf i hi).hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

end HasDeriv

variable {ι : Type*} {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → 𝕜 → 𝔸'}

@[fun_prop]
theorem DifferentiableAt.finset_prod (hd : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (∏ i ∈ u, f i ·) x := by
  classical
  exact
    (HasDerivAt.finset_prod (fun i hi ↦ DifferentiableAt.hasDerivAt (hd i hi))).differentiableAt

@[fun_prop]
theorem DifferentiableWithinAt.finset_prod (hd : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (∏ i ∈ u, f i ·) s x := by
  classical
  exact (HasDerivWithinAt.finset_prod (fun i hi ↦
    DifferentiableWithinAt.hasDerivWithinAt (hd i hi))).differentiableWithinAt

@[fun_prop]
theorem DifferentiableOn.finset_prod (hd : ∀ i ∈ u, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (∏ i ∈ u, f i ·) s :=
  fun x hx ↦ .finset_prod (fun i hi ↦ hd i hi x hx)

@[fun_prop]
theorem Differentiable.finset_prod (hd : ∀ i ∈ u, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (∏ i ∈ u, f i ·) :=
  fun x ↦ .finset_prod (fun i hi ↦ hd i hi x)

end Prod

section Div

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
    HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

@[fun_prop]
theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.hasDerivWithinAt.div_const _).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') :
    DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.hasDerivAt.div_const _).differentiableAt

@[fun_prop]
theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') :
    DifferentiableOn 𝕜 (fun x => c x / d) s := fun x hx => (hc x hx).div_const d

@[simp, fun_prop]
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') :
    Differentiable 𝕜 fun x => c x / d := fun x => (hc x).div_const d

theorem derivWithin_div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
    derivWithin (fun x => c x / d) s x = derivWithin c s x / d := by
  simp [div_eq_inv_mul, derivWithin_const_mul, hc]

@[simp]
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [div_eq_mul_inv, deriv_mul_const_field]

end Div

section CLMCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G}
  {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  have := (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt
  rwa [add_apply, comp_apply, comp_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this

theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x := by
  have := (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt
  rwa [add_apply, comp_apply, comp_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this

theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd

theorem derivWithin_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => (c y).comp (d y)) s x =
      (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv

theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this

theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x := by
  have := (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this

theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this

theorem derivWithin_clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv

end CLMCompApply
