/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration by parts and by substitution

We derive additional integration techniques from FTC-2:
* `intervalIntegral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `intervalIntegral.integral_comp_mul_deriv''` - integration by substitution

Versions of the change of variables formula for monotone and antitone functions, but with much
weaker assumptions on the integrands and not restricted to intervals,
can be found in `Mathlib/MeasureTheory/Function/JacobianOneDim.lean`

## Tags

integration by parts, change of variables in integrals
-/

open MeasureTheory Set

open scoped Topology Interval

namespace intervalIntegral

variable {a b : ℝ}

section Parts

section Mul

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {u v u' v' : ℝ → A}

/-- The integral of the derivative of a product of two maps.
For improper integrals, see `MeasureTheory.integral_deriv_mul_eq_sub`,
`MeasureTheory.integral_Ioi_deriv_mul_eq_sub`, and `MeasureTheory.integral_Iic_deriv_mul_eq_sub`. -/
theorem integral_deriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx ↦ (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

/-- The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
two-sided derivative in the interior of the interval. -/
theorem integral_deriv_mul_eq_sub_of_hasDerivAt (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]]) (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx ↦ huu' x hx |>.hasDerivWithinAt) (fun x hx ↦ hvv' x hx |>.hasDerivWithinAt) hu' hv'

/-- The integral of the derivative of a product of two maps.
Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
  one-sided derivative at the endpoints. -/
theorem integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- Special case of `integral_deriv_mul_eq_sub_of_hasDeriv_right` where the functions have a
  derivative at the endpoints. -/
theorem integral_deriv_mul_eq_sub
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx ↦ hu x hx |>.hasDerivWithinAt) (fun x hx ↦ hv x hx |>.hasDerivWithinAt) hu' hv'

/-- **Integration by parts**. For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`. -/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

/-- **Integration by parts**. Special case of `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval. -/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

/-- **Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints. -/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- **Integration by parts**. Special case of
`intervalIntegrable.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints.
For improper integrals, see
`MeasureTheory.integral_mul_deriv_eq_deriv_mul`,
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`,
and `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`. -/
theorem integral_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end Mul

section SMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
variable [IsScalarTower ℝ 𝕜 E]

variable {u u' : ℝ → 𝕜}
variable {v v' : ℝ → E}

/-- The integral of the derivative of a scalar multiplication. -/
theorem integral_deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x • v x + u x • v' x = u b • v b - u a • v a := by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx ↦ (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

/-- **Integration by parts** (vector-valued). -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x := by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv

/-- **Integration by parts** (vector-valued).
Special case of `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval. -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints. -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints. -/
theorem integral_smul_deriv_eq_deriv_smul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end SMul

end Parts

/-!
### Integration by substitution / Change of variables
-/

section SMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → ℝ} {g g' : ℝ → E}

/-- Change of variables, general form. If `f` is continuous on `[a, b]` and has
right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `f' x • (g ∘ f) x` is integrable on `[a, b]`,
then we can substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also
`integral_image_eq_integral_deriv_smul_of_monotoneOn` dropping all assumptions on `g`. -/
theorem integral_comp_smul_deriv''' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x ↦ f' x • (g ∘ f) x) [[a, b]]) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  rw [hf.image_uIcc, ← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u ↦ ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.image_uIcc]; exact mem_image_of_mem f left_mem_uIcc
    · rw [← hf.image_uIcc]; exact mapsTo_image _ _
  have h_der :
    ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (fun u ↦ ∫ t in f a..f u, g t) (f' x • (g ∘ f) x) (Ioi x) x := by
    intro x hx
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hx.1
    obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hx.2
    have cdsub : [[c, d]] ⊆ Ioo (min a b) (max a b) := by
      rw [uIcc_of_le (hc.2.trans hd.1).le]
      exact Icc_subset_Ioo hc.1 hd.2
    replace hg_cont := hg_cont.mono (image_mono cdsub)
    let J := [[sInf (f '' [[c, d]]), sSup (f '' [[c, d]])]]
    have hJ : f '' [[c, d]] = J := (hf.mono (cdsub.trans Ioo_subset_Icc_self)).image_uIcc
    rw [hJ] at hg_cont
    have h2x : f x ∈ J := by rw [← hJ]; exact mem_image_of_mem _ (mem_uIcc_of_le hc.2.le hd.1.le)
    have h2g : IntervalIntegrable g volume (f a) (f x) := by
      refine hg1.mono_set ?_
      rw [← hf.image_uIcc]
      exact hf.surjOn_uIcc left_mem_uIcc (Ioo_subset_Icc_self hx)
    have h3g : StronglyMeasurableAtFilter g (𝓝[J] f x) :=
      hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (f x)
    haveI : Fact (f x ∈ J) := ⟨h2x⟩
    have : HasDerivWithinAt (fun u ↦ ∫ x in f a..u, g x) (g (f x)) J (f x) :=
      intervalIntegral.integral_hasDerivWithinAt_right h2g h3g (hg_cont (f x) h2x)
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hd.1) ?_).Ioi_of_Ioo hd.1
    rw [← hJ]
    refine (mapsTo_image _ _).mono ?_ Subset.rfl
    exact Ioo_subset_Icc_self.trans ((Icc_subset_Icc_left hc.2.le).trans Icc_subset_uIcc)
  rw [← intervalIntegrable_iff'] at hg2
  simp_rw [integral_eq_sub_of_hasDeriv_right h_cont h_der hg2, integral_same, sub_zero]

/-- Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also
`integral_image_eq_integral_deriv_smul_of_monotoneOn` dropping all assumptions on `g`. -/
theorem integral_comp_smul_deriv'' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  refine integral_comp_smul_deriv''' hf hff' (hg.mono <| image_mono Ioo_subset_Icc_self) ?_
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

/-- Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_comp_smul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.

If the function `f` is monotone or antitone, see also
`integral_image_eq_integral_deriv_smul_of_monotoneOn` dropping all assumptions on `g`. -/
theorem integral_comp_smul_deriv' (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv'' (fun x hx ↦ (h x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

/-- Change of variables, most common version. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

If the function `f` is monotone or antitone, see also
`integral_image_eq_integral_deriv_smul_of_monotoneOn` dropping all assumptions on `g`. -/
theorem integral_comp_smul_deriv (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv' h h' hg.continuousOn

section CompleteSpace

variable [CompleteSpace E]

theorem integral_deriv_comp_smul_deriv' (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a := by
  rw [integral_comp_smul_deriv'' hf hff' hf' hg',
    integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

theorem integral_deriv_comp_smul_deriv (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a :=
  integral_eq_sub_of_hasDerivAt (fun x hx ↦ (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

end CompleteSpace

end SMul

section Mul

/-- Change of variables, general form for scalar functions. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `(g ∘ f) x * f' x` is integrable on `[a, b]`, then we can substitute `u = f x`
to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv''' {a b : ℝ} {f f' : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x ↦ (g ∘ f) x * f' x) [[a, b]]) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  have hg2' : IntegrableOn (fun x ↦ f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_comp_smul_deriv''' hf hff' hg_cont hg1 hg2'

/-- Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using integral_comp_smul_deriv'' hf hff' hf' hg

/-- Change of variables. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
Compared to `intervalIntegral.integral_comp_mul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x := by
  simpa [mul_comm] using integral_comp_smul_deriv' h h' hg

/-- Change of variables, most common version. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x :=
  integral_comp_mul_deriv' h h' hg.continuousOn

theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_comp_smul_deriv' hf hff' hf' hg hgg' hg'

theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_comp_smul_deriv hf hg hf' hg'

end Mul

end intervalIntegral
