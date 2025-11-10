/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variable formulas for integrals in dimension 1

We record in this file versions of the general change of variables formula in integrals for
functions from `R` to `ℝ`. This makes it possible to replace the determinant of the Fréchet
derivative with the one-dimensional derivative.

We also give more specific versions of these theorems for monotone and antitone functions: this
makes it possible to drop the injectivity assumption of the general theorems, as the derivative
is zero on the set of non-injectivity, which means that it can be discarded.

See also `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean` for versions of
the change of variables formula in dimension 1 for non-monotone functions, formulated with
the interval integral and with stronger requirements on the integrand.
-/


open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace ContinuousLinearMap

open scoped NNReal ENNReal Topology Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ} {f f' : ℝ → ℝ}
  {g : ℝ → F}

namespace MeasureTheory

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the
Lebesgue integral of a function `g : ℝ → ℝ≥0∞` on `f '' s` coincides with the Lebesgue integral
of `|(f' x)| * g ∘ f` on `s`. -/
theorem lintegral_image_eq_lintegral_abs_deriv_mul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x) := by
  simpa only [det_one_smulRight] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then a
function `g : ℝ → F` is integrable on `f '' s` if and only if `|(f' x)| • g ∘ f` is integrable on
`s`. -/
theorem integrableOn_image_iff_integrableOn_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s := by
  simpa only [det_one_smulRight] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Change of variable formula for differentiable functions (one-variable version): if a function
`f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the Bochner integral of a
function `g : ℝ → F` on `f '' s` coincides with the integral of `|(f' x)| • g ∘ f` on `s`. -/
theorem integral_image_eq_integral_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → F) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  simpa only [det_one_smulRight] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Technical structure theorem for monotone differentiable functions.

If a function `f` is monotone on a measurable set and has a derivative `f'`, one can decompose
the set as a disjoint union `a ∪ b ∪ c` of measurable sets where `a` is countable (the points which
are isolated on the left or on the right, where `f'` is not well controlled),
`f` is locally constant on `b` and `f' = 0` there (the preimages of the countably many points with
several preimages), and `f` is injective on `c` with nonnegative derivative (the other points). -/
theorem exists_decomposition_of_monotoneOn_hasDerivWithinAt (hs : MeasurableSet s)
    (hf : MonotoneOn f s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    ∃ (a b c : Set ℝ), a ∪ (b ∪ c) = s ∧ MeasurableSet a ∧ MeasurableSet b ∧ MeasurableSet c ∧
    Disjoint a (b ∪ c) ∧ Disjoint b c ∧ a.Countable ∧ (f '' b).Countable ∧
    (∀ x ∈ b, f' x = 0) ∧ (∀ x ∈ c, 0 ≤ f' x) ∧ InjOn f c := by
  let a := {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥} ∪ {x ∈ s | 𝓝[s ∩ Iio x] x = ⊥}
  have a_count : a.Countable :=
    countable_setOf_isolated_right_within.union countable_setOf_isolated_left_within
  let s₁ := s \ a
  have hs₁ : MeasurableSet s₁ := hs.diff a_count.measurableSet
  let u : Set ℝ := {c | ∃ x y, x ∈ s₁ ∧ y ∈ s₁ ∧ x < y ∧ f x = c ∧ f y = c}
  have hu : Set.Countable u := MonotoneOn.countable_setOf_two_preimages (hf.mono diff_subset)
  let b := s₁ ∩ f ⁻¹' u
  have hb : MeasurableSet b := by
    have : b = ⋃ z ∈ u, s₁ ∩ f⁻¹' {z} := by ext; simp [b]
    rw [this]
    apply MeasurableSet.biUnion hu (fun z hz ↦ ?_)
    obtain ⟨v, hv, tv⟩ : ∃ v, OrdConnected v ∧ (s \ a) ∩ f ⁻¹' {z} = (s \ a) ∩ v :=
      ordConnected_singleton.preimage_monotoneOn (hf.mono diff_subset)
    exact tv ▸ (hs.diff a_count.measurableSet).inter hv.measurableSet
  let c := s₁ \ b
  have hc : MeasurableSet c := hs₁.diff hb
  refine ⟨a, b, c, ?_, a_count.measurableSet, hb, hc, ?_, ?_, a_count, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [diff_self_inter, inter_union_diff, union_diff_self, mem_union, mem_setOf_eq,
      or_iff_right_iff_imp, a, b, s₁, c]
    tauto
  · simpa [b, c, s₁] using disjoint_sdiff_right
  · simpa [c] using disjoint_sdiff_right
  · exact hu.mono (by simp [b])
  · /- We have to show that the derivative is `0` at `x ∈ b`. For that, we use that there is another
    point `p` with `f p = f x`, by definition of `b`. If `p < x`, then `f` is locally constant to
    the left of `x`. As `x` is not isolated to its left (since we are not in the set `a`), it
    follows that `f' x = 0`. The same argument works if `x < p`, using the right neighborhood
    instead. -/
    intro x hx
    obtain ⟨p, ps₁, px, fpx⟩ : ∃ p ∈ s₁, p ≠ x ∧ f p = f x := by
      rcases hx.2 with ⟨p, q, ps₁, qs₁, pq, hp, hq⟩
      rcases eq_or_ne p x with h'p | h'p
      · exact ⟨q, qs₁, (h'p.symm.le.trans_lt pq).ne', hq⟩
      · exact ⟨p, ps₁, h'p, hp⟩
    -- we treat separately the cases `p < x` and `x < p` as we couldn't unify their proofs nicely
    rcases lt_or_gt_of_ne px with px | px
    · have K : HasDerivWithinAt f 0 (s ∩ Ioo p x) x := by
        have E (y) (hy : y ∈ s ∩ Ioo p x) : f y = f x := by
          apply le_antisymm (hf hy.1 hx.1.1 hy.2.2.le)
          rw [← fpx]
          exact hf ps₁.1 hy.1 hy.2.1.le
        have : HasDerivWithinAt (fun y ↦ f x) 0 (s ∩ Ioo p x) x :=
          hasDerivWithinAt_const x (s ∩ Ioo p x) (f x)
        exact this.congr E rfl
      have K' : HasDerivWithinAt f (f' x) (s ∩ Ioo p x) x :=
        (hf' x hx.1.1).mono inter_subset_left
      apply UniqueDiffWithinAt.eq_deriv _ _ K' K
      have J1 : (s ∩ Ioo p x) \ {x} = s ∩ Ioo p x := by simp
      have J2 : 𝓝[s ∩ Ioo p x] x = 𝓝[s ∩ Iio x] x := by
        simp [nhdsWithin_inter, nhdsWithin_Ioo_eq_nhdsLT px]
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin, J1, J2]
      simp only [mem_inter_iff, mem_diff, hx.1.1, mem_union, mem_setOf_eq, true_and, not_or,
        mem_preimage, b, s₁, a] at hx
      exact neBot_iff.2 hx.1.2
    · have K : HasDerivWithinAt f 0 (s ∩ Ioo x p) x := by
        have E (y) (hy : y ∈ s ∩ Ioo x p) : f y = f x := by
          apply le_antisymm  _ (hf hx.1.1 hy.1 hy.2.1.le)
          rw [← fpx]
          exact hf hy.1 ps₁.1 hy.2.2.le
        have : HasDerivWithinAt (fun y ↦ f x) 0 (s ∩ Ioo x p) x :=
          hasDerivWithinAt_const x (s ∩ Ioo x p) (f x)
        exact this.congr E rfl
      have K' : HasDerivWithinAt f (f' x) (s ∩ Ioo x p) x :=
        (hf' x hx.1.1).mono inter_subset_left
      apply UniqueDiffWithinAt.eq_deriv _ _ K' K
      have J1 : (s ∩ Ioo x p) \ {x} = (s ∩ Ioo x p) := by simp
      have J2 : 𝓝[s ∩ Ioo x p] x = 𝓝[s ∩ Ioi x] x := by
        simp [nhdsWithin_inter, nhdsWithin_Ioo_eq_nhdsGT px]
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin, J1, J2]
      simp only [mem_inter_iff, mem_diff, hx.1.1, mem_union, mem_setOf_eq, true_and, not_or,
        mem_preimage, b, s₁, a] at hx
      exact neBot_iff.2 hx.1.1
  · /- We have to show that the derivative is nonnegative at points of `c`. As these points are
    not isolated in `s`, this follows from the fact that `f` is monotone on `s`. -/
    intro x hx
    apply (hf' x hx.1.1).nonneg_of_monotoneOn _ hf
    simp only [mem_diff, hx.1.1, mem_union, mem_setOf_eq, true_and, not_or, c, s₁, a, b] at hx
    rw [accPt_principal_iff_nhdsWithin]
    have : (𝓝[s ∩ Iio x] x).NeBot := neBot_iff.2 hx.1.2
    apply this.mono
    apply nhdsWithin_mono
    rintro y ⟨yt, yx : y < x⟩
    exact ⟨yt, by simpa using yx.ne⟩
  · intro x hx y hy hxy
    contrapose! hxy
    wlog H : x < y generalizing x y with h
    · have : y < x := by order
      exact (h hy hx hxy.symm this).symm
    refine fun h ↦ hx.2 ⟨hx.1, ?_⟩
    exact ⟨x, y, hx.1, hy.1, H, rfl, h.symm⟩

/- Change of variable formula for differentiable functions: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(f' x) * u ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_monotoneOn`. -/
theorem lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (f' x) * u (f x) := by
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have I : ∫⁻ x in s, ENNReal.ofReal (f' x) * u (f x)
      = ∫⁻ x in c, ENNReal.ofReal (f' x) * u (f x) := by
    have : ∫⁻ x in a, ENNReal.ofReal (f' x) * u (f x) = 0 :=
      setLIntegral_measure_zero a _ (a_count.measure_zero volume)
    rw [← h_union, lintegral_union (hb.union hc) h_disj, this, zero_add]
    have : ∫⁻ x in b, ENNReal.ofReal (f' x) * u (f x) = 0 :=
      setLIntegral_eq_zero hb (fun x hx ↦ by simp [deriv_b x hx])
    rw [lintegral_union hc h_disj', this, zero_add]
  have J : ∫⁻ x in f '' s, u x = ∫⁻ x in f '' c, u x := by
    apply setLIntegral_congr
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hf' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  have : ∫⁻ x in c, ENNReal.ofReal (f' x) * u (f x)
      = ∫⁻ x in c, ENNReal.ofReal (|(F' x).det|) * u (f x) := by
    apply setLIntegral_congr_fun hc (fun x hx ↦ ?_)
    simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, one_mul, F']
    rw [abs_of_nonneg (deriv_c x hx)]
  rw [this]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul _ hc hf' inj_c _

/-- Change of variable formula for differentiable functions, set version: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_monotoneOn`. -/
theorem lintegral_deriv_eq_volume_image_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (f' x)) = volume (f '' s) := by
  simpa using (lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf 1).symm

/-- Integrability in the change of variable formula for differentiable functions: if a real
function `f` is monotone and differentiable on a measurable set `s`, then a function
`g : ℝ → F` is integrable on `f '' s` if and only if `f' x • g ∘ f` is integrable on `s` . -/
theorem integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (g : ℝ → F) :
    IntegrableOn g (f '' s) ↔ IntegrableOn (fun x ↦ (f' x) • g (f x)) s := by
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have I : IntegrableOn (fun x => (f' x) • g (f x)) s
      ↔ IntegrableOn (fun x => (f' x) • g (f x)) c := by
    have A : IntegrableOn (fun x ↦ f' x • g (f x)) a :=
      IntegrableOn.of_measure_zero (a_count.measure_zero volume)
    have B : IntegrableOn (fun x ↦ f' x • g (f x)) b := by
      have : IntegrableOn (fun x ↦ (0 : F)) b := by simp
      exact this.congr_fun (fun x hx ↦ by simp [deriv_b x hx]) hb
    simp only [← h_union, integrableOn_union, A, B, true_and]
  have J : IntegrableOn g (f '' s) ↔ IntegrableOn g (f '' c) := by
    apply integrableOn_congr_set_ae
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul _ hc hF' inj_c]
  apply integrableOn_congr_fun (fun x hx ↦ ?_) hc
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, one_mul, F']
  rw [abs_of_nonneg (deriv_c x hx)]

/-- Change of variable formula for differentiable functions: if a real function `f` is
monotone and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(f' x) • g ∘ f` on `s` . -/
theorem integral_image_eq_integral_deriv_smul_of_monotoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : MonotoneOn f s) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, f' x • g (f x) := by
  by_cases H : IntegrableOn g (f '' s); swap
  · rw [integral_undef H, integral_undef]
    simpa [integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hf' hf] using H
  have H' : IntegrableOn (fun x ↦ (f' x) • g (f x)) s :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hf' hf g).1 H
  rcases exists_decomposition_of_monotoneOn_hasDerivWithinAt hs hf hf' with
    ⟨a, b, c, h_union, ha, hb, hc, h_disj, h_disj', a_count, fb_count, deriv_b, deriv_c, inj_c⟩
  have a_s : a ⊆ s := by rw [← h_union]; exact subset_union_left
  have bc_s : b ∪ c ⊆ s := by rw [← h_union]; exact subset_union_right
  have b_s : b ⊆ s := by rw [← h_union]; exact subset_union_left.trans subset_union_right
  have c_s : c ⊆ s := by rw [← h_union]; exact subset_union_right.trans subset_union_right
  have I : ∫ x in s, f' x • g (f x) = ∫ x in c, f' x • g (f x) := by
    have : ∫ x in a, f' x • g (f x) = 0 :=
      setIntegral_measure_zero _ (a_count.measure_zero volume)
    rw [← h_union, setIntegral_union h_disj (hb.union hc) (H'.mono_set a_s) (H'.mono_set bc_s),
      this, zero_add]
    have : ∫ x in b, f' x • g (f x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx ↦ by simp [deriv_b x hx])
    rw [setIntegral_union h_disj' hc (H'.mono_set b_s) (H'.mono_set c_s), this, zero_add]
  have J : ∫ x in f '' s, g x = ∫ x in f '' c, g x := by
    apply setIntegral_congr_set
    rw [← h_union, image_union, image_union]
    have A : (f '' a ∪ (f '' b ∪ f '' c) : Set ℝ) =ᵐ[volume] (f '' b ∪ f '' c : Set ℝ) := by
      refine union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr ?_)
      exact (a_count.image _).measure_zero _
    have B : (f '' b ∪ f '' c : Set ℝ) =ᵐ[volume] f '' c :=
      union_ae_eq_right_of_ae_eq_empty (ae_eq_empty.mpr (fb_count.measure_zero _))
    exact A.trans B
  rw [I, J]
  let F' : ℝ → (ℝ →L[ℝ] ℝ) := fun x ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' (x : ℝ) (hx : x ∈ c) : HasFDerivWithinAt f (F' x) c x :=
    (hf' x (c_s hx)).hasFDerivWithinAt.mono c_s
  have : ∫ x in c, f' x • g (f x) = ∫ x in c, |(F' x).det| • g (f x) := by
    apply setIntegral_congr_fun hc (fun x hx ↦ ?_)
    simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, one_mul, F']
    rw [abs_of_nonneg (deriv_c x hx)]
  rw [this]
  exact integral_image_eq_integral_abs_det_fderiv_smul _ hc hF' inj_c _

/- Change of variable formula for differentiable functions: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`u : ℝ → ℝ≥0∞` on `f '' s` coincides with the integral of `(-f' x) * u ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_antitoneOn`. -/
theorem lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, u x = ∫⁻ x in s, ENNReal.ofReal (-f' x) * u (f x) := by
  let n : ℝ → ℝ := (fun x ↦ - x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : ∫⁻ x in e '' s, u (n x) = ∫⁻ x in s, ENNReal.ofReal (-f' x) * (u ∘ n) (e x) := by
    rw [← lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hg' hf.neg (u ∘ n)]; rfl
  have B : ∫⁻ x in n '' (e '' s), u x = ∫⁻ x in e '' s, ENNReal.ofReal (|-1|) * u (n x) :=
    lintegral_image_eq_lintegral_abs_deriv_mul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at B
  rw [A, ← image_comp] at B
  convert B using 4 with x hx x <;> simp [n, e]

/-- Change of variable formula for differentiable functions, set version: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `-f' x` on `s` .
Note that the measurability of `f '' s` is given by `MeasurableSet.image_of_antitoneOn`. -/
theorem lintegral_deriv_eq_volume_image_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (-f' x)) = volume (f '' s) := by
  simpa using (lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf 1).symm

/-- Integrability in the change of variable formula for differentiable functions: if a real
function `f` is antitone and differentiable on a measurable set `s`, then a function
`g : ℝ → F` is integrable on `f '' s` if and only if `-f' x • g ∘ f` is integrable on `s` . -/
theorem integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (g : ℝ → F) :
    IntegrableOn g (f '' s) ↔ IntegrableOn (fun x ↦ (-f' x) • g (f x)) s := by
  let n : ℝ → ℝ := (fun x ↦ - x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : IntegrableOn (fun x ↦ g (n x)) (e '' s)
      ↔ IntegrableOn (fun x ↦ (-f' x) • (g ∘ n) (e x)) s := by
    rw [← integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hg' hf.neg (g ∘ n)]; rfl
  have B : IntegrableOn g (n '' (e '' s)) ↔ IntegrableOn (fun x ↦ (|-1| : ℝ) • g (n x)) (e '' s) :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, one_smul] at B
  rw [A, ← image_comp] at B
  convert B using 3 with x hx x <;> simp [n, e]

/-- Change of variable formula for differentiable functions: if a real function `f` is
antitone and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : ℝ → F` on `f '' s` coincides with the integral of `(-f' x) • g ∘ f` on `s` . -/
theorem integral_image_eq_integral_deriv_smul_of_antitone (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : AntitoneOn f s) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, (-f' x) • g (f x) := by
  let n : ℝ → ℝ := (fun x ↦ - x)
  let e := n ∘ f
  have hg' (x) (hx : x ∈ s) : HasDerivWithinAt e (-f' x) s x := (hf' x hx).neg
  have A : ∫ x in e '' s, g (n x) = ∫ x in s, (-f' x) • (g ∘ n) (e x) := by
    rw [← integral_image_eq_integral_deriv_smul_of_monotoneOn hs hg' hf.neg (g ∘ n)]; rfl
  have B : ∫ x in n '' (e '' s), g x = ∫ x in e '' s, (|-1| : ℝ) • g (n x) :=
    integral_image_eq_integral_abs_deriv_smul (hs.image_of_monotoneOn hf.neg)
      (fun x hx ↦ hasDerivWithinAt_neg _ _) neg_injective.injOn _
  simp only [abs_neg, abs_one, one_smul] at B
  rw [A, ← image_comp] at B
  convert B using 3 with x hx x <;> simp [n, e]

section WithDensity

lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [hf.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul volume hs
    hg hf_int hf']
  simp only [det_one_smulRight]

lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f hg hf_int hf']
  simp only [det_one_smulRight]

lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul'
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) :=
  hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul hs
    (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
    (fun x _ => (hf' x).hasDerivWithinAt)

lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
      (fun x _ => (hf' x).hasDerivWithinAt)]
  simp only [det_one_smulRight]

end WithDensity

end MeasureTheory
