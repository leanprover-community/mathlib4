/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Inverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.MeasureTheory.Constructions.Polish

#align_import measure_theory.function.jacobian from "leanprover-community/mathlib"@"b84aee748341da06a6d78491367e2c0e9f15e8a5"

/-!
# Change of variables in higher-dimensional integrals

Let `μ` be a Lebesgue measure on a finite-dimensional real vector space `E`.
Let `f : E → E` be a function which is injective and differentiable on a measurable set `s`,
with derivative `f'`. Then we prove that `f '' s` is measurable, and
its measure is given by the formula `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ` (where `(f' x).det`
is almost everywhere measurable, but not Borel-measurable in general). This formula is proved in
`lintegral_abs_det_fderiv_eq_addHaar_image`. We deduce the change of variables
formula for the Lebesgue and Bochner integrals, in `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
and `integral_image_eq_integral_abs_det_fderiv_smul` respectively.

## Main results

* `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`: if `f` is differentiable on a
  set `s` with zero measure, then `f '' s` also has zero measure.
* `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`: if `f` is differentiable on a set `s`, and
  its derivative is never invertible, then `f '' s` has zero measure (a version of Sard's lemma).
* `aemeasurable_fderivWithin`: if `f` is differentiable on a measurable set `s`, then `f'`
  is almost everywhere measurable on `s`.

For the next statements, `s` is a measurable set and `f` is differentiable on `s`
(with a derivative `f'`) and injective on `s`.

* `measurable_image_of_fderivWithin`: the image `f '' s` is measurable.
* `measurableEmbedding_of_fderivWithin`: the function `s.restrict f` is a measurable embedding.
* `lintegral_abs_det_fderiv_eq_addHaar_image`: the image measure is given by
    `μ (f '' s) = ∫⁻ x in s, |(f' x).det| ∂μ`.
* `lintegral_image_eq_lintegral_abs_det_fderiv_mul`: for `g : E → ℝ≥0∞`, one has
    `∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ`.
* `integral_image_eq_integral_abs_det_fderiv_smul`: for `g : E → F`, one has
    `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`.
* `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`: for `g : E → F`, the function `g` is
  integrable on `f '' s` if and only if `|(f' x).det| • g (f x))` is integrable on `s`.

## Implementation

Typical versions of these results in the literature have much stronger assumptions: `s` would
typically be open, and the derivative `f' x` would depend continuously on `x` and be invertible
everywhere, to have the local inverse theorem at our disposal. The proof strategy under our weaker
assumptions is more involved. We follow [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2].

The first remark is that, if `f` is sufficiently well approximated by a linear map `A` on a set
`s`, then `f` expands the volume of `s` by at least `A.det - ε` and at most `A.det + ε`, where
the closeness condition depends on `A` in a non-explicit way (see `addHaar_image_le_mul_of_det_lt`
and `mul_le_addHaar_image_of_lt_det`). This fact holds for balls by a simple inclusion argument,
and follows for general sets using the Besicovitch covering theorem to cover the set by balls with
measures adding up essentially to `μ s`.

When `f` is differentiable on `s`, one may partition `s` into countably many subsets `s ∩ t n`
(where `t n` is measurable), on each of which `f` is well approximated by a linear map, so that the
above results apply. See `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, which
follows from the pointwise differentiability (in a non-completely trivial way, as one should ensure
a form of uniformity on the sets of the partition).

Combining the above two results would give the conclusion, except for two difficulties: it is not
obvious why `f '' s` and `f'` should be measurable, which prevents us from using countable
additivity for the measure and the integral. It turns out that `f '' s` is indeed measurable,
and that `f'` is almost everywhere measurable, which is enough to recover countable additivity.

The measurability of `f '' s` follows from the deep Lusin-Souslin theorem ensuring that, in a
Polish space, a continuous injective image of a measurable set is measurable.

The key point to check the almost everywhere measurability of `f'` is that, if `f` is approximated
up to `δ` by a linear map on a set `s`, then `f'` is within `δ` of `A` on a full measure subset
of `s` (namely, its density points). With the above approximation argument, it follows that `f'`
is the almost everywhere limit of a sequence of measurable functions (which are constant on the
pieces of the good discretization), and is therefore almost everywhere measurable.

## Tags
Change of variables in integrals

## References
[Fremlin, *Measure Theory* (volume 2)][fremlin_vol2]
-/


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open MeasureTheory MeasureTheory.Measure Metric Filter Set FiniteDimensional Asymptotics
  TopologicalSpace

open scoped NNReal ENNReal Topology Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}

/-!
### Decomposition lemmas

We state lemmas ensuring that a differentiable function can be approximated, on countably many
measurable pieces, by linear maps (with a prescribed precision depending on the linear map).
-/

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may cover `s`
with countably many closed sets `t n` on which `f` is well approximated by linear maps `A n`. -/
theorem exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      (∀ n, IsClosed (t n)) ∧
        (s ⊆ ⋃ n, t n) ∧
          (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
            (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
    close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
    enough to `x`, say on a ball of radius `r` (or even `u n` for some `n`, where `u` is a fixed
    sequence tending to `0`).
    Let `M n z` be the points where this happens. Then this set is relatively closed inside `s`,
    and moreover in every closed ball of radius `u n / 3` inside it the map is well approximated by
    `f' z`. Using countably many closed balls to split `M n z` into small diameter subsets
    `K n z p`, one obtains the desired sets `t q` after reindexing.
    -/
  -- exclude the trivial case where `s` is empty
  rcases eq_empty_or_nonempty s with (rfl | hs)
  -- ⊢ ∃ t A, (∀ (n : ℕ), IsClosed (t n)) ∧ ∅ ⊆ ⋃ (n : ℕ), t n ∧ (∀ (n : ℕ), Approx …
  · refine' ⟨fun _ => ∅, fun _ => 0, _, _, _, _⟩ <;> simp
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
  -- we will use countably many linear maps. Select these from all the derivatives since the
  -- space of linear maps is second-countable
  obtain ⟨T, T_count, hT⟩ :
    ∃ T : Set s,
      T.Countable ∧ ⋃ x ∈ T, ball (f' (x : E)) (r (f' x)) = ⋃ x : s, ball (f' x) (r (f' x)) :=
    TopologicalSpace.isOpen_iUnion_countable _ fun x => isOpen_ball
  -- fix a sequence `u` of positive reals tending to zero.
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  -- `M n z` is the set of points `x` such that `f y - f x` is close to `f' z (y - x)` for `y`
  -- in the ball of radius `u n` around `x`.
  let M : ℕ → T → Set E := fun n z =>
    {x | x ∈ s ∧ ∀ y ∈ s ∩ ball x (u n), ‖f y - f x - f' z (y - x)‖ ≤ r (f' z) * ‖y - x‖}
  -- As `f` is differentiable everywhere on `s`, the sets `M n z` cover `s` by design.
  have s_subset : ∀ x ∈ s, ∃ (n : ℕ) (z : T), x ∈ M n z := by
    intro x xs
    obtain ⟨z, zT, hz⟩ : ∃ z ∈ T, f' x ∈ ball (f' (z : E)) (r (f' z)) := by
      have : f' x ∈ ⋃ z ∈ T, ball (f' (z : E)) (r (f' z)) := by
        rw [hT]
        refine' mem_iUnion.2 ⟨⟨x, xs⟩, _⟩
        simpa only [mem_ball, Subtype.coe_mk, dist_self] using (rpos (f' x)).bot_lt
      rwa [mem_iUnion₂, bex_def] at this
    obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ‖f' x - f' z‖ + ε ≤ r (f' z) := by
      refine' ⟨r (f' z) - ‖f' x - f' z‖, _, le_of_eq (by abel)⟩
      simpa only [sub_pos] using mem_ball_iff_norm.mp hz
    obtain ⟨δ, δpos, hδ⟩ :
      ∃ (δ : ℝ), 0 < δ ∧ ball x δ ∩ s ⊆ {y | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 (IsLittleO.def (hf' x xs) εpos)
    obtain ⟨n, hn⟩ : ∃ n, u n < δ := ((tendsto_order.1 u_lim).2 _ δpos).exists
    refine' ⟨n, ⟨z, zT⟩, ⟨xs, _⟩⟩
    intro y hy
    calc
      ‖f y - f x - (f' z) (y - x)‖ = ‖f y - f x - (f' x) (y - x) + (f' x - f' z) (y - x)‖ := by
        congr 1
        simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖f y - f x - (f' x) (y - x)‖ + ‖(f' x - f' z) (y - x)‖ := (norm_add_le _ _)
      _ ≤ ε * ‖y - x‖ + ‖f' x - f' z‖ * ‖y - x‖ := by
        refine' add_le_add (hδ _) (ContinuousLinearMap.le_op_norm _ _)
        rw [inter_comm]
        exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy
      _ ≤ r (f' z) * ‖y - x‖ := by
        rw [← add_mul, add_comm]
        exact mul_le_mul_of_nonneg_right hε (norm_nonneg _)
  -- the sets `M n z` are relatively closed in `s`, as all the conditions defining it are clearly
  -- closed
  have closure_M_subset : ∀ n z, s ∩ closure (M n z) ⊆ M n z := by
    rintro n z x ⟨xs, hx⟩
    refine' ⟨xs, fun y hy => _⟩
    obtain ⟨a, aM, a_lim⟩ : ∃ a : ℕ → E, (∀ k, a k ∈ M n z) ∧ Tendsto a atTop (𝓝 x) :=
      mem_closure_iff_seq_limit.1 hx
    have L1 :
      Tendsto (fun k : ℕ => ‖f y - f (a k) - (f' z) (y - a k)‖) atTop
        (𝓝 ‖f y - f x - (f' z) (y - x)‖) := by
      apply Tendsto.norm
      have L : Tendsto (fun k => f (a k)) atTop (𝓝 (f x)) := by
        apply (hf' x xs).continuousWithinAt.tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ a_lim
        exact eventually_of_forall fun k => (aM k).1
      apply Tendsto.sub (tendsto_const_nhds.sub L)
      exact ((f' z).continuous.tendsto _).comp (tendsto_const_nhds.sub a_lim)
    have L2 : Tendsto (fun k : ℕ => (r (f' z) : ℝ) * ‖y - a k‖) atTop (𝓝 (r (f' z) * ‖y - x‖)) :=
      (tendsto_const_nhds.sub a_lim).norm.const_mul _
    have I : ∀ᶠ k in atTop, ‖f y - f (a k) - (f' z) (y - a k)‖ ≤ r (f' z) * ‖y - a k‖ := by
      have L : Tendsto (fun k => dist y (a k)) atTop (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist a_lim
      filter_upwards [(tendsto_order.1 L).2 _ hy.2]
      intro k hk
      exact (aM k).2 y ⟨hy.1, hk⟩
    exact le_of_tendsto_of_tendsto L1 L2 I
  -- choose a dense sequence `d p`
  rcases TopologicalSpace.exists_dense_seq E with ⟨d, hd⟩
  -- ⊢ ∃ t A, (∀ (n : ℕ), IsClosed (t n)) ∧ s ⊆ ⋃ (n : ℕ), t n ∧ (∀ (n : ℕ), Approx …
  -- split `M n z` into subsets `K n z p` of small diameters by intersecting with the ball
  -- `closedBall (d p) (u n / 3)`.
  let K : ℕ → T → ℕ → Set E := fun n z p => closure (M n z) ∩ closedBall (d p) (u n / 3)
  -- ⊢ ∃ t A, (∀ (n : ℕ), IsClosed (t n)) ∧ s ⊆ ⋃ (n : ℕ), t n ∧ (∀ (n : ℕ), Approx …
  -- on the sets `K n z p`, the map `f` is well approximated by `f' z` by design.
  have K_approx : ∀ (n) (z : T) (p), ApproximatesLinearOn f (f' z) (s ∩ K n z p) (r (f' z)) := by
    intro n z p x hx y hy
    have yM : y ∈ M n z := closure_M_subset _ _ ⟨hy.1, hy.2.1⟩
    refine' yM.2 _ ⟨hx.1, _⟩
    calc
      dist x y ≤ dist x (d p) + dist y (d p) := dist_triangle_right _ _ _
      _ ≤ u n / 3 + u n / 3 := (add_le_add hx.2.2 hy.2.2)
      _ < u n := by linarith [u_pos n]
  -- the sets `K n z p` are also closed, again by design.
  have K_closed : ∀ (n) (z : T) (p), IsClosed (K n z p) := fun n z p =>
    isClosed_closure.inter isClosed_ball
  -- reindex the sets `K n z p`, to let them only depend on an integer parameter `q`.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ × T × ℕ, Function.Surjective F := by
    haveI : Encodable T := T_count.toEncodable
    have : Nonempty T := by
      rcases eq_empty_or_nonempty T with (rfl | hT)
      · rcases hs with ⟨x, xs⟩
        rcases s_subset x xs with ⟨n, z, _⟩
        exact False.elim z.2
      · exact hT.coe_sort
    inhabit ↥T
    exact ⟨_, Encodable.surjective_decode_iget (ℕ × T × ℕ)⟩
  -- these sets `t q = K n z p` will do
  refine'
    ⟨fun q => K (F q).1 (F q).2.1 (F q).2.2, fun q => f' (F q).2.1, fun n => K_closed _ _ _,
      fun x xs => _, fun q => K_approx _ _ _, fun _ q => ⟨(F q).2.1, (F q).2.1.1.2, rfl⟩⟩
  -- the only fact that needs further checking is that they cover `s`.
  -- we already know that any point `x ∈ s` belongs to a set `M n z`.
  obtain ⟨n, z, hnz⟩ : ∃ (n : ℕ) (z : T), x ∈ M n z := s_subset x xs
  -- ⊢ x ∈ ⋃ (n : ℕ), (fun q => K (F q).fst (F q).snd.fst (F q).snd.snd) n
  -- by density, it also belongs to a ball `closedBall (d p) (u n / 3)`.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, x ∈ closedBall (d p) (u n / 3) := by
    have : Set.Nonempty (ball x (u n / 3)) := by simp only [nonempty_ball]; linarith [u_pos n]
    obtain ⟨p, hp⟩ : ∃ p : ℕ, d p ∈ ball x (u n / 3) := hd.exists_mem_open isOpen_ball this
    exact ⟨p, (mem_ball'.1 hp).le⟩
  -- choose `q` for which `t q = K n z p`.
  obtain ⟨q, hq⟩ : ∃ q, F q = (n, z, p) := hF _
  -- ⊢ x ∈ ⋃ (n : ℕ), (fun q => K (F q).fst (F q).snd.fst (F q).snd.snd) n
  -- then `x` belongs to `t q`.
  apply mem_iUnion.2 ⟨q, _⟩
  -- ⊢ x ∈ (fun q => K (F q).fst (F q).snd.fst (F q).snd.snd) q
  simp (config := { zeta := false }) only [hq, subset_closure hnz, hp, mem_inter_iff, and_true, hnz]
  -- 🎉 no goals
#align exists_closed_cover_approximates_linear_on_of_has_fderiv_within_at exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may
partition `s` into countably many disjoint relatively measurable sets (i.e., intersections
of `s` with measurable sets `t n`) on which `f` is well approximated by linear maps `A n`. -/
theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n, t n) ∧
            (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine'
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, _, _, ht⟩
  · rw [iUnion_disjointed]; exact st
    -- ⊢ s ⊆ ⋃ (n : ℕ), t n
                            -- 🎉 no goals
  · intro n; exact (t_approx n).mono_set (inter_subset_inter_right _ (disjointed_subset _ _))
    -- ⊢ ApproximatesLinearOn f (A n) (s ∩ disjointed t n) (r (A n))
             -- 🎉 no goals
#align exists_partition_approximates_linear_on_of_has_fderiv_within_at exists_partition_approximatesLinearOn_of_hasFDerivWithinAt

namespace MeasureTheory

/-!
### Local lemmas

We check that a function which is well enough approximated by a linear map expands the volume
essentially like this linear map, and that its derivative (if it exists) is almost everywhere close
to the approximating linear map.
-/


/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at most `m` for any `m > det A`. -/
theorem addHaar_image_le_mul_of_det_lt (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : ENNReal.ofReal |A.det| < m) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → μ (f '' s) ≤ m * μ s := by
  apply nhdsWithin_le_nhds
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑↑μ …
  let d := ENNReal.ofReal |A.det|
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑↑μ …
  -- construct a small neighborhood of `A '' (closedBall 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ :
    ∃ ε : ℝ, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 < ε := by
    have HC : IsCompact (A '' closedBall 0 1) :=
      (ProperSpace.isCompact_closedBall _ _).image A.continuous
    have L0 :
      Tendsto (fun ε => μ (cthickening ε (A '' closedBall 0 1))) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact tendsto_measure_cthickening_of_isCompact HC
    have L1 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply L0.congr' _
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [← HC.add_closedBall_zero (le_of_lt hr), add_comm]
    have L2 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (d * μ (closedBall 0 1))) := by
      convert L1
      exact (addHaar_image_continuousLinearMap _ _ _).symm
    have I : d * μ (closedBall 0 1) < m * μ (closedBall 0 1) :=
      (ENNReal.mul_lt_mul_right (measure_closedBall_pos μ _ zero_lt_one).ne'
            measure_closedBall_lt_top.ne).2
        hm
    have H :
      ∀ᶠ b : ℝ in 𝓝[>] 0, μ (closedBall 0 b + A '' closedBall 0 1) < m * μ (closedBall 0 1) :=
      (tendsto_order.1 L2).2 _ I
    exact (H.and self_mem_nhdsWithin).exists
  have : Iio (⟨ε, εpos.le⟩ : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0) := by apply Iio_mem_nhds; exact εpos
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑↑μ …
  filter_upwards [this]
  -- ⊢ ∀ (a : ℝ≥0), a ∈ Iio { val := ε, property := (_ : 0 ≤ ε) } → ∀ (s : Set E) ( …
  -- fix a function `f` which is close enough to `A`.
  intro δ hδ s f hf
  -- ⊢ ↑↑μ (f '' s) ≤ ↑m * ↑↑μ s
  -- This function expands the volume of any ball by at most `m`
  have I : ∀ x r, x ∈ s → 0 ≤ r → μ (f '' (s ∩ closedBall x r)) ≤ m * μ (closedBall x r) := by
    intro x r xs r0
    have K : f '' (s ∩ closedBall x r) ⊆ A '' closedBall 0 r + closedBall (f x) (ε * r) := by
      rintro y ⟨z, ⟨zs, zr⟩, rfl⟩
      apply Set.mem_add.2 ⟨A (z - x), f z - f x - A (z - x) + f x, _, _, _⟩
      · apply mem_image_of_mem
        simpa only [dist_eq_norm, mem_closedBall, mem_closedBall_zero_iff, sub_zero] using zr
      · rw [mem_closedBall_iff_norm, add_sub_cancel]
        calc
          ‖f z - f x - A (z - x)‖ ≤ δ * ‖z - x‖ := hf _ zs _ xs
          _ ≤ ε * r :=
            mul_le_mul (le_of_lt hδ) (mem_closedBall_iff_norm.1 zr) (norm_nonneg _) εpos.le
      · simp only [map_sub, Pi.sub_apply]
        abel
    have :
      A '' closedBall 0 r + closedBall (f x) (ε * r) =
        {f x} + r • (A '' closedBall 0 1 + closedBall 0 ε) := by
      rw [smul_add, ← add_assoc, add_comm {f x}, add_assoc, smul_closedBall _ _ εpos.le, smul_zero,
        singleton_add_closedBall_zero, ← image_smul_set ℝ E E A, smul_closedBall _ _ zero_le_one,
        smul_zero, Real.norm_eq_abs, abs_of_nonneg r0, mul_one, mul_comm]
    rw [this] at K
    calc
      μ (f '' (s ∩ closedBall x r)) ≤ μ ({f x} + r • (A '' closedBall 0 1 + closedBall 0 ε)) :=
        measure_mono K
      _ = ENNReal.ofReal (r ^ finrank ℝ E) * μ (A '' closedBall 0 1 + closedBall 0 ε) := by
        simp only [abs_of_nonneg r0, addHaar_smul, image_add_left, abs_pow, singleton_add,
          measure_preimage_add]
      _ ≤ ENNReal.ofReal (r ^ finrank ℝ E) * (m * μ (closedBall 0 1)) := by
        rw [add_comm]; exact mul_le_mul_left' hε.le _
      _ = m * μ (closedBall x r) := by simp only [addHaar_closedBall' μ _ r0]; ring
  -- covering `s` by closed balls with total measure very close to `μ s`, one deduces that the
  -- measure of `f '' s` is at most `m * (μ s + a)` for any positive `a`.
  have J : ∀ᶠ a in 𝓝[>] (0 : ℝ≥0∞), μ (f '' s) ≤ m * (μ s + a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    change 0 < a at ha
    obtain ⟨t, r, t_count, ts, rpos, st, μt⟩ :
      ∃ (t : Set E) (r : E → ℝ),
        t.Countable ∧
          t ⊆ s ∧
            (∀ x : E, x ∈ t → 0 < r x) ∧
              (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧
                (∑' x : ↥t, μ (closedBall (↑x) (r ↑x))) ≤ μ s + a :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le μ ha.ne' (fun _ => Ioi 0) s
        fun x _ δ δpos => ⟨δ / 2, by simp [half_pos δpos, δpos]⟩
    haveI : Encodable t := t_count.toEncodable
    calc
      μ (f '' s) ≤ μ (⋃ x : t, f '' (s ∩ closedBall x (r x))) := by
        rw [biUnion_eq_iUnion] at st
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact image_subset _ (subset_inter (Subset.refl _) st)
      _ ≤ ∑' x : t, μ (f '' (s ∩ closedBall x (r x))) := (measure_iUnion_le _)
      _ ≤ ∑' x : t, m * μ (closedBall x (r x)) :=
        (ENNReal.tsum_le_tsum fun x => I x (r x) (ts x.2) (rpos x x.2).le)
      _ ≤ m * (μ s + a) := by rw [ENNReal.tsum_mul_left]; exact mul_le_mul_left' μt _
  -- taking the limit in `a`, one obtains the conclusion
  have L : Tendsto (fun a => (m : ℝ≥0∞) * (μ s + a)) (𝓝[>] 0) (𝓝 (m * (μ s + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ENNReal.Tendsto.const_mul (tendsto_const_nhds.add tendsto_id)
    simp only [ENNReal.coe_ne_top, Ne.def, or_true_iff, not_false_iff]
  rw [add_zero] at L
  -- ⊢ ↑↑μ (f '' s) ≤ ↑m * ↑↑μ s
  exact ge_of_tendsto L J
  -- 🎉 no goals
#align measure_theory.add_haar_image_le_mul_of_det_lt MeasureTheory.addHaar_image_le_mul_of_det_lt

/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at least `m` for any `m < det A`. -/
theorem mul_le_addHaar_image_of_lt_det (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : (m : ℝ≥0∞) < ENNReal.ofReal |A.det|) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → (m : ℝ≥0∞) * μ s ≤ μ (f '' s) := by
  apply nhdsWithin_le_nhds
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑m  …
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `addHaar_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the trivial case where `m = 0`.
  rcases eq_or_lt_of_le (zero_le m) with (rfl | mpos)
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑0  …
  · apply eventually_of_forall
    -- ⊢ ∀ (x : ℝ≥0) (s : Set E) (f : E → E), ApproximatesLinearOn f A s x → ↑0 * ↑↑μ …
    simp only [forall_const, zero_mul, imp_true_iff, zero_le, ENNReal.coe_zero]
    -- 🎉 no goals
  have hA : A.det ≠ 0 := by
    intro h; simp only [h, ENNReal.not_lt_zero, ENNReal.ofReal_zero, abs_zero] at hm
  -- let `B` be the continuous linear equiv version of `A`.
  let B := A.toContinuousLinearEquivOfDetNeZero hA
  -- ⊢ {x | (fun δ => ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → ↑m  …
  -- the determinant of `B.symm` is bounded by `m⁻¹`
  have I : ENNReal.ofReal |(B.symm : E →L[ℝ] E).det| < (m⁻¹ : ℝ≥0) := by
    simp only [ENNReal.ofReal, abs_inv, Real.toNNReal_inv, ContinuousLinearEquiv.det_coe_symm,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, ENNReal.coe_lt_coe] at hm ⊢
    exact NNReal.inv_lt_inv mpos.ne' hm
  -- therefore, we may apply `addHaar_image_le_mul_of_det_lt` to `B.symm` and `m⁻¹`.
  obtain ⟨δ₀, δ₀pos, hδ₀⟩ :
    ∃ δ : ℝ≥0,
      0 < δ ∧
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t := by
    have :
      ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0,
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t :=
      addHaar_image_le_mul_of_det_lt μ B.symm I
    rcases(this.and self_mem_nhdsWithin).exists with ⟨δ₀, h, h'⟩
    exact ⟨δ₀, h', h⟩
  -- record smallness conditions for `δ` that will be needed to apply `hδ₀` below.
  have L1 : ∀ᶠ δ in 𝓝 (0 : ℝ≥0), Subsingleton E ∨ δ < ‖(B.symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases Subsingleton E
    · simp only [h, true_or_iff, eventually_const]
    simp only [h, false_or_iff]
    apply Iio_mem_nhds
    simpa only [h, false_or_iff, inv_pos] using B.subsingleton_or_nnnorm_symm_pos
  have L2 :
    ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ < δ₀ := by
    have :
      Tendsto (fun δ => ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ) (𝓝 0)
        (𝓝 (‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - 0)⁻¹ * 0)) := by
      rcases eq_or_ne ‖(B.symm : E →L[ℝ] E)‖₊ 0 with (H | H)
      · simpa only [H, zero_mul] using tendsto_const_nhds
      refine' Tendsto.mul (tendsto_const_nhds.mul _) tendsto_id
      refine' (Tendsto.sub tendsto_const_nhds tendsto_id).inv₀ _
      simpa only [tsub_zero, inv_eq_zero, Ne.def] using H
    simp only [mul_zero] at this
    exact (tendsto_order.1 this).2 δ₀ δ₀pos
  -- let `δ` be small enough, and `f` approximated by `B` up to `δ`.
  filter_upwards [L1, L2]
  -- ⊢ ∀ (a : ℝ≥0), Subsingleton E ∨ a < ‖↑(ContinuousLinearEquiv.symm (ContinuousL …
  intro δ h1δ h2δ s f hf
  -- ⊢ ↑m * ↑↑μ s ≤ ↑↑μ (f '' s)
  have hf' : ApproximatesLinearOn f (B : E →L[ℝ] E) s δ := by convert hf
  -- ⊢ ↑m * ↑↑μ s ≤ ↑↑μ (f '' s)
  let F := hf'.toLocalEquiv h1δ
  -- ⊢ ↑m * ↑↑μ s ≤ ↑↑μ (f '' s)
  -- the condition to be checked can be reformulated in terms of the inverse maps
  suffices H : μ (F.symm '' F.target) ≤ (m⁻¹ : ℝ≥0) * μ F.target
  -- ⊢ ↑m * ↑↑μ s ≤ ↑↑μ (f '' s)
  · change (m : ℝ≥0∞) * μ F.source ≤ μ F.target
    -- ⊢ ↑m * ↑↑μ F.source ≤ ↑↑μ F.target
    rwa [← F.symm_image_target_eq_source, mul_comm, ← ENNReal.le_div_iff_mul_le, div_eq_mul_inv,
      mul_comm, ← ENNReal.coe_inv mpos.ne']
    · apply Or.inl
      -- ⊢ ↑m ≠ 0
      simpa only [ENNReal.coe_eq_zero, Ne.def] using mpos.ne'
      -- 🎉 no goals
    · simp only [ENNReal.coe_ne_top, true_or_iff, Ne.def, not_false_iff]
      -- 🎉 no goals
  -- as `f⁻¹` is well approximated by `B⁻¹`, the conclusion follows from `hδ₀`
  -- and our choice of `δ`.
  exact hδ₀ _ _ ((hf'.to_inv h1δ).mono_num h2δ.le)
  -- 🎉 no goals
#align measure_theory.mul_le_add_haar_image_of_lt_det MeasureTheory.mul_le_addHaar_image_of_lt_det

/-- If a differentiable function `f` is approximated by a linear map `A` on a set `s`, up to `δ`,
then at almost every `x` in `s` one has `‖f' x - A‖ ≤ δ`. -/
theorem _root_.ApproximatesLinearOn.norm_fderiv_sub_le {A : E →L[ℝ] E} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s) (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : ∀ᵐ x ∂μ.restrict s, ‖f' x - A‖₊ ≤ δ := by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x (r z)` (by differentiability) and to `A (r z)`
    (by linear approximation), so these two quantities are close, i.e., `(f' x - A) z` is small. -/
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs]
  -- ⊢ ∀ (a : E), Tendsto (fun r => ↑↑μ (s ∩ closedBall a r) / ↑↑μ (closedBall a r) …
  -- start from a Lebesgue density point `x`, belonging to `s`.
  intro x hx xs
  -- ⊢ ‖f' x - A‖₊ ≤ δ
  -- consider an arbitrary vector `z`.
  apply ContinuousLinearMap.op_norm_le_bound _ δ.2 fun z => ?_
  -- ⊢ ‖↑(f' x - A) z‖ ≤ ↑δ * ‖z‖
  -- to show that `‖(f' x - A) z‖ ≤ δ ‖z‖`, it suffices to do it up to some error that vanishes
  -- asymptotically in terms of `ε > 0`.
  suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε
  -- ⊢ ‖↑(f' x - A) z‖ ≤ ↑δ * ‖z‖
  · have :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by continuity) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    -- ⊢ ‖↑(f' x - A) z‖ ≤ ↑δ * ‖z‖
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    -- ⊢ (fun x_1 => ‖↑(f' x - A) z‖) ≤ᶠ[𝓝[Ioi 0] 0] fun ε => (↑δ + ε) * (‖z‖ + ε) +  …
    filter_upwards [self_mem_nhdsWithin]
    -- ⊢ ∀ (a : ℝ), a ∈ Ioi 0 → ‖↑(f' x - A) z‖ ≤ (↑δ + a) * (‖z‖ + a) + ‖f' x - A‖ * a
    exact H
    -- 🎉 no goals
  -- fix a positive `ε`.
  intro ε εpos
  -- ⊢ ‖↑(f' x - A) z‖ ≤ (↑δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` intersects `s`, as `x` is a
  -- density point
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 (IsLittleO.def (hf' x xs) εpos)
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` is included in the set where
  -- `f y - f x` is well approximated by `f' x (y - x)`.
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset bounded_closedBall (ball_mem_nhds x ρpos)
  -- fix a small positive `r` satisfying the above properties, as well as a corresponding `y`.
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    ∃ r : ℝ,
      (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  -- write `y = x + r a` with `a ∈ closedBall z ε`.
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel'_right]
      _ ≤ ‖z‖ + ‖a - z‖ := (norm_add_le _ _)
      _ ≤ ‖z‖ + ε := add_le_add_left (mem_closedBall_iff_norm.1 az) _
  -- use the approximation properties to control `(f' x - A) a`, and then `(f' x - A) z` as `z` is
  -- close to `a`.
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [ContinuousLinearMap.map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        congr 1
        simp only [ya, add_sub_cancel', sub_sub_sub_cancel_left, ContinuousLinearMap.coe_sub',
          eq_self_iff_true, sub_left_inj, Pi.sub_apply, ContinuousLinearMap.map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := (norm_sub_le _ _)
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel', norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) :=
        mul_le_mul_of_nonneg_left norm_a (mul_nonneg rpos.le (add_nonneg δ.2 εpos.le))
  show ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε;
  -- ⊢ ‖↑(f' x - A) z‖ ≤ (↑δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε
  exact
    calc
      ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
        congr 1
        simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := (norm_add_le _ _)
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at I; exact (mul_le_mul_left rpos).1 I
        · apply ContinuousLinearMap.le_op_norm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm'.1 az) (norm_nonneg _))
#align approximates_linear_on.norm_fderiv_sub_le ApproximatesLinearOn.norm_fderiv_sub_le

/-!
### Measure zero of the image, over non-measurable sets

If a set has measure `0`, then its image under a differentiable map has measure zero. This doesn't
require the set to be measurable. In the same way, if `f` is differentiable on a set `s` with
non-invertible derivative everywhere, then `f '' s` has measure `0`, again without measurability
assumptions.
-/


/-- A differentiable function maps sets of measure zero to sets of measure zero. -/
theorem addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : DifferentiableOn ℝ f s)
    (hs : μ s = 0) : μ (f '' s) = 0 := by
  refine' le_antisymm _ (zero_le _)
  -- ⊢ ↑↑μ (f '' s) ≤ 0
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + 1 : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + 1
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [ENNReal.ofReal, lt_add_iff_pos_right, zero_lt_one, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  -- ⊢ ↑↑μ (f '' s) ≤ 0
  obtain ⟨t, A, _, _, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = fderivWithin ℝ f s y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderivWithin ℝ f s)
      (fun x xs => (hf x xs).hasFDerivWithinAt) δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_subset f (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := (measure_iUnion_le _)
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + 1 : ℝ≥0) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2
      exact ht n
    _ ≤ ∑' n, ((Real.toNNReal |(A n).det| + 1 : ℝ≥0) : ℝ≥0∞) * 0 := by
      refine' ENNReal.tsum_le_tsum fun n => mul_le_mul_left' _ _
      exact le_trans (measure_mono (inter_subset_left _ _)) (le_of_eq hs)
    _ = 0 := by simp only [tsum_zero, mul_zero]
#align measure_theory.add_haar_image_eq_zero_of_differentiable_on_of_add_haar_eq_zero MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero

/-- A version of Sard lemma in fixed dimension: given a differentiable function from `E` to `E` and
a set where the differential is not invertible, then the image of this set has zero measure.
Here, we give an auxiliary statement towards this result. -/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (R : ℝ) (hs : s ⊆ closedBall 0 R) (ε : ℝ≥0)
    (εpos : 0 < ε) (h'f' : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) ≤ ε * μ (closedBall 0 R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  -- ⊢ ↑↑μ (f '' ∅) ≤ ↑ε * ↑↑μ (closedBall 0 R)
                                                    -- 🎉 no goals
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + ε : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  -- ⊢ ↑↑μ (f '' s) ≤ ↑ε * ↑↑μ (closedBall 0 R)
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_subset f (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := (measure_iUnion_le _)
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + ε : ℝ≥0) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2
      exact ht n
    _ = ∑' n, ε * μ (s ∩ t n) := by
      congr with n
      rcases Af' h's n with ⟨y, ys, hy⟩
      simp only [hy, h'f' y ys, Real.toNNReal_zero, abs_zero, zero_add]
    _ ≤ ε * ∑' n, μ (closedBall 0 R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      refine' mul_le_mul_left' (ENNReal.tsum_le_tsum fun n => measure_mono _) _
      exact inter_subset_inter_left _ hs
    _ = ε * μ (⋃ n, closedBall 0 R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right _ _
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * μ (closedBall 0 R) := by
      rw [← inter_iUnion]
      exact mul_le_mul_left' (measure_mono (inter_subset_left _ _)) _
#align measure_theory.add_haar_image_eq_zero_of_det_fderiv_within_eq_zero_aux MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux

/-- A version of Sard lemma in fixed dimension: given a differentiable function from `E` to `E` and
a set where the differential is not invertible, then the image of this set has zero measure. -/
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (h'f' : ∀ x ∈ s, (f' x).det = 0) :
    μ (f '' s) = 0 := by
  suffices H : ∀ R, μ (f '' (s ∩ closedBall 0 R)) = 0
  -- ⊢ ↑↑μ (f '' s) = 0
  · apply le_antisymm _ (zero_le _)
    -- ⊢ ↑↑μ (f '' s) ≤ 0
    rw [← iUnion_inter_closedBall_nat s 0]
    -- ⊢ ↑↑μ (f '' ⋃ (n : ℕ), s ∩ closedBall 0 ↑n) ≤ 0
    calc
      μ (f '' ⋃ n : ℕ, s ∩ closedBall 0 n) ≤ ∑' n : ℕ, μ (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
  intro R
  -- ⊢ ↑↑μ (f '' (s ∩ closedBall 0 R)) = 0
  have A : ∀ (ε : ℝ≥0), 0 < ε → μ (f '' (s ∩ closedBall 0 R)) ≤ ε * μ (closedBall 0 R) :=
    fun ε εpos =>
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux μ
      (fun x hx => (hf' x hx.1).mono (inter_subset_left _ _)) R (inter_subset_right _ _) ε εpos
      fun x hx => h'f' x hx.1
  have B : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have :
      Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * μ (closedBall 0 R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  apply le_antisymm _ (zero_le _)
  -- ⊢ ↑↑μ (f '' (s ∩ closedBall 0 R)) ≤ 0
  apply ge_of_tendsto B
  -- ⊢ ∀ᶠ (c : ℝ≥0) in 𝓝[Ioi 0] 0, ↑↑μ (f '' (s ∩ closedBall 0 R)) ≤ ↑c * ↑↑μ (clos …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ≥0), a ∈ Ioi 0 → ↑↑μ (f '' (s ∩ closedBall 0 R)) ≤ ↑a * ↑↑μ (closedB …
  exact A
  -- 🎉 no goals
#align measure_theory.add_haar_image_eq_zero_of_det_fderiv_within_eq_zero MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero

/-!
### Weak measurability statements

We show that the derivative of a function on a set is almost everywhere measurable, and that the
image `f '' s` is measurable if `f` is injective on `s`. The latter statement follows from the
Lusin-Souslin theorem.
-/


/-- The derivative of a function on a measurable set is almost everywhere measurable on this set
with respect to Lebesgue measure. Note that, in general, it is not genuinely measurable there,
as `f'` is not unique (but only on a set of measure `0`, as the argument shows). -/
theorem aemeasurable_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable f' (μ.restrict s) := by
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
    Fix `ε > 0`. Thanks to `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, one
    can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
    approximated by linear maps `A n`. On almost all of `s ∩ t n`, it follows from
    `ApproximatesLinearOn.norm_fderiv_sub_le` that `f'` is uniformly approximated by `A n`, which
    gives the conclusion. -/
  -- fix a precision `ε`
  refine' aemeasurable_of_unif_approx fun ε εpos => _
  -- ⊢ ∃ f, AEMeasurable f ∧ ∀ᵐ (x : E) ∂Measure.restrict μ s, dist (f x) (f' x) ≤ ε
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  -- ⊢ ∃ f, AEMeasurable f ∧ ∀ᵐ (x : E) ∂Measure.restrict μ s, dist (f x) (f' x) ≤ ε
  have δpos : 0 < δ := εpos
  -- ⊢ ∃ f, AEMeasurable f ∧ ∀ᵐ (x : E) ∂Measure.restrict μ s, dist (f x) (f' x) ≤ ε
  -- partition `s` into sets `s ∩ t n` on which `f` is approximated by linear maps `A n`.
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, _⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) δ) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' (fun _ => δ) fun _ =>
      δpos.ne'
  -- define a measurable function `g` which coincides with `A n` on `t n`.
  obtain ⟨g, g_meas, hg⟩ :
      ∃ g : E → E →L[ℝ] E, Measurable g ∧ ∀ (n : ℕ) (x : E), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const) <|
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine' ⟨g, g_meas.aemeasurable, _⟩
  -- ⊢ ∀ᵐ (x : E) ∂Measure.restrict μ s, dist (g x) (f' x) ≤ ε
  -- reduce to checking that `f'` and `g` are close on almost all of `s ∩ t n`, for all `n`.
  suffices H : ∀ᵐ x : E ∂sum fun n => μ.restrict (s ∩ t n), dist (g x) (f' x) ≤ ε
  -- ⊢ ∀ᵐ (x : E) ∂Measure.restrict μ s, dist (g x) (f' x) ≤ ε
  · have : μ.restrict s ≤ sum fun n => μ.restrict (s ∩ t n) := by
      have : s = ⋃ n, s ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) (inter_subset_left _ _)
      conv_lhs => rw [this]
      exact restrict_iUnion_le
    exact ae_mono this H
    -- 🎉 no goals
  -- fix such an `n`.
  refine' ae_sum_iff.2 fun n => _
  -- ⊢ ∀ᵐ (x : E) ∂Measure.restrict μ (s ∩ t n), dist (g x) (f' x) ≤ ε
  -- on almost all `s ∩ t n`, `f' x` is close to `A n` thanks to
  -- `ApproximatesLinearOn.norm_fderiv_sub_le`.
  have E₁ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), ‖f' x - A n‖₊ ≤ δ :=
    (ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
      (hf' x hx.1).mono (inter_subset_left _ _)
  -- moreover, `g x` is equal to `A n` there.
  have E₂ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), g x = A n := by
    suffices H : ∀ᵐ x : E ∂μ.restrict (t n), g x = A n
    exact ae_mono (restrict_mono (inter_subset_right _ _) le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  -- putting these two properties together gives the conclusion.
  filter_upwards [E₁, E₂] with x hx1 hx2
  -- ⊢ dist (g x) (f' x) ≤ ε
  rw [← nndist_eq_nnnorm] at hx1
  -- ⊢ dist (g x) (f' x) ≤ ε
  rw [hx2, dist_comm]
  -- ⊢ dist (f' x) (A n) ≤ ε
  exact hx1
  -- 🎉 no goals
#align measure_theory.ae_measurable_fderiv_within MeasureTheory.aemeasurable_fderivWithin

theorem aemeasurable_ofReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => ENNReal.ofReal |(f' x).det|) (μ.restrict s) := by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  -- ⊢ AEMeasurable fun x => |ContinuousLinearMap.det (f' x)|
  refine' continuous_abs.measurable.comp_aemeasurable _
  -- ⊢ AEMeasurable fun x => ContinuousLinearMap.det (f' x)
  refine' ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable _
  -- ⊢ AEMeasurable fun x => f' x
  exact aemeasurable_fderivWithin μ hs hf'
  -- 🎉 no goals
#align measure_theory.ae_measurable_of_real_abs_det_fderiv_within MeasureTheory.aemeasurable_ofReal_abs_det_fderivWithin

theorem aemeasurable_toNNReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => |(f' x).det|.toNNReal) (μ.restrict s) := by
  apply measurable_real_toNNReal.comp_aemeasurable
  -- ⊢ AEMeasurable fun x => |ContinuousLinearMap.det (f' x)|
  refine' continuous_abs.measurable.comp_aemeasurable _
  -- ⊢ AEMeasurable fun x => ContinuousLinearMap.det (f' x)
  refine' ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable _
  -- ⊢ AEMeasurable fun x => f' x
  exact aemeasurable_fderivWithin μ hs hf'
  -- 🎉 no goals
#align measure_theory.ae_measurable_to_nnreal_abs_det_fderiv_within MeasureTheory.aemeasurable_toNNReal_abs_det_fderivWithin

/-- If a function is differentiable and injective on a measurable set,
then the image is measurable.-/
theorem measurable_image_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf
#align measure_theory.measurable_image_of_fderiv_within MeasureTheory.measurable_image_of_fderivWithin

/-- If a function is differentiable and injective on a measurable set `s`, then its restriction
to `s` is a measurable embedding. -/
theorem measurableEmbedding_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    MeasurableEmbedding (s.restrict f) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf
#align measure_theory.measurable_embedding_of_fderiv_within MeasureTheory.measurableEmbedding_of_fderivWithin

/-!
### Proving the estimate for the measure of the image

We show the formula `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ = μ (f '' s)`,
in `lintegral_abs_det_fderiv_eq_addHaar_image`. For this, we show both inequalities in both
directions, first up to controlled errors and then letting these errors tend to `0`.
-/


theorem addHaar_image_le_lintegral_abs_det_fderiv_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) {ε : ℝ≥0} (εpos : 0 < ε) :
    μ (f '' s) ≤ (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
  /- To bound `μ (f '' s)`, we cover `s` by sets where `f` is well-approximated by linear maps
    `A n` (and where `f'` is almost everywhere close to `A n`), and then use that `f` expands the
    measure of such a set by at most `(A n).det + ε`. -/
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              μ (g '' t) ≤ (ENNReal.ofReal |A.det| + ε) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε :=
      continuousAt_iff.1 ContinuousLinearMap.continuous_det.continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    refine' ⟨min δ δ'', lt_min δpos (half_pos δ'pos), _, _⟩
    · intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      calc
        ‖B - A‖ ≤ (min δ δ'' : ℝ≥0) := hB
        _ ≤ δ'' := by simp only [le_refl, NNReal.coe_min, min_le_iff, or_true_iff]
        _ < δ' := half_lt_self δ'pos
    · intro t g htg
      exact h t g (htg.mono_num (min_le_left _ _))
  choose δ hδ using this
  -- ⊢ ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f'  …
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_subset f (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := (measure_iUnion_le _)
    _ ≤ ∑' n, (ENNReal.ofReal |(A n).det| + ε) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2.2
      exact ht n
    _ = ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono (inter_subset_left _ _)]
      intro x hx
      have I : |(A n).det| ≤ |(f' x).det| + ε :=
        calc
          |(A n).det| = |(f' x).det - ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(f' x).det| + |(f' x).det - (A n).det| := (abs_sub _ _)
          _ ≤ |(f' x).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(A n).det| + ε ≤ ENNReal.ofReal (|(f' x).det| + ε) + ε :=
          add_le_add (ENNReal.ofReal_le_ofReal I) le_rfl
        _ = ENNReal.ofReal |(f' x).det| + 2 * ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, two_mul, add_assoc, NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ x in ⋃ n, s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      have M : ∀ n : ℕ, MeasurableSet (s ∩ t n) := fun n => hs.inter (t_meas n)
      rw [lintegral_iUnion M]
      exact pairwise_disjoint_mono t_disj fun n => inter_subset_right _ _
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      have : s = ⋃ n, s ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) (inter_subset_left _ _)
      rw [← this]
    _ = (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
      simp only [lintegral_add_right' _ aemeasurable_const, set_lintegral_const]
#align measure_theory.add_haar_image_le_lintegral_abs_det_fderiv_aux1 MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv_aux1

theorem addHaar_image_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : ℝ≥0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine' tendsto_const_nhds.add _
    refine' ENNReal.Tendsto.mul_const _ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  -- ⊢ ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f'  …
  apply ge_of_tendsto this
  -- ⊢ ∀ᶠ (c : ℝ≥0) in 𝓝[Ioi 0] 0, ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal | …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ≥0), a ∈ Ioi 0 → ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal |Con …
  rintro ε (εpos : 0 < ε)
  -- ⊢ ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f'  …
  exact addHaar_image_le_lintegral_abs_det_fderiv_aux1 μ hs hf' εpos
  -- 🎉 no goals
#align measure_theory.add_haar_image_le_lintegral_abs_det_fderiv_aux2 MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv_aux2

theorem addHaar_image_le_lintegral_abs_det_fderiv (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  -- ⊢ ↑↑μ (f '' s) ≤ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f'  …
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurable_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μ (f '' s) ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      conv_lhs => rw [A, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        addHaar_image_le_lintegral_abs_det_fderiv_aux2 μ (hs.inter (u_meas n)) _ fun x hx =>
          (hf' x hx.1).mono (inter_subset_left _ _)
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) this)
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_rhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right _ _
#align measure_theory.add_haar_image_le_lintegral_abs_det_fderiv MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv

theorem lintegral_abs_det_fderiv_le_addHaar_image_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) {ε : ℝ≥0} (εpos : 0 < ε) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) + 2 * ε * μ s := by
  /- To bound `∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ`, we cover `s` by sets where `f` is
    well-approximated by linear maps `A n` (and where `f'` is almost everywhere close to `A n`),
    and then use that `f` expands the measure of such a set by at least `(A n).det - ε`. -/
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              ENNReal.ofReal |A.det| * μ t ≤ μ (g '' t) + ε * μ t := by
    intro A
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε :=
      continuousAt_iff.1 ContinuousLinearMap.continuous_det.continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    have I'' : ∀ B : E →L[ℝ] E, ‖B - A‖ ≤ ↑δ'' → |B.det - A.det| ≤ ↑ε := by
      intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      exact hB.trans_lt (half_lt_self δ'pos)
    rcases eq_or_ne A.det 0 with (hA | hA)
    · refine' ⟨δ'', half_pos δ'pos, I'', _⟩
      simp only [hA, forall_const, zero_mul, ENNReal.ofReal_zero, imp_true_iff,
        zero_le, abs_zero]
    let m : ℝ≥0 := Real.toNNReal |A.det| - ε
    have I : (m : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
      simp only [ENNReal.ofReal, ENNReal.coe_sub]
      apply ENNReal.sub_lt_self ENNReal.coe_ne_top
      · simpa only [abs_nonpos_iff, Real.toNNReal_eq_zero, ENNReal.coe_eq_zero, Ne.def] using hA
      · simp only [εpos.ne', ENNReal.coe_eq_zero, Ne.def, not_false_iff]
    rcases ((mul_le_addHaar_image_of_lt_det μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    refine' ⟨min δ δ'', lt_min δpos (half_pos δ'pos), _, _⟩
    · intro B hB
      apply I'' _ (hB.trans _)
      simp only [le_refl, NNReal.coe_min, min_le_iff, or_true_iff]
    · intro t g htg
      rcases eq_or_ne (μ t) ∞ with (ht | ht)
      · simp only [ht, εpos.ne', ENNReal.mul_top, ENNReal.coe_eq_zero, le_top, Ne.def,
          not_false_iff, _root_.add_top]
      have := h t g (htg.mono_num (min_le_left _ _))
      rwa [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at this
      simp only [ht, imp_true_iff, Ne.def, not_false_iff]
  choose δ hδ using this
  -- ⊢ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f' x)| ∂μ ≤ ↑↑μ (f …
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) (inter_subset_left _ _)
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n => hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right _ _
    _ ≤ ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono (inter_subset_left _ _)]
      intro x hx
      have I : |(f' x).det| ≤ |(A n).det| + ε :=
        calc
          |(f' x).det| = |(A n).det + ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(A n).det| + |(f' x).det - (A n).det| := (abs_add _ _)
          _ ≤ |(A n).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(f' x).det| ≤ ENNReal.ofReal (|(A n).det| + ε) :=
          ENNReal.ofReal_le_ofReal I
        _ = ENNReal.ofReal |(A n).det| + ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    _ = ∑' n, (ENNReal.ofReal |(A n).det| * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      simp only [set_lintegral_const, lintegral_add_right _ measurable_const]
    _ ≤ ∑' n, (μ (f '' (s ∩ t n)) + ε * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      refine' ENNReal.tsum_le_tsum fun n => add_le_add_right _ _
      exact (hδ (A n)).2.2 _ _ (ht n)
    _ = μ (f '' s) + 2 * ε * μ s := by
      conv_rhs => rw [s_eq]
      rw [image_iUnion, measure_iUnion]; rotate_left
      · intro i j hij
        apply Disjoint.image _ hf (inter_subset_left _ _) (inter_subset_left _ _)
        exact Disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _) (t_disj hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (t_meas i))
            (fun x hx => (hf' x hx.1).mono (inter_subset_left _ _))
            (hf.mono (inter_subset_left _ _))
      rw [measure_iUnion]; rotate_left
      · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right _ _
      · exact fun i => hs.inter (t_meas i)
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      congr 1
      ext1 i
      rw [mul_assoc, two_mul, add_assoc]
#align measure_theory.lintegral_abs_det_fderiv_le_add_haar_image_aux1 MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image_aux1

theorem lintegral_abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  -- We just need to let the error tend to `0` in the previous lemma.
  have :
    Tendsto (fun ε : ℝ≥0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine' tendsto_const_nhds.add _
    refine' ENNReal.Tendsto.mul_const _ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  -- ⊢ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f' x)| ∂μ ≤ ↑↑μ (f …
  apply ge_of_tendsto this
  -- ⊢ ∀ᶠ (c : ℝ≥0) in 𝓝[Ioi 0] 0, ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinea …
  filter_upwards [self_mem_nhdsWithin]
  -- ⊢ ∀ (a : ℝ≥0), a ∈ Ioi 0 → ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMa …
  rintro ε (εpos : 0 < ε)
  -- ⊢ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f' x)| ∂μ ≤ ↑↑μ (f …
  exact lintegral_abs_det_fderiv_le_addHaar_image_aux1 μ hs hf' hf εpos
  -- 🎉 no goals
#align measure_theory.lintegral_abs_det_fderiv_le_add_haar_image_aux2 MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image_aux2

theorem lintegral_abs_det_fderiv_le_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  /- We already know the result for finite-measure sets. We cover `s` by finite-measure sets using
    `spanningSets μ`, and apply the previous result to each of these parts. -/
  let u n := disjointed (spanningSets μ) n
  -- ⊢ ∫⁻ (x : E) in s, ENNReal.ofReal |ContinuousLinearMap.det (f' x)| ∂μ ≤ ↑↑μ (f …
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurable_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right _ _
    _ ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        lintegral_abs_det_fderiv_le_addHaar_image_aux2 μ (hs.inter (u_meas n)) _
          (fun x hx => (hf' x hx.1).mono (inter_subset_left _ _)) (hf.mono (inter_subset_left _ _))
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) this)
    _ = μ (f '' s) := by
      conv_rhs => rw [A, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hf (inter_subset_left _ _) (inter_subset_left _ _)
        exact
          Disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _)
            (disjoint_disjointed _ hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (u_meas i))
            (fun x hx => (hf' x hx.1).mono (inter_subset_left _ _))
            (hf.mono (inter_subset_left _ _))

#align measure_theory.lintegral_abs_det_fderiv_le_add_haar_image MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a measurable set `s`, then the measure of `f '' s` is given by the
integral of `|(f' x).det|` on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivWithin`. -/
theorem lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) :=
  le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')
#align measure_theory.lintegral_abs_det_fderiv_eq_add_haar_image MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a measurable set `s`, then the pushforward of the measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set. This version requires
that `f` is measurable, as otherwise `Measure.map f` is zero per our definitions.
For a version without measurability assumption but dealing with the restricted
function `s.restrict f`, see `restrict_map_withDensity_abs_det_fderiv_eq_addHaar`.
-/
theorem map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (h'f : Measurable f) :
    Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) =
      μ.restrict (f '' s) := by
  apply Measure.ext fun t ht => ?_
  -- ⊢ ↑↑(Measure.map f (withDensity (Measure.restrict μ s) fun x => ENNReal.ofReal …
  rw [map_apply h'f ht, withDensity_apply _ (h'f ht), Measure.restrict_apply ht,
    restrict_restrict (h'f ht),
    lintegral_abs_det_fderiv_eq_addHaar_image μ ((h'f ht).inter hs)
      (fun x hx => (hf' x hx.2).mono (inter_subset_right _ _)) (hf.mono (inter_subset_right _ _)),
    image_preimage_inter]
#align measure_theory.map_with_density_abs_det_fderiv_eq_add_haar MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar

/-- Change of variable formula for differentiable functions, set version: if a function `f` is
injective and differentiable on a measurable set `s`, then the pushforward of the measure with
density `|(f' x).det|` on `s` is the Lebesgue measure on the image set. This version is expressed
in terms of the restricted function `s.restrict f`.
For a version for the original function, but with a measurability assumption,
see `map_withDensity_abs_det_fderiv_eq_addHaar`.
-/
theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map (s.restrict f) (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (f '' s) := by
  obtain ⟨u, u_meas, uf⟩ : ∃ u, Measurable u ∧ EqOn u f s := by
    classical
    refine' ⟨piecewise s f 0, _, piecewise_eqOn _ _ _⟩
    refine' ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn hs
    have : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
    exact this.continuousOn
  have u' : ∀ x ∈ s, HasFDerivWithinAt u (f' x) s x := fun x hx =>
    (hf' x hx).congr (fun y hy => uf hy) (uf hx)
  set F : s → E := u ∘ (↑) with hF
  -- ⊢ Measure.map (Set.restrict s f) (Measure.comap Subtype.val (withDensity μ fun …
  have A :
    Measure.map F (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (u '' s) := by
    rw [hF, ← Measure.map_map u_meas measurable_subtype_coe, map_comap_subtype_coe hs,
      restrict_withDensity hs]
    exact map_withDensity_abs_det_fderiv_eq_addHaar μ hs u' (hf.congr uf.symm) u_meas
  rw [uf.image_eq] at A
  -- ⊢ Measure.map (Set.restrict s f) (Measure.comap Subtype.val (withDensity μ fun …
  have : F = s.restrict f := by
    ext x
    exact uf x.2
  rwa [this] at A
  -- 🎉 no goals
#align measure_theory.restrict_map_with_density_abs_det_fderiv_eq_add_haar MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar

/-! ### Change of variable formulas in integrals -/


/- Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Lebesgue integral of a function
`g : E → ℝ≥0∞` on `f '' s` coincides with the integral of `|(f' x).det| * g ∘ f` on `s`.
Note that the measurability of `f '' s` is given by `measurable_image_of_fderivWithin`. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  have : ∀ x : s, g (s.restrict f x) = (g ∘ f) x := fun x => rfl
  -- ⊢ ∫⁻ (a : ↑s), g (Set.restrict s f a) ∂Measure.comap Subtype.val (withDensity  …
  simp only [this]
  -- ⊢ ∫⁻ (a : ↑s), (g ∘ f) ↑a ∂Measure.comap Subtype.val (withDensity μ fun x => E …
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs,
    set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
    -- 🎉 no goals
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
    -- 🎉 no goals
  · exact aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'
    -- 🎉 no goals
#align measure_theory.lintegral_image_eq_lintegral_abs_det_fderiv_mul MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul

/-- Integrability in the change of variable formula for differentiable functions: if a
function `f` is injective and differentiable on a measurable set `s`, then a function
`g : E → F` is integrable on `f '' s` if and only if `|(f' x).det| • g ∘ f` is
integrable on `s`. -/
theorem integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (f x)) s μ := by
  rw [IntegrableOn, ← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  change Integrable ((g ∘ f) ∘ ((↑) : s → E)) _ ↔ _
  -- ⊢ Integrable ((g ∘ f) ∘ Subtype.val) ↔ IntegrableOn (fun x => |ContinuousLinea …
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff, map_comap_subtype_coe hs]
  -- ⊢ Integrable (g ∘ f) ↔ IntegrableOn (fun x => |ContinuousLinearMap.det (f' x)| …
  simp only [ENNReal.ofReal]
  -- ⊢ Integrable (g ∘ f) ↔ IntegrableOn (fun x => |ContinuousLinearMap.det (f' x)| …
  rw [restrict_withDensity hs, integrable_withDensity_iff_integrable_coe_smul₀, IntegrableOn]
  -- ⊢ (Integrable fun x => ↑(Real.toNNReal |ContinuousLinearMap.det (f' x)|) • (g  …
  · rw [iff_iff_eq]
    -- ⊢ (Integrable fun x => ↑(Real.toNNReal |ContinuousLinearMap.det (f' x)|) • (g  …
    congr 2 with x
    -- ⊢ ↑(Real.toNNReal |ContinuousLinearMap.det (f' x)|) • (g ∘ f) x = |ContinuousL …
    rw [Real.coe_toNNReal _ (abs_nonneg _)]
    -- ⊢ |ContinuousLinearMap.det (f' x)| • (g ∘ f) x = |ContinuousLinearMap.det (f'  …
    rfl
    -- 🎉 no goals
  · exact aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf'
    -- 🎉 no goals
#align measure_theory.integrable_on_image_iff_integrable_on_abs_det_fderiv_smul MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul

/-- Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : E → F` on `f '' s` coincides with the integral of `|(f' x).det| • g ∘ f` on `s`. -/
theorem integral_image_eq_integral_abs_det_fderiv_smul [CompleteSpace F] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  have : ∀ x : s, g (s.restrict f x) = (g ∘ f) x := fun x => rfl
  -- ⊢ ∫ (x : ↑s), g (Set.restrict s f x) ∂Measure.comap Subtype.val (withDensity μ …
  simp only [this, ENNReal.ofReal]
  -- ⊢ ∫ (x : ↑s), (g ∘ f) ↑x ∂Measure.comap Subtype.val (withDensity μ fun x => ↑( …
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    set_integral_withDensity_eq_set_integral_smul₀
      (aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf') _ hs]
  congr with x
  -- ⊢ Real.toNNReal |ContinuousLinearMap.det (f' x)| • (g ∘ f) x = |ContinuousLine …
  conv_rhs => rw [← Real.coe_toNNReal _ (abs_nonneg (f' x).det)]
  -- 🎉 no goals
#align measure_theory.integral_image_eq_integral_abs_det_fderiv_smul MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul

-- Porting note: move this to `Topology.Algebra.Module.Basic` when port is over
theorem det_one_smulRight {𝕜 : Type*} [NormedField 𝕜] (v : 𝕜) :
    ((1 : 𝕜 →L[𝕜] 𝕜).smulRight v).det = v := by
  have : (1 : 𝕜 →L[𝕜] 𝕜).smulRight v = v • (1 : 𝕜 →L[𝕜] 𝕜) := by
    ext1
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply, mul_one]
  rw [this, ContinuousLinearMap.det, ContinuousLinearMap.coe_smul]
  -- ⊢ ↑LinearMap.det (v • ↑1) = v
  rw [show ((1 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜) = LinearMap.id from rfl]
  -- ⊢ ↑LinearMap.det (v • LinearMap.id) = v
  rw [LinearMap.det_smul, FiniteDimensional.finrank_self, LinearMap.det_id, pow_one, mul_one]
  -- 🎉 no goals
#align measure_theory.det_one_smul_right MeasureTheory.det_one_smulRight

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then a
function `g : ℝ → F` is integrable on `f '' s` if and only if `|(f' x)| • g ∘ f` is integrable on
`s`. -/
theorem integrableOn_image_iff_integrableOn_abs_deriv_smul {s : Set ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s := by
  simpa only [det_one_smulRight] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
#align measure_theory.integrable_on_image_iff_integrable_on_abs_deriv_smul MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul

/-- Change of variable formula for differentiable functions (one-variable version): if a function
`f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the Bochner integral of a
function `g : ℝ → F` on `f '' s` coincides with the integral of `|(f' x)| • g ∘ f` on `s`. -/
theorem integral_image_eq_integral_abs_deriv_smul {s : Set ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    [CompleteSpace F] (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → F) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  simpa only [det_one_smulRight] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
#align measure_theory.integral_image_eq_integral_abs_deriv_smul MeasureTheory.integral_image_eq_integral_abs_deriv_smul

theorem integral_target_eq_integral_abs_det_fderiv_smul [CompleteSpace F] {f : LocalHomeomorph E E}
    (hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x) (g : E → F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ := by
  have : f '' f.source = f.target := LocalEquiv.image_source_eq_target f.toLocalEquiv
  -- ⊢ ∫ (x : E) in f.target, g x ∂μ = ∫ (x : E) in f.source, |ContinuousLinearMap. …
  rw [← this]
  -- ⊢ ∫ (x : E) in ↑f '' f.source, g x ∂μ = ∫ (x : E) in f.source, |ContinuousLine …
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  -- ⊢ ∀ (x : E), x ∈ f.source → HasFDerivWithinAt (↑f) (f' x) f.source x
  intro x hx
  -- ⊢ HasFDerivWithinAt (↑f) (f' x) f.source x
  exact (hf' x hx).hasFDerivWithinAt
  -- 🎉 no goals
#align measure_theory.integral_target_eq_integral_abs_det_fderiv_smul MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul

end MeasureTheory
