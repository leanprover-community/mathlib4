/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.integral.divergence_theorem
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.DivergenceTheorem
import Mathbin.Analysis.BoxIntegral.Integrability
import Mathbin.Analysis.Calculus.Deriv.Basic
import Mathbin.MeasureTheory.Constructions.Prod.Integral
import Mathbin.MeasureTheory.Integral.IntervalIntegral

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
continuous on a rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, differentiable on its interior with
derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹`, and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on
`[a, b]`, where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the
sum of integrals of `f` over the faces of `[a, b]`, taken with appropriate signs. Moreover, the same
is true if the function is not differentiable at countably many points of the interior of `[a, b]`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

## Notations

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `fin n → ℝ`, `fin (n + 1) → ℝ`, `fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely `[a ∘
  fin.succ_above i, b ∘ fin.succ_above i]`;
* `e i` : `i`-th basis vector `pi.single i 1`;
* `front_face i`, `back_face i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `fin.insert_nth i (b i)` and `fin.insert_nth i (a i)`.

## TODO

* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/


open Set Finset TopologicalSpace Function BoxIntegral MeasureTheory Filter

open scoped BigOperators Classical Topology Interval

universe u

namespace MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section

variable {n : ℕ}

-- mathport name: «exprℝⁿ»
local notation "ℝⁿ" => Fin n → ℝ

-- mathport name: «exprℝⁿ⁺¹»
local notation "ℝⁿ⁺¹" => Fin (n + 1) → ℝ

-- mathport name: «exprEⁿ⁺¹»
local notation "Eⁿ⁺¹" => Fin (n + 1) → E

-- mathport name: «expre »
local notation "e " i => Pi.single i 1

section

/-!
### Divergence theorem for functions on `ℝⁿ⁺¹ = fin (n + 1) → ℝ`.

In this section we use the divergence theorem for a Henstock-Kurzweil-like integral
`box_integral.has_integral_GP_divergence_of_forall_has_deriv_within_at` to prove the divergence
theorem for Bochner integral. The divergence theorem for Bochner integral
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable` assumes that the function
itself is continuous on a closed box, differentiable at all but countably many points of its
interior, and the divergence is integrable on the box.

This statement differs from `box_integral.has_integral_GP_divergence_of_forall_has_deriv_within_at`
in several aspects.

* We use Bochner integral instead of a Henstock-Kurzweil integral. This modification is done in
  `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₁`. As a side effect
  of this change, we need to assume that the divergence is integrable.

* We don't assume differentiability on the boundary of the box. This modification is done in
  `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₂`. To prove it, we
  choose an increasing sequence of smaller boxes that cover the interior of the original box, then
  apply the previous lemma to these smaller boxes and take the limit of both sides of the equation.

* We assume `a ≤ b` instead of `∀ i, a i < b i`. This is the last step of the proof, and it is done
  in the main theorem `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`.
-/


/-- An auxiliary lemma for
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`. This is exactly
`box_integral.has_integral_GP_divergence_of_forall_has_deriv_within_at` reformulated for the
Bochner integral. -/
theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹) (hs : s.Countable)
    (Hc : ContinuousOn f I.Icc) (Hd : ∀ x ∈ I.Icc \ s, HasFDerivWithinAt f (f' x) I.Icc x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) I.Icc) :
    (∫ x in I.Icc, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        (∫ x in (I.face i).Icc, f (i.insertNth (I.upper i) x) i) -
          ∫ x in (I.face i).Icc, f (i.insertNth (I.lower i) x) i :=
  by
  simp only [← set_integral_congr_set_ae (box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    has_integral_GP_divergence_of_forall_has_deriv_within_at I f f' (s ∩ I.Icc)
      (hs.mono (inter_subset_left _ _)) (fun x hx => Hc _ hx.2) fun x hx =>
      Hd _ ⟨hx.1, fun h => hx.2 ⟨h, hx.1⟩⟩
  rw [continuousOn_pi] at Hc 
  refine' (A.unique B).trans (sum_congr rfl fun i hi => _)
  refine' congr_arg₂ Sub.sub _ _
  · have := box.continuous_on_face_Icc (Hc i) (Set.right_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc
    exact (this.has_box_integral ⊥ rfl).integral_eq; infer_instance
  · have := box.continuous_on_face_Icc (Hc i) (Set.left_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc
    exact (this.has_box_integral ⊥ rfl).integral_eq; infer_instance
#align measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₁ MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁

/-- An auxiliary lemma for
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`. Compared to the previous
lemma, here we drop the assumption of differentiability on the boundary of the box. -/
theorem integral_divergence_of_has_fderiv_within_at_off_countable_aux₂ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹) (hs : s.Countable)
    (Hc : ContinuousOn f I.Icc) (Hd : ∀ x ∈ I.Ioo \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) I.Icc) :
    (∫ x in I.Icc, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        (∫ x in (I.face i).Icc, f (i.insertNth (I.upper i) x) i) -
          ∫ x in (I.face i).Icc, f (i.insertNth (I.lower i) x) i :=
  by
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
    these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : ∀ k, (J k).Icc ⊆ I.Icc := fun k => (hJ_sub k).trans I.Ioo_subset_Icc
  have hJ_le : ∀ k, J k ≤ I := fun k => box.le_iff_Icc.2 (hJ_sub' k)
  have HcJ : ∀ k, ContinuousOn f (J k).Icc := fun k => Hc.mono (hJ_sub' k)
  have HdJ : ∀ (k), ∀ x ∈ (J k).Icc \ s, HasFDerivWithinAt f (f' x) (J k).Icc x := fun k x hx =>
    (Hd x ⟨hJ_sub k hx.1, hx.2⟩).HasFDerivWithinAt
  have HiJ : ∀ k, integrable_on (fun x => ∑ i, f' x (e i) i) (J k).Icc := fun k =>
    Hi.mono_set (hJ_sub' k)
  -- Apply the previous lemma to `J k`.
  have HJ_eq := fun k =>
    integral_divergence_of_has_fderiv_within_at_off_countable_aux₁ (J k) f f' s hs (HcJ k) (HdJ k)
      (HiJ k)
  -- Note that the LHS of `HJ_eq k` tends to the LHS of the goal as `k → ∞`.
  have hI_tendsto :
    tendsto (fun k => ∫ x in (J k).Icc, ∑ i, f' x (e i) i) at_top
      (𝓝 (∫ x in I.Icc, ∑ i, f' x (e i) i)) :=
    by
    simp only [integrable_on, ← measure.restrict_congr_set (box.Ioo_ae_eq_Icc _)] at Hi ⊢
    rw [← box.Union_Ioo_of_tendsto J.monotone hJl hJu] at Hi ⊢
    exact
      tendsto_set_integral_of_monotone (fun k => (J k).measurableSet_Ioo) (box.Ioo.comp J).Monotone
        Hi
  -- Thus it suffices to prove the same about the RHS.
  refine' tendsto_nhds_unique_of_eventuallyEq hI_tendsto _ (eventually_of_forall HJ_eq)
  clear hI_tendsto
  rw [tendsto_pi_nhds] at hJl hJu 
  /- We'll need to prove a similar statement about the integrals over the front sides and the
    integrals over the back sides. In order to avoid repeating ourselves, we formulate a lemma. -/
  suffices
    ∀ (i : Fin (n + 1)) (c : ℕ → ℝ) (d),
      (∀ k, c k ∈ Icc (I.lower i) (I.upper i)) →
        tendsto c at_top (𝓝 d) →
          tendsto (fun k => ∫ x in ((J k).face i).Icc, f (i.insertNth (c k) x) i) at_top
            (𝓝 <| ∫ x in (I.face i).Icc, f (i.insertNth d x) i)
    by
    rw [box.Icc_eq_pi] at hJ_sub' 
    refine' tendsto_finset_sum _ fun i hi => (this _ _ _ _ (hJu _)).sub (this _ _ _ _ (hJl _))
    exacts [fun k => hJ_sub' k (J k).upper_mem_Icc _ trivial, fun k =>
      hJ_sub' k (J k).lower_mem_Icc _ trivial]
  intro i c d hc hcd
  /- First we prove that the integrals of the restriction of `f` to `{x | x i = d}` over increasing
    boxes `((J k).face i).Icc` tend to the desired limit. The proof mostly repeats the one above. -/
  have hd : d ∈ Icc (I.lower i) (I.upper i) :=
    is_closed_Icc.mem_of_tendsto hcd (eventually_of_forall hc)
  have Hic : ∀ k, integrable_on (fun x => f (i.insert_nth (c k) x) i) (I.face i).Icc := fun k =>
    (box.continuous_on_face_Icc ((continuous_apply i).comp_continuousOn Hc) (hc k)).integrableOn_Icc
  have Hid : integrable_on (fun x => f (i.insert_nth d x) i) (I.face i).Icc :=
    (box.continuous_on_face_Icc ((continuous_apply i).comp_continuousOn Hc) hd).integrableOn_Icc
  have H :
    tendsto (fun k => ∫ x in ((J k).face i).Icc, f (i.insert_nth d x) i) at_top
      (𝓝 <| ∫ x in (I.face i).Icc, f (i.insert_nth d x) i) :=
    by
    have hIoo : (⋃ k, ((J k).face i).Ioo) = (I.face i).Ioo :=
      box.Union_Ioo_of_tendsto ((box.monotone_face i).comp J.monotone)
        (tendsto_pi_nhds.2 fun _ => hJl _) (tendsto_pi_nhds.2 fun _ => hJu _)
    simp only [integrable_on, ← measure.restrict_congr_set (box.Ioo_ae_eq_Icc _), ← hIoo] at Hid ⊢
    exact
      tendsto_set_integral_of_monotone (fun k => ((J k).face i).measurableSet_Ioo)
        (box.Ioo.monotone.comp ((box.monotone_face i).comp J.monotone)) Hid
  /- Thus it suffices to show that the distance between the integrals of the restrictions of `f` to
    `{x | x i = c k}` and `{x | x i = d}` over `((J k).face i).Icc` tends to zero as `k → ∞`. Choose
    `ε > 0`. -/
  refine' H.congr_dist (metric.nhds_basis_closed_ball.tendsto_right_iff.2 fun ε εpos => _)
  have hvol_pos : ∀ J : box (Fin n), 0 < ∏ j, J.upper j - J.lower j := fun J =>
    prod_pos fun j hj => sub_pos.2 <| J.lower_lt_upper _
  /- Choose `δ > 0` such that for any `x y ∈ I.Icc` at distance at most `δ`, the distance between
    `f x` and `f y` is at most `ε / volume (I.face i).Icc`, then the distance between the integrals
    is at most `(ε / volume (I.face i).Icc) * volume ((J k).face i).Icc ≤ ε`. -/
  rcases Metric.uniformContinuousOn_iff_le.1
      (I.is_compact_Icc.uniform_continuous_on_of_continuous Hc)
      (ε / ∏ j, (I.face i).upper j - (I.face i).lower j) (div_pos εpos (hvol_pos (I.face i))) with
    ⟨δ, δpos, hδ⟩
  refine' (hcd.eventually (Metric.ball_mem_nhds _ δpos)).mono fun k hk => _
  have Hsub : ((J k).face i).Icc ⊆ (I.face i).Icc := box.le_iff_Icc.1 (box.face_mono (hJ_le _) i)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm, ←
    integral_sub (Hid.mono_set Hsub) ((Hic _).mono_set Hsub)]
  calc
    ‖∫ x in ((J k).face i).Icc, f (i.insert_nth d x) i - f (i.insert_nth (c k) x) i‖ ≤
        (ε / ∏ j, (I.face i).upper j - (I.face i).lower j) * (volume ((J k).face i).Icc).toReal :=
      by
      refine'
        norm_set_integral_le_of_norm_le_const' (((J k).face i).measure_Icc_lt_top _)
          ((J k).face i).measurableSet_Icc fun x hx => _
      rw [← dist_eq_norm]
      calc
        dist (f (i.insert_nth d x) i) (f (i.insert_nth (c k) x) i) ≤
            dist (f (i.insert_nth d x)) (f (i.insert_nth (c k) x)) :=
          dist_le_pi_dist (f (i.insert_nth d x)) (f (i.insert_nth (c k) x)) i
        _ ≤ ε / ∏ j, (I.face i).upper j - (I.face i).lower j :=
          hδ _ (I.maps_to_insert_nth_face_Icc hd <| Hsub hx) _
            (I.maps_to_insert_nth_face_Icc (hc _) <| Hsub hx) _
        
      rw [Fin.dist_insertNth_insertNth, dist_self, dist_comm]
      exact max_le hk.le δpos.lt.le
    _ ≤ ε :=
      by
      rw [box.Icc_def, Real.volume_Icc_pi_toReal ((J k).face i).lower_le_upper, ←
        le_div_iff (hvol_pos _)]
      refine'
        div_le_div_of_le_left εpos.le (hvol_pos _) (prod_le_prod (fun j hj => _) fun j hj => _)
      exacts [sub_nonneg.2 (box.lower_le_upper _ _),
        sub_le_sub ((hJ_sub' _ (J _).upper_mem_Icc).2 _) ((hJ_sub' _ (J _).lower_mem_Icc).1 _)]
    
#align measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₂ MeasureTheory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₂

variable (a b : ℝⁿ⁺¹)

-- mathport name: «exprface »
local notation "face " i => Set.Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)

-- mathport name: «exprfront_face »
local notation "front_face " i:2000 => Fin.insertNth i (b i)

-- mathport name: «exprback_face »
local notation "back_face " i:2000 => Fin.insertNth i (a i)

/-- **Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is continuous on a rectangular
box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, is differentiable on its interior with derivative
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`,
where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriat signs.

Moreover, the same is true if the function is not differentiable at countably many
points of the interior of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ fin.succ_above i, b ∘ fin.succ_above i]` in `ℝⁿ`, where
`fin.succ_above : fin n ↪o fin (n + 1)` is the order embedding with range `{i}ᶜ`. The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ back_face i` and `f ∘ front_face i`, where
`back_face i = fin.insert_nth i (a i)` and `front_face i = fin.insert_nth i (b i)` are embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordinate. -/
theorem integral_divergence_of_has_fderiv_within_at_off_countable (hle : a ≤ b) (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        (∫ x in face i, f ((front_face (i)) x) i) - ∫ x in face i, f ((back_face (i)) x) i :=
  by
  rcases em (∃ i, a i = b i) with (⟨i, hi⟩ | hne)
  · -- First we sort out the trivial case `∃ i, a i = b i`.
    simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j) (b j)) = ∅ := univ_pi_eq_empty hi'
    rw [this, integral_empty, sum_eq_zero]
    rintro j -
    rcases eq_or_ne i j with (rfl | hne)
    · simp [hi]
    · rcases Fin.exists_succAbove_eq hne with ⟨i, rfl⟩
      have : (pi Set.univ fun k : Fin n => Ioc (a <| j.succ_above k) (b <| j.succ_above k)) = ∅ :=
        univ_pi_eq_empty hi'
      rw [this, integral_empty, integral_empty, sub_self]
  · -- In the non-trivial case `∀ i, a i < b i`, we apply a lemma we proved above.
    have hlt : ∀ i, a i < b i := fun i => (hle i).lt_of_ne fun hi => hne ⟨i, hi⟩
    convert
      integral_divergence_of_has_fderiv_within_at_off_countable_aux₂ ⟨a, b, hlt⟩ f f' s hs Hc Hd Hi
#align measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable MeasureTheory.integral_divergence_of_has_fderiv_within_at_off_countable

/-- **Divergence theorem** for a family of functions `f : fin (n + 1) → ℝⁿ⁺¹ → E`. See also
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable'` for a version formulated
in terms of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`. -/
theorem integral_divergence_of_has_fderiv_within_at_off_countable' (hle : a ≤ b)
    (f : Fin (n + 1) → ℝⁿ⁺¹ → E) (f' : Fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ (pi Set.univ fun i => Ioo (a i) (b i)) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' i x (e i)) =
      ∑ i : Fin (n + 1),
        (∫ x in face i, f i ((front_face (i)) x)) - ∫ x in face i, f i ((back_face (i)) x) :=
  integral_divergence_of_has_fderiv_within_at_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi
#align measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable' MeasureTheory.integral_divergence_of_has_fderiv_within_at_off_countable'

end

/-- An auxiliary lemma that is used to specialize the general divergence theorem to spaces that do
not have the form `fin n → ℝ`. -/
theorem integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv {F : Type _}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [MeasureSpace F] [BorelSpace F]
    (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
    (he_vol : MeasurePreserving eL volume volume) (f : Fin (n + 1) → F → E)
    (f' : Fin (n + 1) → F → F →L[ℝ] E) (s : Set F) (hs : s.Countable) (a b : F) (hle : a ≤ b)
    (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ interior (Icc a b) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x) (DF : F → E)
    (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm <| e i)) (Hi : IntegrableOn DF (Icc a b)) :
    (∫ x in Icc a b, DF x) =
      ∑ i : Fin (n + 1),
        (∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL b i) x)) -
          ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL a i) x) :=
  have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.toMeasurableEquiv.MeasurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by ext1 x;
    simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc
    (∫ x in Icc a b, DF x) = ∫ x in Icc a b, ∑ i, f' i x (eL.symm <| e i) := by simp only [hDF]
    _ = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm <| e i) :=
      by
      rw [← he_vol.set_integral_preimage_emb he_emb]
      simp only [hIcc, eL.symm_apply_apply]
    _ =
        ∑ i : Fin (n + 1),
          (∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL b i) x)) -
            ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL a i) x) :=
      by
      convert
        integral_divergence_of_has_fderiv_within_at_off_countable' (eL a) (eL b)
          ((he_ord _ _).2 hle) (fun i x => f i (eL.symm x))
          (fun i x => f' i (eL.symm x) ∘L (eL.symm : ℝⁿ⁺¹ →L[ℝ] F)) (eL.symm ⁻¹' s)
          (hs.preimage eL.symm.injective) _ _ _
      · exact fun i => (Hc i).comp eL.symm.continuous_on hIcc'.subset
      · refine' fun x hx i => (Hd (eL.symm x) ⟨_, hx.2⟩ i).comp x eL.symm.has_fderiv_at
        rw [← hIcc]
        refine' preimage_interior_subset_interior_preimage eL.continuous _
        simpa only [Set.mem_preimage, eL.apply_symm_apply, ← pi_univ_Icc,
          interior_pi_set finite_univ, interior_Icc] using hx.1
      · rw [← he_vol.integrable_on_comp_preimage he_emb, hIcc]
        simp [← hDF, (· ∘ ·), Hi]
    
#align measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv MeasureTheory.integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv

end

open scoped Interval

open ContinuousLinearMap (smul_right)

-- mathport name: «exprℝ¹»
local notation "ℝ¹" => Fin 1 → ℝ

-- mathport name: «exprℝ²»
local notation "ℝ²" => Fin 2 → ℝ

-- mathport name: «exprE¹»
local notation "E¹" => Fin 1 → E

-- mathport name: «exprE²»
local notation "E²" => Fin 2 → E

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also

* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` for a version that only assumes right
differentiability of `f`;

* `measure_theory.integral_eq_of_has_deriv_within_at_off_countable` for a version that works both
  for `a ≤ b` and `b ≤ a` at the expense of using unordered intervals instead of `set.Icc`. -/
theorem integral_eq_of_has_deriv_within_at_off_countable_of_le (f f' : ℝ → E) {a b : ℝ}
    (hle : a ≤ b) {s : Set ℝ} (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) (Hi : IntervalIntegrable f' volume a b) :
    (∫ x in a..b, f' x) = f b - f a :=
  by
  set e : ℝ ≃L[ℝ] ℝ¹ := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  have e_symm : ∀ x, e.symm x = x 0 := fun x => rfl
  set F' : ℝ → ℝ →L[ℝ] E := fun x => smul_right (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' : ∀ x y, F' x y = y • f' x := fun x y => rfl
  calc
    (∫ x in a..b, f' x) = ∫ x in Icc a b, f' x := by
      simp only [intervalIntegral.integral_of_le hle, set_integral_congr_set_ae Ioc_ae_eq_Icc]
    _ =
        ∑ i : Fin 1,
          (∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e a i) x) :=
      by
      simp only [← interior_Icc] at Hd 
      refine'
        integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _ (fun _ => f)
          (fun _ => F') s hs a b hle (fun i => Hc) (fun x hx i => Hd x hx) _ _ _
      · exact fun x y => (OrderIso.funUnique (Fin 1) ℝ).symm.le_iff_le
      · exact (volume_preserving_fun_unique (Fin 1) ℝ).symm _
      · intro x; rw [Fin.sum_univ_one, hF', e_symm, Pi.single_eq_same, one_smul]
      · rw [intervalIntegrable_iff_integrable_Ioc_of_le hle] at Hi 
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm
    _ = f b - f a := by
      simp only [Fin.sum_univ_one, e_symm]
      have : ∀ c : ℝ, const (Fin 0) c = isEmptyElim := fun c => Subsingleton.elim _ _
      simp [this, volume_pi, measure.pi_of_empty fun _ : Fin 0 => volume]
    
#align measure_theory.integral_eq_of_has_deriv_within_at_off_countable_of_le MeasureTheory.integral_eq_of_has_deriv_within_at_off_countable_of_le

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also `measure_theory.interval_integral.integral_eq_sub_of_has_deriv_right` for a version that
only assumes right differentiability of `f`.
-/
theorem integral_eq_of_has_deriv_within_at_off_countable (f f' : ℝ → E) {a b : ℝ} {s : Set ℝ}
    (hs : s.Countable) (Hc : ContinuousOn f [a, b])
    (Hd : ∀ x ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x)
    (Hi : IntervalIntegrable f' volume a b) : (∫ x in a..b, f' x) = f b - f a :=
  by
  cases' le_total a b with hab hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm, neg_eq_iff_eq_neg, neg_sub]
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi.symm
#align measure_theory.integral_eq_of_has_deriv_within_at_off_countable MeasureTheory.integral_eq_of_has_deriv_within_at_off_countable

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- **Divergence theorem** for functions on the plane along rectangles. It is formulated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle equals the integral of the normal derivative of `F` along the
boundary.

See also `measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead of the integral
over `Icc a b`. -/
theorem integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1 ..b.1, g (x, b.2)) - ∫ x in a.1 ..b.1, g (x, a.2)) +
          ∫ y in a.2 ..b.2, f (b.1, y)) -
        ∫ y in a.2 ..b.2, f (a.1, y) :=
  let e : (ℝ × ℝ) ≃L[ℝ] ℝ² := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          (∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e a i) x) :=
      by
      refine'
        integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _ ![f, g] ![f', g'] s
          hs a b hle _ (fun x hx => _) _ _ Hi
      · exact fun x y => (OrderIso.finTwoArrowIso ℝ).symm.le_iff_le
      · exact (volume_preserving_fin_two_arrow ℝ).symm _
      · exact Fin.forall_fin_two.2 ⟨Hcf, Hcg⟩
      · rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc] at hx 
        exact Fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩
      · intro x; rw [Fin.sum_univ_two]; simp
    _ =
        ((∫ y in Icc a.2 b.2, f (b.1, y)) - ∫ y in Icc a.2 b.2, f (a.1, y)) +
          ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) :=
      by
      have :
        ∀ (a b : ℝ¹) (f : ℝ¹ → E), (∫ x in Icc a b, f x) = ∫ x in Icc (a 0) (b 0), f fun _ => x :=
        by
        intro a b f
        convert
          (((volume_preserving_fun_unique (Fin 1) ℝ).symm _).set_integral_preimage_emb
              (MeasurableEquiv.measurableEmbedding _) _ _).symm
        exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc a b).symm
      simp only [Fin.sum_univ_two, this]
      rfl
    _ =
        (((∫ x in a.1 ..b.1, g (x, b.2)) - ∫ x in a.1 ..b.1, g (x, a.2)) +
            ∫ y in a.2 ..b.2, f (b.1, y)) -
          ∫ y in a.2 ..b.2, f (a.1, y) :=
      by
      simp only [intervalIntegral.integral_of_le hle.1, intervalIntegral.integral_of_le hle.2,
        set_integral_congr_set_ae Ioc_ae_eq_Icc]
      abel
    
#align measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le MeasureTheory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- **Divergence theorem** for functions on the plane. It is formulated in terms of two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j =1,2`, equals the integral of
the normal derivative of `F` along the boundary.

See also `measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`. -/
theorem integral2_divergence_prod_of_has_fderiv_within_at_off_countable (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f ([a₁, b₁] ×ˢ [a₂, b₂])) (Hcg : ContinuousOn g ([a₁, b₁] ×ˢ [a₂, b₂]))
    (Hdf :
      ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s, HasFDerivAt f (f' x) x)
    (Hdg :
      ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([a₁, b₁] ×ˢ [a₂, b₂])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) :=
  by
  wlog h₁ : a₁ ≤ b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁, min_comm b₁ a₁, max_comm b₁ a₁] at this 
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine' (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_le h₁))).trans _; abel
  wlog h₂ : a₂ ≤ b₂ generalizing a₂ b₂
  · specialize this b₂ a₂
    rw [uIcc_comm b₂ a₂, min_comm b₂ a₂, max_comm b₂ a₂] at this 
    simp only [intervalIntegral.integral_symm b₂ a₂, intervalIntegral.integral_neg]
    refine' (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_le h₂))).trans _; abel
  simp only [uIcc_of_le h₁, uIcc_of_le h₂, min_eq_left, max_eq_right, h₁, h₂] at Hcf Hcg Hdf Hdg Hi 
  calc
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
        ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) :=
      by
      simp only [intervalIntegral.integral_of_le, h₁, h₂, set_integral_congr_set_ae Ioc_ae_eq_Icc]
    _ = ∫ x in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f' x (1, 0) + g' x (0, 1) := (set_integral_prod _ Hi).symm
    _ =
        (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
          ∫ y in a₂..b₂, f (a₁, y) :=
      by
      rw [Icc_prod_Icc] at *
      apply
          integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le f g f' g'
            (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s <;>
        assumption
    
#align measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable MeasureTheory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable

end MeasureTheory

