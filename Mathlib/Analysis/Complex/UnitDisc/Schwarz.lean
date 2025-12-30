/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.UnitDisc.Shift

/-!
# Schwarz-Pick lemma for maps from a ball

In this file we prove a version of the Schwarz lemma that estimates `dist (f z) (f w)`
for two points of a disc where `f` is complex differentiable and is bounded.

As a corollary, we prove a similar estimate for a function bounded on a polydisc,
then use it to show that a function that is separately holomorphic on a polydisc `U`
and is bounded on `U` is continuous on `U`.

The latter lemma is a step towards Hartogs's theorem
saying that a function that is separately holomorphic must be holomorphic.
-/

open Function Set Metric
open scoped BigOperators ComplexConjugate Complex.UnitDisc Topology

public section

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} {r R : ℝ}

/-- **Schwarz-Pick lemma** for a map from a disc in `ℂ` to a disc in a normed space,
estimating the distance between the images of two points in the disc.

This version assumes that the disc in the codomain
is centered around the image of one of the points. -/
theorem dist_le_of_mapsTo_ball_of_mem {z w : ℂ} (hd : DifferentiableOn ℂ f (ball c r))
    (h_maps : MapsTo f (ball c r) (closedBall (f z) R))
    (hz : z ∈ ball c r) (hw : w ∈ ball c r) :
    dist (f z) (f w) ≤ R * r * dist z w / ‖r ^ 2 - conj (z - c) * (w - c)‖ := by
  wlog H : c = 0 ∧ r = 1
  · set g : ℂ → ℂ := fun x ↦ c + r • x
    have hr₀ : 0 < r := nonempty_ball.mp ⟨z, hz⟩
    have hg_img : g '' ball 0 1 = ball c r := by
      simpa only [g, ← image_smul, ← image_vadd, image_image] using affinity_unitBall hr₀ c
    rw [← hg_img, mem_image] at hz hw
    rcases hz with ⟨z, hz, rfl⟩
    rcases hw with ⟨w, hw, rfl⟩
    replace hd : DifferentiableOn ℂ (f ∘ g) (ball 0 1) :=
      hd.comp (by fun_prop) (hg_img ▸ mapsTo_image _ _)
    replace h_maps : MapsTo (f ∘ g) (ball 0 1) (closedBall (f (g z)) R) :=
      h_maps.comp (hg_img ▸ mapsTo_image _ _)
    convert this hd h_maps hz hw ⟨rfl, rfl⟩ using 1
    simp [g, dist_eq_norm, ← mul_sub, abs_of_pos hr₀, mul_mul_mul_comm (r : ℂ) _ (r : ℂ), ← sq,
      ← mul_one_sub]
    field_simp
  rcases H with ⟨rfl, rfl⟩
  rw [mem_ball_zero_iff] at hz hw
  lift z to 𝔻 using hz
  lift w to 𝔻 using hw
  set g : ℂ → ℂ := fun x ↦ (z + x) / (1 + conj ↑z * x)
  have hg_coe : ∀ x : 𝔻, g x = z.shift x := by simp [g, UnitDisc.coe_shift]
  have hg_maps : MapsTo g (ball 0 1) (ball 0 1) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx ⊢
    lift x to 𝔻 using hx
    simpa only [hg_coe] using (z.shift x).norm_lt_one
  have hg_img : g '' ball 0 1 = ball 0 1 := by
    refine hg_maps.image_subset.antisymm fun x hx ↦ ?_
    rw [mem_ball_zero_iff] at hx
    use (-z).shift (.mk x hx), Subtype.prop _
    simpa only [UnitDisc.coe_shift, g, ← UnitDisc.coe_inj]
      using UnitDisc.shift_apply_shift_neg z (.mk x hx)
  have hg₀ : g 0 = z := by simp [g]
  replace hd : DifferentiableOn ℂ (f ∘ g) (ball 0 1) := by
    refine hd.comp (fun x hx ↦ ?_) hg_maps
    have : 1 + conj (z : ℂ) * x ≠ 0 := z.shift_den_ne_zero ⟨x, hx⟩
    fun_prop (disch := assumption)
  convert dist_le_div_mul_dist_of_mapsTo_ball hd
    (by simpa only [Function.comp_apply, hg₀] using h_maps.comp hg_maps)
    (z := (-z).shift w) (Subtype.prop _) using 1
  · simp [hg_coe, hg₀, dist_comm]
  · simp [UnitDisc.coe_shift, dist_eq_norm_sub', ← sub_eq_neg_add, ← sub_eq_add_neg, mul_div_assoc]

/-- Give a function that is separately holomorphic on an open polydisc and is bounded on it,
this lemma provides an explicit estimate on the distance between the images of any two points. -/
theorem dist_le_of_differentiableOn_update_of_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → E} {c : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (hfd : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ i,
      DifferentiableOn ℂ (f ∘ update z i) (ball (c i) (r i)))
    (hM : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ‖f z‖ ≤ M)
    {z w : ι → ℂ} (hz : z ∈ univ.pi fun i ↦ ball (c i) (r i))
    (hw : w ∈ univ.pi fun i ↦ ball (c i) (r i)) :
    dist (f z) (f w) ≤ 2 * M * ∑ i,
      r i * dist (z i) (w i) / ‖r i ^ 2 - conj (z i - c i) * (w i - c i)‖ := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  set z' : Fin (n + 1) → ι → ℂ := fun k i ↦ if (e i).castSucc < k then w i else z i
  have hz'_dist (i : ι) :
      dist (f (z' (e i).castSucc)) (f (z' (e i).succ)) ≤
        2 * M * r i * dist (z i) (w i) / ‖r i ^ 2 - conj (z i - c i) * (w i - c i)‖ := by
    simp only [mem_univ_pi, mem_ball] at *
    set g : ℂ → E := f ∘ update (z' (e i).castSucc) i
    have hgd : DifferentiableOn ℂ g (ball (c i) (r i)) := by
      refine hfd (z' (e i).castSucc) (fun j ↦ ?_) i
      by_cases H : e j < e i <;> simp [z', H, hz, hw]
    have hmaps : MapsTo g (ball (c i) (r i)) (closedBall (g (z i)) (2 * M)) := by
      intro x hx
      rw [mem_ball] at hx
      rw [mem_closedBall, two_mul]
      refine (dist_le_norm_add_norm _ _).trans (add_le_add ?_ ?_) <;> apply hM <;>
        · intro j
          rcases eq_or_ne j i with rfl | hj <;> [skip; by_cases H : e j < e i] <;> simp [z', *]
    convert dist_le_of_mapsTo_ball_of_mem (w := w i) hgd hmaps (by simp [hz]) (by simp [hw])
      using 1
    simp only [g, Function.comp_apply]
    congr 2 with j <;>
      rcases eq_or_ne j i with rfl | hj <;> simp [z', *, le_iff_eq_or_lt]
  calc
    dist (f z) (f w) ≤ ∑ k : Fin n, dist (f (z' k.castSucc)) (f (z' k.succ)) := by
      rw [Finset.sum_fin_eq_sum_range]
      convert dist_le_range_sum_dist (fun i ↦ if h : i < n + 1 then f (z' ⟨i, h⟩) else 0) n
        with i hi
      · simp [z', Fin.lt_def]
      · rw [Finset.mem_range] at hi
        simp [hi, hi.trans n.lt_add_one]
    _ ≤ _ := by
      rw [← e.sum_comp, Finset.mul_sum]
      gcongr with i hi
      simpa [mul_assoc, mul_div_assoc] using hz'_dist i

/-- A function that is separately holomorphic and is bounded on a polydisc
must be continuous on the same polydisc.

This is a preliminary lemma that is needed to prove Hartogs's theorem
saying that the first assumption is enough to conclude that the function is in fact analytic
on the polydisc. -/
theorem continuousOn_of_differentiableOn_update_of_bddAbove {ι : Type*} [Finite ι] [DecidableEq ι]
    {f : (ι → ℂ) → E} {c : ι → ℂ} {r : ι → ℝ}
    (hfd : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ i,
      DifferentiableOn ℂ (f ∘ update z i) (ball (c i) (r i)))
    (hbdd : BddAbove ((‖f ·‖) '' univ.pi fun i ↦ ball (c i) (r i))) :
    ContinuousOn f (univ.pi fun i ↦ ball (c i) (r i)) := by
  rcases nonempty_fintype ι
  rcases hbdd with ⟨M, hM⟩
  rw [mem_upperBounds, forall_mem_image] at hM
  intro z hz
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
    (eventually_mem_nhdsWithin.mono fun _ h ↦
      dist_le_of_differentiableOn_update_of_norm_le hfd hM h hz) ?_
  convert ContinuousWithinAt.tendsto _
  · simp
  · refine .const_mul _ <| tendsto_finset_sum _ fun i hi ↦ .div ?_ ?_ ?_
    · exact Continuous.continuousWithinAt (by fun_prop)
    · exact Continuous.continuousWithinAt (by fun_prop)
    · rw [norm_ne_zero_iff, sub_ne_zero, conj_mul']
      norm_cast
      refine ne_of_gt ?_
      gcongr
      simpa using hz i

end Complex
