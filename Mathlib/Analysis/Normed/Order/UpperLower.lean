/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Topology.Algebra.Order.UpperLower
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Upper/lower/order-connected sets in normed groups

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.

## TODO

Is there a way to generalise `IsClosed.upperClosure_pi`/`IsClosed.lowerClosure_pi` so that they also
apply to `ℝ`, `ℝ × ℝ`, `EuclideanSpace ι ℝ`? `_pi` has been appended to their names to disambiguate
from the other possible lemmas, but we will want there to be a single set of lemmas for all
situations.
-/

open Bornology Function Metric Set
open scoped Pointwise

variable {α ι : Type*}

section NormedOrderedGroup
variable [NormedCommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s : Set α}

@[to_additive IsUpperSet.thickening]
protected theorem IsUpperSet.thickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsLowerSet.thickening]
protected theorem IsLowerSet.thickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsUpperSet.cthickening]
protected theorem IsUpperSet.cthickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive IsLowerSet.cthickening]
protected theorem IsLowerSet.cthickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive upperClosure_interior_subset] lemma upperClosure_interior_subset' (s : Set α) :
    (upperClosure (interior s) : Set α) ⊆ interior (upperClosure s) :=
  upperClosure_min (interior_mono subset_upperClosure) (upperClosure s).upper.interior

@[to_additive lowerClosure_interior_subset] lemma lowerClosure_interior_subset' (s : Set α) :
    (lowerClosure (interior s) : Set α) ⊆ interior (lowerClosure s) :=
  lowerClosure_min (interior_mono subset_lowerClosure) (lowerClosure s).lower.interior

end NormedOrderedGroup

/-! ### `ℝⁿ` -/


section Finite
variable [Finite ι] {s : Set (ι → ℝ)} {x y : ι → ℝ}

theorem IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x ∈ closure s)
    (h : ∀ i, x i < y i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm']
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((lt_sub_iff_add_lt.2 <| hyz _).trans (hw _ <| mem_univ _).1).le

theorem IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x ∈ closure s)
    (h : ∀ i, y i < x i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm]
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((hw _ <| mem_univ _).2.trans <| hyz _).le

end Finite

section Fintype
variable [Fintype ι] {s : Set (ι → ℝ)} {a₁ a₂ b₁ b₂ x y : ι → ℝ} {δ : ℝ}

-- TODO: Generalise those lemmas so that they also apply to `ℝ` and `EuclideanSpace ι ℝ`
lemma dist_inf_sup_pi (x y : ι → ℝ) : dist (x ⊓ y) (x ⊔ y) = dist x y := by
  refine congr_arg NNReal.toReal (Finset.sup_congr rfl fun i _ ↦ ?_)
  simp only [Real.nndist_eq', max_sub_min_eq_abs, Pi.inf_apply,
    Pi.sup_apply, Real.nnabs_of_nonneg, abs_nonneg, Real.toNNReal_abs]

lemma dist_mono_left_pi : MonotoneOn (dist · y) (Ici y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy ↦ NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ ↦ ?_)
  rw [Real.nndist_eq, Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₁ i)),
    Real.nndist_eq, Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₂ i))]
  exact Real.toNNReal_mono (sub_le_sub_right (hy _) _)

lemma dist_mono_right_pi : MonotoneOn (dist x) (Ici x) := by
  simpa only [dist_comm _ x] using dist_mono_left_pi (y := x)

lemma dist_anti_left_pi : AntitoneOn (dist · y) (Iic y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy ↦ NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ ↦ ?_)
  rw [Real.nndist_eq', Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₂ i ≤ y i)),
    Real.nndist_eq', Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₁ i ≤ y i))]
  exact Real.toNNReal_mono (sub_le_sub_left (hy _) _)

lemma dist_anti_right_pi : AntitoneOn (dist x) (Iic x) := by
  simpa only [dist_comm] using dist_anti_left_pi (y := x)

lemma dist_le_dist_of_le_pi (ha : a₂ ≤ a₁) (h₁ : a₁ ≤ b₁) (hb : b₁ ≤ b₂) :
    dist a₁ b₁ ≤ dist a₂ b₂ :=
  (dist_mono_right_pi h₁ (h₁.trans hb) hb).trans <|
    dist_anti_left_pi (ha.trans <| h₁.trans hb) (h₁.trans hb) ha

theorem IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · rw [dist_self_add_left]
    refine (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq ?_
    simp only [norm_mul, norm_div, Real.norm_eq_abs]
    simp only [zero_lt_three, abs_of_pos, zero_lt_four, abs_of_pos hδ]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith

theorem IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · rw [dist_self_sub_left]
    refine (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq ?_
    simp only [norm_mul, norm_div, Real.norm_eq_abs, zero_lt_three, abs_of_pos,
      zero_lt_four, abs_of_pos hδ]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith

end Fintype

section Finite
variable [Finite ι] {s : Set (ι → ℝ)}

/-!
#### Note

The closure and frontier of an antichain might not be antichains. Take for example the union
of the open segments from `(0, 2)` to `(1, 1)` and from `(2, 1)` to `(3, 0)`. `(1, 1)` and `(2, 1)`
are comparable and both in the closure/frontier.
-/

protected lemma IsClosed.upperClosure_pi (hs : IsClosed s) (hs' : BddBelow s) :
    IsClosed (upperClosure s : Set (ι → ℝ)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx ↦ ?_
  choose g hg hgf using hf
  obtain ⟨a, ha⟩ := hx.bddAbove_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddAbove_Iic) fun n ↦
    ⟨hg n, (hgf _).trans <| ha <| mem_range_self _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' hbf (hx.comp hφ.tendsto_atTop) fun _ ↦ hgf _⟩

protected lemma IsClosed.lowerClosure_pi (hs : IsClosed s) (hs' : BddAbove s) :
    IsClosed (lowerClosure s : Set (ι → ℝ)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx ↦ ?_
  choose g hg hfg using hf
  haveI : BoundedGENhdsClass ℝ := by infer_instance
  obtain ⟨a, ha⟩ := hx.bddBelow_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddBelow_Ici) fun n ↦
    ⟨hg n, (ha <| mem_range_self _).trans <| hfg _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' (hx.comp hφ.tendsto_atTop) hbf fun _ ↦ hfg _⟩

protected lemma IsClopen.upperClosure_pi (hs : IsClopen s) (hs' : BddBelow s) :
    IsClopen (upperClosure s : Set (ι → ℝ)) := ⟨hs.1.upperClosure_pi hs', hs.2.upperClosure⟩

protected lemma IsClopen.lowerClosure_pi (hs : IsClopen s) (hs' : BddAbove s) :
    IsClopen (lowerClosure s : Set (ι → ℝ)) := ⟨hs.1.lowerClosure_pi hs', hs.2.lowerClosure⟩

lemma closure_upperClosure_comm_pi (hs : BddBelow s) :
    closure (upperClosure s : Set (ι → ℝ)) = upperClosure (closure s) :=
  (closure_minimal (upperClosure_anti subset_closure) <|
      isClosed_closure.upperClosure_pi hs.closure).antisymm <|
    upperClosure_min (closure_mono subset_upperClosure) (upperClosure s).upper.closure

lemma closure_lowerClosure_comm_pi (hs : BddAbove s) :
    closure (lowerClosure s : Set (ι → ℝ)) = lowerClosure (closure s) :=
  (closure_minimal (lowerClosure_mono subset_closure) <|
        isClosed_closure.lowerClosure_pi hs.closure).antisymm <|
    lowerClosure_min (closure_mono subset_lowerClosure) (lowerClosure s).lower.closure

end Finite
