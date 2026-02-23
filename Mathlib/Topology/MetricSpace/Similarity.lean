/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Congruence
public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Tactic.FinCases

/-!
# Similarities

This file defines `Similar`, i.e., the equivalence between indexed sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example is
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

Let `P₁` and `P₂` be metric spaces, let `ι` be an index set, and let `v₁ : ι → P₁` and
`v₂ : ι → P₂` be indexed families of points.

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

@[expose] public section

open scoped NNReal

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

/-- Similarity between indexed sets of vertices v₁ and v₂.
Use `open scoped Similar` to access the `v₁ ∼ v₂` notation. -/
def Similar (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar

/-- Similarity holds if and only if all extended distances are proportional. -/
lemma similar_iff_exists_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) :=
  Iff.rfl

/-- Similarity holds if and only if all extended distances between points with different
indices are proportional. -/
lemma similar_iff_exists_pairwise_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ ↦ ?_⟩
  · exact fun _ ↦ h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi

lemma Congruent.similar {v₁ : ι → P₁} {v₂ : ι → P₂} (h : Congruent v₁ v₂) : Similar v₁ v₂ :=
  ⟨1, one_ne_zero, fun i₁ i₂ ↦ by simpa using h i₁ i₂⟩

namespace Similar

/-- A similarity scales extended distance. Forward direction of `similar_iff_exists_edist_eq`. -/
alias ⟨exists_edist_eq, _⟩ := similar_iff_exists_edist_eq

/-- Similarity follows from scaled extended distance. Backward direction of
`similar_iff_exists_edist_eq`. -/
alias ⟨_, of_exists_edist_eq⟩ := similar_iff_exists_edist_eq

/-- A similarity pairwise scales extended distance. Forward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨exists_pairwise_edist_eq, _⟩ := similar_iff_exists_pairwise_edist_eq

/-- Similarity follows from pairwise scaled extended distance. Backward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨_, of_exists_pairwise_edist_eq⟩ := similar_iff_exists_pairwise_edist_eq

@[refl] protected lemma refl (v₁ : ι → P₁) : v₁ ∼ v₁ :=
  ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩

@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff _ ENNReal.coe_ne_top, h]
  norm_cast

lemma _root_.similar_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨Similar.symm, Similar.symm⟩

@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ := by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul, mul_assoc, h₁, h₂]

/-- Change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ∼ v₂) (f : ι' → ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

/-- Change between equivalent index sets ι and ι'. -/
@[simp]
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ := by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

/-- Families with at most a single point are always similar. -/
@[nontriviality, simp]
lemma of_subsingleton_index [Subsingleton ι] : v₁ ∼ v₂ :=
  Congruent.of_subsingleton_index.similar

/-! Similarity is preserved under dilations. -/

section Dilation
variable {F}

lemma comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) (h : v₁ ∼ v₂) :
    f ∘ v₁ ∼ v₂ :=
  .trans ⟨Dilation.ratio f, Dilation.ratio_ne_zero f, fun _ _ => Dilation.edist_eq f _ _⟩ h

lemma comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  .symm (h.symm.comp_left f)

@[simp]
lemma comp_left_iff [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
  ⟨.trans <| .comp_right f (.refl _), .comp_left f⟩

@[simp]
lemma comp_right_iff [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ := by
  rw [similar_comm, comp_left_iff, similar_comm]

end Dilation

/-! Similarity is preserved under isometries.

While these are trivial consequences of the dilation results, they avoid ending up with a
`toDilation` in the expression, and so are easier to apply to plain functions.
If `Dilation` were a predicate like `Isometry` then these would not be needed.
-/

section Isometry

lemma comp_isometry_left {f : P₁ → P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂ :=
  comp_left hf.toDilation h

lemma comp_isometry_right {f : P₂ → P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  comp_right hf.toDilation h

@[simp]
lemma comp_isometry_left_iff {f : P₁ → P₃} (hf : Isometry f) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
  comp_left_iff hf.toDilation

@[simp]
lemma comp_isometry_right_iff {f : P₂ → P₃} (hf : Isometry f) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ :=
  comp_right_iff hf.toDilation

end Isometry

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/-- Swapping the first two vertices preserves similarity. -/
theorem comm_left (h : ![a, b, c] ∼ ![a', b', c']) :
    ![b, a, c] ∼ ![b', a', c'] := by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/-- Swapping the last two vertices preserves similarity. -/
theorem comm_right (h : ![a, b, c] ∼ ![a', b', c']) :
    ![a, c, b] ∼ ![a', c', b'] := by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/-- Reversing the order of vertices preserves similarity. -/
theorem reverse_of_three (h : ![a, b, c] ∼ ![a', b', c']) :
    ![c, b, a] ∼ ![c', b', a'] :=
  h.comm_left.comm_right.comm_left

end Triangle

end Similar

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/-- Similarity holds if and only if all non-negative distances are proportional. -/
lemma similar_iff_exists_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) :=
  exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

/-- Similarity holds if and only if all non-negative distances between points with different
indices are proportional. -/
lemma similar_iff_exists_pairwise_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional. -/
lemma similar_iff_exists_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) :=
  similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

/-- Similarity holds if and only if all distances between points with different indices are
proportional. -/
lemma similar_iff_exists_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional with a positive real ratio. -/
lemma similar_iff_exists_pos_dist_eq : Similar v₁ v₂ ↔
    (∃ r : ℝ, 0 < r ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

/-- Similarity holds iff pairwise distances are proportional with a positive ratio. -/
lemma similar_iff_exists_pos_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ, 0 < r ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

namespace Similar

/-- A similarity scales non-negative distance. Forward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨exists_nndist_eq, _⟩ := similar_iff_exists_nndist_eq

/-- Similarity follows from scaled non-negative distance. Backward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨_, of_exists_nndist_eq⟩ := similar_iff_exists_nndist_eq

/-- A similarity scales distance. Forward direction of `similar_iff_exists_dist_eq`. -/
alias ⟨exists_dist_eq, _⟩ := similar_iff_exists_dist_eq

/-- Similarity follows from scaled distance. Backward direction of
`similar_iff_exists_dist_eq`. -/
alias ⟨_, of_exists_dist_eq⟩ := similar_iff_exists_dist_eq

/-- A similarity pairwise scales non-negative distance. Forward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨exists_pairwise_nndist_eq, _⟩ := similar_iff_exists_pairwise_nndist_eq

/-- Similarity follows from pairwise scaled non-negative distance. Backward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨_, of_exists_pairwise_nndist_eq⟩ := similar_iff_exists_pairwise_nndist_eq

/-- A similarity pairwise scales distance. Forward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨exists_pairwise_dist_eq, _⟩ := similar_iff_exists_pairwise_dist_eq

/-- Similarity follows from pairwise scaled distance. Backward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pairwise_dist_eq⟩ := similar_iff_exists_pairwise_dist_eq

/-- Scales distance with positive ratio. Forward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨exists_pos_dist_eq, _⟩ := similar_iff_exists_pos_dist_eq

/-- Similarity from scaled positive distance. Backward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨_, of_exists_pos_dist_eq⟩ := similar_iff_exists_pos_dist_eq

/-- Scales pairwise distance with positive ratio. Forward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨exists_pos_pairwise_dist_eq, _⟩ := similar_iff_exists_pos_pairwise_dist_eq

/-- Similarity from scaled pairwise positive distance. Backward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pos_pairwise_dist_eq⟩ := similar_iff_exists_pos_pairwise_dist_eq

end Similar

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/-- If two triangles have two pairs of proportional adjacent sides, then the triangles are similar.
-/
theorem similar_of_dist_mul_eq_dist_mul_eq (h_ne : dist a b ≠ 0) (h_ne' : dist a' b' ≠ 0)
    (heq1 : dist a b * dist b' c' = dist b c * dist a' b')
    (heq2 : dist a b * dist c' a' = dist c a * dist a' b') :
    Similar ![a, b, c] ![a', b', c'] := by
  set r : ℝ := (dist a b / dist a' b') with hr
  have hr_pos : 0 < r := by positivity
  apply Similar.of_exists_pos_pairwise_dist_eq
  use r
  refine ⟨hr_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

alias similar_of_side_side := similar_of_dist_mul_eq_dist_mul_eq

end Triangle

end PseudoMetricSpace
