/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Module.LocallyConvex

#align_import analysis.locally_convex.with_seminorms from "leanprover-community/mathlib"@"b31173ee05c911d61ad6a05bd2196835c932e0ec"

/-!
# Topology induced by a family of seminorms

## Main definitions

* `SeminormFamily.basisSets`: The set of open seminorm balls for a family of seminorms.
* `SeminormFamily.moduleFilterBasis`: A module filter basis formed by the open balls.
* `Seminorm.IsBounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `WithSeminorms.toLocallyConvexSpace`: A space equipped with a family of seminorms is locally
convex.
* `WithSeminorms.firstCountable`: A space is first countable if it's topology is induced by a
countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `Seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`LinearMap.continuous_of_locally_bounded` this gives general criterion for continuity.

* `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/


open NormedField Set Seminorm TopologicalSpace Filter List

open BigOperators NNReal Pointwise Topology Uniformity

variable {𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section FilterBasis

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable (𝕜 E ι)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbrev SeminormFamily :=
  ι → Seminorm 𝕜 E
#align seminorm_family SeminormFamily

variable {𝕜 E ι}

namespace SeminormFamily

/-- The sets of a filter basis for the neighborhood filter of 0. -/
def basisSets (p : SeminormFamily 𝕜 E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)
#align seminorm_family.basis_sets SeminormFamily.basisSets

variable (p : SeminormFamily 𝕜 E ι)

theorem basisSets_iff {U : Set E} :
    U ∈ p.basisSets ↔ ∃ (i : Finset ι) (r : _) (_ : 0 < r), U = ball (i.sup p) 0 r := by
  simp only [basisSets, mem_iUnion, mem_singleton_iff]
  -- 🎉 no goals
#align seminorm_family.basis_sets_iff SeminormFamily.basisSets_iff

theorem basisSets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩
#align seminorm_family.basis_sets_mem SeminormFamily.basisSets_mem

theorem basisSets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩
                                        -- 🎉 no goals
#align seminorm_family.basis_sets_singleton_mem SeminormFamily.basisSets_singleton_mem

theorem basisSets_nonempty [Nonempty ι] : p.basisSets.Nonempty := by
  let i := Classical.arbitrary ι
  -- ⊢ Set.Nonempty (basisSets p)
  refine' nonempty_def.mpr ⟨(p i).ball 0 1, _⟩
  -- ⊢ ball (p i) 0 1 ∈ basisSets p
  exact p.basisSets_singleton_mem i zero_lt_one
  -- 🎉 no goals
#align seminorm_family.basis_sets_nonempty SeminormFamily.basisSets_nonempty

theorem basisSets_intersect (U V : Set E) (hU : U ∈ p.basisSets) (hV : V ∈ p.basisSets) :
    ∃ z ∈ p.basisSets, z ⊆ U ∩ V := by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
    refine' ⟨p.basisSets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩
    rw [hU, hV, ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
      ball_finset_sup_eq_iInter _ _ _ hr₁, ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_left _ _ hi, ball_mono <| min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_right _ _ hi, ball_mono <| min_le_right _ _⟩)
#align seminorm_family.basis_sets_intersect SeminormFamily.basisSets_intersect

theorem basisSets_zero (U) (hU : U ∈ p.basisSets) : (0 : E) ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  -- ⊢ 0 ∈ U
  rw [hU, mem_ball_zero, map_zero]
  -- ⊢ 0 < r
  exact hr
  -- 🎉 no goals
#align seminorm_family.basis_sets_zero SeminormFamily.basisSets_zero

theorem basisSets_add (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V + V ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∃ V, V ∈ basisSets p ∧ V + V ⊆ U
  use (s.sup p).ball 0 (r / 2)
  -- ⊢ ball (Finset.sup s p) 0 (r / 2) ∈ basisSets p ∧ ball (Finset.sup s p) 0 (r / …
  refine' ⟨p.basisSets_mem s (div_pos hr zero_lt_two), _⟩
  -- ⊢ ball (Finset.sup s p) 0 (r / 2) + ball (Finset.sup s p) 0 (r / 2) ⊆ U
  refine' Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) _
  -- ⊢ ball (Finset.sup s p) (0 + 0) (r / 2 + r / 2) ⊆ U
  rw [hU, add_zero, add_halves']
  -- 🎉 no goals
#align seminorm_family.basis_sets_add SeminormFamily.basisSets_add

theorem basisSets_neg (U) (hU' : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  -- ⊢ ∃ V, V ∈ basisSets p ∧ V ⊆ (fun x => -x) ⁻¹' U
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  -- ⊢ ∃ V, V ∈ basisSets p ∧ V ⊆ ball (Finset.sup s p) 0 r
  exact ⟨U, hU', Eq.subset hU⟩
  -- 🎉 no goals
#align seminorm_family.basis_sets_neg SeminormFamily.basisSets_neg

/-- The `addGroupFilterBasis` induced by the filter basis `Seminorm.basisSets`. -/
protected def addGroupFilterBasis [Nonempty ι] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg
#align seminorm_family.add_group_filter_basis SeminormFamily.addGroupFilterBasis

theorem basisSets_smul_right (v : E) (U : Set E) (hU : U ∈ p.basisSets) :
    ∀ᶠ x : 𝕜 in 𝓝 0, x • v ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∀ᶠ (x : 𝕜) in 𝓝 0, x • v ∈ U
  rw [hU, Filter.eventually_iff]
  -- ⊢ {x | x • v ∈ ball (Finset.sup s p) 0 r} ∈ 𝓝 0
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  -- ⊢ {x | ‖x‖ * ↑(Finset.sup s p) v < r} ∈ 𝓝 0
  by_cases h : 0 < (s.sup p) v
  -- ⊢ {x | ‖x‖ * ↑(Finset.sup s p) v < r} ∈ 𝓝 0
  · simp_rw [(lt_div_iff h).symm]
    -- ⊢ {x | ‖x‖ < r / ↑(Finset.sup s p) v} ∈ 𝓝 0
    rw [← _root_.ball_zero_eq]
    -- ⊢ Metric.ball 0 (r / ↑(Finset.sup s p) v) ∈ 𝓝 0
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
    -- 🎉 no goals
  simp_rw [le_antisymm (not_lt.mp h) (map_nonneg _ v), mul_zero, hr]
  -- ⊢ {x | True} ∈ 𝓝 0
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)
  -- 🎉 no goals
#align seminorm_family.basis_sets_smul_right SeminormFamily.basisSets_smul_right

variable [Nonempty ι]

theorem basisSets_smul (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ 𝓝 (0 : 𝕜), ∃ W ∈ p.addGroupFilterBasis.sets, V • W ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∃ V, V ∈ 𝓝 0 ∧ ∃ W, W ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V • W ⊆ U
  refine' ⟨Metric.ball 0 r.sqrt, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), _⟩
  -- ⊢ ∃ W, W ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ Metric.ball 0 (Real.sqrt r …
  refine' ⟨(s.sup p).ball 0 r.sqrt, p.basisSets_mem s (Real.sqrt_pos.mpr hr), _⟩
  -- ⊢ Metric.ball 0 (Real.sqrt r) • ball (Finset.sup s p) 0 (Real.sqrt r) ⊆ U
  refine' Set.Subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _
  -- ⊢ ball (Finset.sup s p) 0 (Real.sqrt r * Real.sqrt r) ⊆ U
  rw [hU, Real.mul_self_sqrt (le_of_lt hr)]
  -- 🎉 no goals
#align seminorm_family.basis_sets_smul SeminormFamily.basisSets_smul

theorem basisSets_smul_left (x : 𝕜) (U : Set E) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.addGroupFilterBasis.sets, V ⊆ (fun y : E => x • y) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun y => x • y) ⁻¹' U
  rw [hU]
  -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun y => x • y) ⁻¹' b …
  by_cases h : x ≠ 0
  -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun y => x • y) ⁻¹' b …
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ ball (Finset.sup s p)  …
    use (s.sup p).ball 0 (r / ‖x‖)
    -- ⊢ ball (Finset.sup s p) 0 (r / ‖x‖) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ …
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
    -- 🎉 no goals
  refine' ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, _⟩
  -- ⊢ ball (Finset.sup s p) 0 r ⊆ (fun y => x • y) ⁻¹' ball (Finset.sup s p) 0 r
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]
#align seminorm_family.basis_sets_smul_left SeminormFamily.basisSets_smul_left

/-- The `moduleFilterBasis` induced by the filter basis `Seminorm.basisSets`. -/
protected def moduleFilterBasis : ModuleFilterBasis 𝕜 E where
  toAddGroupFilterBasis := p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right
#align seminorm_family.module_filter_basis SeminormFamily.moduleFilterBasis

theorem filter_eq_iInf (p : SeminormFamily 𝕜 E ι) :
    p.moduleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) := by
  refine' le_antisymm (le_iInf fun i => _) _
  -- ⊢ FilterBasis.filter AddGroupFilterBasis.toFilterBasis ≤ comap (↑(p i)) (𝓝 0)
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    -- ⊢ ∃ i_1, i_1 ∈ AddGroupFilterBasis.toFilterBasis ∧ id i_1 ⊆ ↑(p i) ⁻¹' Metric. …
    refine' ⟨(p i).ball 0 ε, _, _⟩
    -- ⊢ ball (p i) 0 ε ∈ AddGroupFilterBasis.toFilterBasis
    · rw [← (Finset.sup_singleton : _ = p i)]
      -- ⊢ ball (Finset.sup {i} p) 0 ε ∈ AddGroupFilterBasis.toFilterBasis
      exact p.basisSets_mem {i} hε
      -- 🎉 no goals
    · rw [id, (p i).ball_zero_eq_preimage_ball]
      -- 🎉 no goals
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    -- ⊢ ∀ (i' : Set E), i' ∈ AddGroupFilterBasis.toFilterBasis → id i' ∈ ⨅ (i : ι),  …
    rintro U (hU : U ∈ p.basisSets)
    -- ⊢ id U ∈ ⨅ (i : ι), comap (↑(p i)) (𝓝 0)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    -- ⊢ id (ball (Finset.sup s p) 0 r) ∈ ⨅ (i : ι), comap (↑(p i)) (𝓝 0)
    rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr, s.iInter_mem_sets]
    -- ⊢ ∀ (i : ι), i ∈ s → ball (p i) 0 r ∈ ⨅ (i : ι), comap (↑(p i)) (𝓝 0)
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩
#align seminorm_family.filter_eq_infi SeminormFamily.filter_eq_iInf

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

-- Todo: This should be phrased entirely in terms of the von Neumann bornology.
/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p
#align seminorm.is_bounded Seminorm.IsBounded

theorem isBounded_const (ι' : Type*) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι) (C : ℝ≥0), q.comp f ≤ C • s.sup p := by
  simp only [IsBounded, forall_const]
  -- 🎉 no goals
#align seminorm.is_bounded_const Seminorm.isBounded_const

theorem const_isBounded (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) : IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0, (q i).comp f ≤ C • p := by
  constructor <;> intro h i
  -- ⊢ IsBounded (fun x => p) q f → ∀ (i : ι'), ∃ C, comp (q i) f ≤ C • p
                  -- ⊢ ∃ C, comp (q i) f ≤ C • p
                  -- ⊢ ∃ s C, comp (q i) f ≤ C • Finset.sup s fun x => p
  · rcases h i with ⟨s, C, h⟩
    -- ⊢ ∃ C, comp (q i) f ≤ C • p
    exact ⟨C, le_trans h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)⟩
    -- 🎉 no goals
  use {Classical.arbitrary ι}
  -- ⊢ ∃ C, comp (q i) f ≤ C • Finset.sup {Classical.arbitrary ι} fun x => p
  simp only [h, Finset.sup_singleton]
  -- 🎉 no goals
#align seminorm.const_is_bounded Seminorm.const_isBounded

theorem isBounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F}
    (hf : IsBounded p q f) (s' : Finset ι') :
    ∃ (C : ℝ≥0) (s : Finset ι), (s'.sup q).comp f ≤ C • s.sup p := by
  classical
    obtain rfl | _ := s'.eq_empty_or_nonempty
    · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
    choose fₛ fC hf using hf
    use s'.card • s'.sup fC, Finset.biUnion s' fₛ
    have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
      intro i hi
      refine' (hf i).trans (smul_le_smul _ (Finset.le_sup hi))
      exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
    refine' (comp_mono f (finset_sup_le_sum q s')).trans _
    simp_rw [← pullback_apply, map_sum, pullback_apply]
    refine' (Finset.sum_le_sum hs).trans _
    rw [Finset.sum_const, smul_assoc]
#align seminorm.is_bounded_sup Seminorm.isBounded_sup

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E] : Prop where
  topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology
#align with_seminorms WithSeminorms

theorem WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology :=
  hp.1
#align with_seminorms.with_seminorms_eq WithSeminorms.withSeminorms_eq

variable [TopologicalSpace E]

variable {p : SeminormFamily 𝕜 E ι}

theorem WithSeminorms.topologicalAddGroup (hp : WithSeminorms p) : TopologicalAddGroup E := by
  rw [hp.withSeminorms_eq]
  -- ⊢ TopologicalAddGroup E
  exact AddGroupFilterBasis.isTopologicalAddGroup _
  -- 🎉 no goals
#align with_seminorms.topological_add_group WithSeminorms.topologicalAddGroup

theorem WithSeminorms.continuousSMul (hp : WithSeminorms p) : ContinuousSMul 𝕜 E := by
  rw [hp.withSeminorms_eq]
  -- ⊢ ContinuousSMul 𝕜 E
  exact ModuleFilterBasis.continuousSMul _
  -- 🎉 no goals

theorem WithSeminorms.hasBasis (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id := by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  -- ⊢ HasBasis (𝓝 0) (fun s => s ∈ SeminormFamily.basisSets p) id
  exact AddGroupFilterBasis.nhds_zero_hasBasis _
  -- 🎉 no goals
#align with_seminorms.has_basis WithSeminorms.hasBasis

theorem WithSeminorms.hasBasis_zero_ball (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2 := by
  refine' ⟨fun V => _⟩
  -- ⊢ V ∈ 𝓝 0 ↔ ∃ i, 0 < i.snd ∧ ball (Finset.sup i.fst p) 0 i.snd ⊆ V
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists]
  -- ⊢ (∃ i, (∃ i_1 r x, i = ball (Finset.sup i_1 p) 0 r) ∧ id i ⊆ V) ↔ ∃ a b, 0 <  …
  constructor
  -- ⊢ (∃ i, (∃ i_1 r x, i = ball (Finset.sup i_1 p) 0 r) ∧ id i ⊆ V) → ∃ a b, 0 <  …
  · rintro ⟨-, ⟨s, r, hr, rfl⟩, hV⟩
    -- ⊢ ∃ a b, 0 < b ∧ ball (Finset.sup a p) 0 b ⊆ V
    exact ⟨s, r, hr, hV⟩
    -- 🎉 no goals
  · rintro ⟨s, r, hr, hV⟩
    -- ⊢ ∃ i, (∃ i_1 r x, i = ball (Finset.sup i_1 p) 0 r) ∧ id i ⊆ V
    exact ⟨_, ⟨s, r, hr, rfl⟩, hV⟩
    -- 🎉 no goals
#align with_seminorms.has_basis_zero_ball WithSeminorms.hasBasis_zero_ball

theorem WithSeminorms.hasBasis_ball (hp : WithSeminorms p) {x : E} :
    (𝓝 (x : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.2 := by
  have : TopologicalAddGroup E := hp.topologicalAddGroup
  -- ⊢ HasBasis (𝓝 x) (fun sr => 0 < sr.snd) fun sr => ball (Finset.sup sr.fst p) x …
  rw [← map_add_left_nhds_zero]
  -- ⊢ HasBasis (Filter.map ((fun x x_1 => x + x_1) x) (𝓝 0)) (fun sr => 0 < sr.snd …
  convert hp.hasBasis_zero_ball.map ((· + ·) x) using 1
  -- ⊢ (fun sr => ball (Finset.sup sr.fst p) x sr.snd) = fun i => (fun x x_1 => x + …
  ext sr : 1
  -- ⊢ ball (Finset.sup sr.fst p) x sr.snd = (fun x x_1 => x + x_1) x '' ball (Fins …
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this
  -- 🎉 no goals
#align with_seminorms.has_basis_ball WithSeminorms.hasBasis_ball

/-- The `x`-neighbourhoods of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around `x`.-/
theorem WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) :
    U ∈ nhds x ↔ ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  rw [hp.hasBasis_ball.mem_iff, Prod.exists]
  -- 🎉 no goals
#align with_seminorms.mem_nhds_iff WithSeminorms.mem_nhds_iff

/-- The open sets of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around all of their points.-/
theorem WithSeminorms.isOpen_iff_mem_balls (hp : WithSeminorms p) (U : Set E) :
    IsOpen U ↔ ∀ x ∈ U, ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]
  -- 🎉 no goals
#align with_seminorms.is_open_iff_mem_balls WithSeminorms.isOpen_iff_mem_balls

/- Note that through the following lemmas, one also immediately has that separating families
of seminorms induce T₂ and T₃ topologies by `TopologicalAddGroup.t2Space`
and `TopologicalAddGroup.t3Space` -/
/-- A separating family of seminorms induces a T₁ topology. -/
theorem WithSeminorms.T1_of_separating (hp : WithSeminorms p)
    (h : ∀ x, x ≠ 0 → ∃ i, p i x ≠ 0) : T1Space E := by
  have := hp.topologicalAddGroup
  -- ⊢ T1Space E
  refine' TopologicalAddGroup.t1Space _ _
  -- ⊢ IsClosed {0}
  rw [← isOpen_compl_iff, hp.isOpen_iff_mem_balls]
  -- ⊢ ∀ (x : E), x ∈ {0}ᶜ → ∃ s r, r > 0 ∧ ball (Finset.sup s p) x r ⊆ {0}ᶜ
  rintro x (hx : x ≠ 0)
  -- ⊢ ∃ s r, r > 0 ∧ ball (Finset.sup s p) x r ⊆ {0}ᶜ
  cases' h x hx with i pi_nonzero
  -- ⊢ ∃ s r, r > 0 ∧ ball (Finset.sup s p) x r ⊆ {0}ᶜ
  refine' ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr _⟩
  -- ⊢ ¬0 ∈ ball (Finset.sup {i} p) x (↑(p i) x)
  rw [Finset.sup_singleton, mem_ball, zero_sub, map_neg_eq_map, not_lt]
  -- 🎉 no goals
#align with_seminorms.t1_of_separating WithSeminorms.T1_of_separating

/-- A family of seminorms inducing a T₁ topology is separating. -/
theorem WithSeminorms.separating_of_T1 [T1Space E] (hp : WithSeminorms p) (x : E) (hx : x ≠ 0) :
    ∃ i, p i x ≠ 0 := by
  have := ((t1Space_TFAE E).out 0 9).mp (inferInstanceAs <| T1Space E)
  -- ⊢ ∃ i, ↑(p i) x ≠ 0
  by_contra' h
  -- ⊢ False
  refine' hx (this _)
  -- ⊢ x ⤳ 0
  rw [hp.hasBasis_zero_ball.specializes_iff]
  -- ⊢ ∀ (i : Finset ι × ℝ), 0 < i.snd → x ∈ ball (Finset.sup i.fst p) 0 i.snd
  rintro ⟨s, r⟩ (hr : 0 < r)
  -- ⊢ x ∈ ball (Finset.sup (s, r).fst p) 0 (s, r).snd
  simp only [ball_finset_sup_eq_iInter _ _ _ hr, mem_iInter₂, mem_ball_zero, h, hr, forall_true_iff]
  -- 🎉 no goals
#align with_seminorms.separating_of_t1 WithSeminorms.separating_of_T1

/-- A family of seminorms is separating iff it induces a T₁ topology. -/
theorem WithSeminorms.separating_iff_T1 (hp : WithSeminorms p) :
    (∀ x, x ≠ 0 → ∃ i, p i x ≠ 0) ↔ T1Space E := by
  refine' ⟨WithSeminorms.T1_of_separating hp, _⟩
  -- ⊢ T1Space E → ∀ (x : E), x ≠ 0 → ∃ i, ↑(p i) x ≠ 0
  intro
  -- ⊢ ∀ (x : E), x ≠ 0 → ∃ i, ↑(p i) x ≠ 0
  exact WithSeminorms.separating_of_T1 hp
  -- 🎉 no goals
#align with_seminorms.separating_iff_t1 WithSeminorms.separating_iff_T1

end Topology

section Tendsto

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [TopologicalSpace E]

variable {p : SeminormFamily 𝕜 E ι}

/-- Convergence along filters for `WithSeminorms`.

Variant with `Finset.sup`. -/
theorem WithSeminorms.tendsto_nhds' (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔ ∀ (s : Finset ι) (ε), 0 < ε → ∀ᶠ x in f, s.sup p (u x - y₀) < ε :=
  by simp [hp.hasBasis_ball.tendsto_right_iff]
     -- 🎉 no goals
#align with_seminorms.tendsto_nhds' WithSeminorms.tendsto_nhds'

/-- Convergence along filters for `WithSeminorms`. -/
theorem WithSeminorms.tendsto_nhds (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds' u y₀]
  -- ⊢ (∀ (s : Finset ι) (ε : ℝ), 0 < ε → ∀ᶠ (x : F) in f, ↑(Finset.sup s p) (u x - …
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩
#align with_seminorms.tendsto_nhds WithSeminorms.tendsto_nhds

variable [SemilatticeSup F] [Nonempty F]

/-- Limit `→ ∞` for `WithSeminorms`. -/
theorem WithSeminorms.tendsto_nhds_atTop (hp : WithSeminorms p) (u : F → E) (y₀ : E) :
    Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔
    ∀ i ε, 0 < ε → ∃ x₀, ∀ x, x₀ ≤ x → p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds u y₀]
  -- ⊢ (∀ (i : ι) (ε : ℝ), 0 < ε → ∀ᶠ (x : F) in atTop, ↑(p i) (u x - y₀) < ε) ↔ ∀  …
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop
  -- 🎉 no goals
#align with_seminorms.tendsto_nhds_at_top WithSeminorms.tendsto_nhds_atTop

end Tendsto

section TopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [Nonempty ι]

section TopologicalSpace

variable [t : TopologicalSpace E]

theorem SeminormFamily.withSeminorms_of_nhds [TopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine'
    ⟨TopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup _⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  -- ⊢ 𝓝 0 = FilterBasis.filter AddGroupFilterBasis.toFilterBasis
  exact h
  -- 🎉 no goals
#align seminorm_family.with_seminorms_of_nhds SeminormFamily.withSeminorms_of_nhds

theorem SeminormFamily.withSeminorms_of_hasBasis [TopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id) : WithSeminorms p :=
  p.withSeminorms_of_nhds <|
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis
#align seminorm_family.with_seminorms_of_has_basis SeminormFamily.withSeminorms_of_hasBasis

theorem SeminormFamily.withSeminorms_iff_nhds_eq_iInf [TopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝 0).comap (p i) := by
  rw [← p.filter_eq_iInf]
  -- ⊢ WithSeminorms p ↔ 𝓝 0 = FilterBasis.filter AddGroupFilterBasis.toFilterBasis
  refine' ⟨fun h => _, p.withSeminorms_of_nhds⟩
  -- ⊢ 𝓝 0 = FilterBasis.filter AddGroupFilterBasis.toFilterBasis
  rw [h.topology_eq_withSeminorms]
  -- ⊢ 𝓝 0 = FilterBasis.filter AddGroupFilterBasis.toFilterBasis
  exact AddGroupFilterBasis.nhds_zero_eq _
  -- 🎉 no goals
#align seminorm_family.with_seminorms_iff_nhds_eq_infi SeminormFamily.withSeminorms_iff_nhds_eq_iInf

/-- The topology induced by a family of seminorms is exactly the infimum of the ones induced by
each seminorm individually. We express this as a characterization of `WithSeminorms p`. -/
theorem SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf [TopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    TopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance),
    nhds_iInf]
  congrm _ = ⨅ i, ?_
  -- ⊢ comap (↑(p i)) (𝓝 0) = 𝓝 0
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup
  -- 🎉 no goals
#align seminorm_family.with_seminorms_iff_topological_space_eq_infi SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf

theorem WithSeminorms.continuous_seminorm {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
    (i : ι) : Continuous (p i) := by
  have := hp.topologicalAddGroup
  -- ⊢ Continuous ↑(p i)
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  -- ⊢ Continuous ↑(p i)
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)
  -- 🎉 no goals
#align with_seminorms.continuous_seminorm WithSeminorms.continuous_seminorm

end TopologicalSpace

/-- The uniform structure induced by a family of seminorms is exactly the infimum of the ones
induced by each seminorm individually. We express this as a characterization of
`WithSeminorms p`. -/
theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
    [UniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    UniformAddGroup.ext_iff inferInstance (uniformAddGroup_iInf fun i => inferInstance),
    toTopologicalSpace_iInf, nhds_iInf]
  congrm _ = ⨅ i, ?_
  -- ⊢ comap (↑(p i)) (𝓝 0) = 𝓝 0
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup
  -- 🎉 no goals
#align seminorm_family.with_seminorms_iff_uniform_space_eq_infi SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf

end TopologicalAddGroup

section NormedSpace

/-- The topology of a `NormedSpace 𝕜 E` is induced by the seminorm `normSeminorm 𝕜 E`. -/
theorem norm_withSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E := by
  let p : SeminormFamily 𝕜 E (Fin 1) := fun _ => normSeminorm 𝕜 E
  -- ⊢ WithSeminorms fun x => normSeminorm 𝕜 E
  refine'
    ⟨SeminormedAddCommGroup.toTopologicalAddGroup.ext
        p.addGroupFilterBasis.isTopologicalAddGroup _⟩
  refine' Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball _
  -- ⊢ HasBasis (𝓝 0) (fun x => 0 < x) (Metric.ball 0)
  rw [← ball_normSeminorm 𝕜 E]
  -- ⊢ HasBasis (𝓝 0) (fun x => 0 < x) (ball (normSeminorm 𝕜 E) 0)
  refine'
    Filter.HasBasis.to_hasBasis p.addGroupFilterBasis.nhds_zero_hasBasis _ fun r hr =>
      ⟨(normSeminorm 𝕜 E).ball 0 r, p.basisSets_singleton_mem 0 hr, rfl.subset⟩
  rintro U (hU : U ∈ p.basisSets)
  -- ⊢ ∃ i', 0 < i' ∧ ball (normSeminorm 𝕜 E) 0 i' ⊆ id U
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∃ i', 0 < i' ∧ ball (normSeminorm 𝕜 E) 0 i' ⊆ id U
  use r, hr
  -- ⊢ ball (normSeminorm 𝕜 E) 0 r ⊆ id U
  rw [hU, id.def]
  -- ⊢ ball (normSeminorm 𝕜 E) 0 r ⊆ ball (Finset.sup s p) 0 r
  by_cases h : s.Nonempty
  -- ⊢ ball (normSeminorm 𝕜 E) 0 r ⊆ ball (Finset.sup s p) 0 r
  · rw [Finset.sup_const h]
    -- 🎉 no goals
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  -- ⊢ ball (normSeminorm 𝕜 E) 0 r ⊆ univ
  exact Set.subset_univ _
  -- 🎉 no goals
#align norm_with_seminorms norm_withSeminorms

end NormedSpace

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [TopologicalSpace E]

theorem WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p x < r := by
  rw [hp.hasBasis.isVonNBounded_basis_iff]
  -- ⊢ (∀ (i : Set E), i ∈ SeminormFamily.basisSets p → Absorbs 𝕜 (id i) s) ↔ ∀ (I  …
  constructor
  -- ⊢ (∀ (i : Set E), i ∈ SeminormFamily.basisSets p → Absorbs 𝕜 (id i) s) → ∀ (I  …
  · intro h I
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    simp only [id.def] at h
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    rcases h with ⟨r, hr, h⟩
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    cases' NormedField.exists_lt_norm 𝕜 r with a ha
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    specialize h a (le_of_lt ha)
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha), mul_one] at h
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    refine' ⟨‖a‖, lt_trans hr ha, _⟩
    -- ⊢ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < ‖a‖
    intro x hx
    -- ⊢ ↑(Finset.sup I p) x < ‖a‖
    specialize h hx
    -- ⊢ ↑(Finset.sup I p) x < ‖a‖
    exact (Finset.sup I p).mem_ball_zero.mp h
    -- 🎉 no goals
  intro h s' hs'
  -- ⊢ Absorbs 𝕜 (id s') s
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  -- ⊢ Absorbs 𝕜 (id s') s
  rw [id.def, hs']
  -- ⊢ Absorbs 𝕜 (ball (Finset.sup I p) 0 r) s
  rcases h I with ⟨r', _, h'⟩
  -- ⊢ Absorbs 𝕜 (ball (Finset.sup I p) 0 r) s
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  -- ⊢ Absorbs 𝕜 (ball (Finset.sup I p) 0 r) s
  refine' Absorbs.mono_right _ h'
  -- ⊢ Absorbs 𝕜 (ball (Finset.sup I p) 0 r) (ball (Finset.sup I p) 0 r')
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr
  -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align with_seminorms.is_vonN_bounded_iff_finset_seminorm_bounded WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded

theorem WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔
      ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.ball_image_iff]
  -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align with_seminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded

theorem WithSeminorms.isVonNBounded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i x < r := by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  -- ⊢ (∀ (I : Finset ι), ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r)  …
  constructor
  -- ⊢ (∀ (I : Finset ι), ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r)  …
  · intro hI i
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(p i) x < r
    convert hI {i}
    -- ⊢ p i = Finset.sup {i} p
    rw [Finset.sup_singleton]
    -- 🎉 no goals
  intro hi I
  -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
  by_cases hI : I.Nonempty
  -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
  · choose r hr h using hi
    -- ⊢ ∃ r, r > 0 ∧ ∀ (x : E), x ∈ s → ↑(Finset.sup I p) x < r
    have h' : 0 < I.sup' hI r := by
      rcases hI.bex with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine' ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => _⟩
    -- ⊢ ↑(p i) x < Finset.sup' I hI r
    refine' lt_of_lt_of_le (h i x hx) _
    -- ⊢ r i ≤ Finset.sup' I hI r
    simp only [Finset.le_sup'_iff, exists_prop]
    -- ⊢ ∃ b, b ∈ I ∧ r i ≤ r b
    exact ⟨i, hi, (Eq.refl _).le⟩
    -- 🎉 no goals
  simp only [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.sup_empty, coe_bot, Pi.zero_apply,
    exists_prop]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩
  -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align with_seminorms.is_vonN_bounded_iff_seminorm_bounded WithSeminorms.isVonNBounded_iff_seminorm_bounded

theorem WithSeminorms.image_isVonNBounded_iff_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.ball_image_iff]
  -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align with_seminorms.image_is_vonN_bounded_iff_seminorm_bounded WithSeminorms.image_isVonNBounded_iff_seminorm_bounded

end NontriviallyNormedField

-- TODO: the names in this section are not very predictable
section continuous_of_bounded

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕝] [Module 𝕝 E]

variable [NontriviallyNormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable [NormedField 𝕝₂] [Module 𝕝₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable {τ₁₂ : 𝕝 →+* 𝕝₂} [RingHomIsometric τ₁₂]

variable [Nonempty ι] [Nonempty ι']

theorem continuous_of_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [TopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i, Continuous ((q i).comp f)) : Continuous f := by
  have : TopologicalAddGroup F := hq.topologicalAddGroup
  -- ⊢ Continuous ↑f
  refine' continuous_of_continuousAt_zero f _
  -- ⊢ ContinuousAt (↑f) 0
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  -- ⊢ Tendsto (↑(q i) ∘ ↑f) (𝓝 0) (𝓝 0)
  convert (hf i).continuousAt.tendsto
  -- ⊢ 0 = ↑(comp (q i) f) 0
  exact (map_zero _).symm
  -- 🎉 no goals
#align seminorm.continuous_of_continuous_comp Seminorm.continuous_of_continuous_comp

theorem continuous_iff_continuous_comp {q : SeminormFamily 𝕜₂ F ι'} [TopologicalSpace E]
    [TopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    Continuous f ↔ ∀ i, Continuous ((q i).comp f) :=
    -- Porting note: if we *don't* use dot notation for `Continuous.comp`, Lean tries to show
    -- continuity of `((q i).comp f) ∘ id` because it doesn't see that `((q i).comp f)` is
    -- actually a composition of functions.
  ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩
#align seminorm.continuous_iff_continuous_comp Seminorm.continuous_iff_continuous_comp

theorem continuous_from_bounded {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
    {_ : TopologicalSpace E} (hp : WithSeminorms p) {_ : TopologicalSpace F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : Seminorm.IsBounded p q f) : Continuous f := by
  have : TopologicalAddGroup E := hp.topologicalAddGroup
  -- ⊢ Continuous ↑f
  refine continuous_of_continuous_comp hq _ fun i => ?_
  -- ⊢ Continuous ↑(comp (q i) f)
  rcases hf i with ⟨s, C, hC⟩
  -- ⊢ Continuous ↑(comp (q i) f)
  rw [← Seminorm.finset_sup_smul] at hC
  -- ⊢ Continuous ↑(comp (q i) f)
  -- Note: we deduce continuouty of `s.sup (C • p)` from that of `∑ i in s, C • p i`.
  -- The reason is that there is no `continuous_finset_sup`, and even if it were we couldn't
  -- really use it since `ℝ` is not an `OrderBot`.
  refine Seminorm.continuous_of_le ?_ (hC.trans <| Seminorm.finset_sup_le_sum _ _)
  -- ⊢ Continuous ↑(∑ i in s, (C • p) i)
  change Continuous (fun x ↦ Seminorm.coeFnAddMonoidHom _ _ (∑ i in s, C • p i) x)
  -- ⊢ Continuous fun x => ↑(coeFnAddMonoidHom 𝕝 E) (∑ i in s, C • p i) x
  simp_rw [map_sum, Finset.sum_apply]
  -- ⊢ Continuous fun x => ∑ c in s, ↑(coeFnAddMonoidHom 𝕝 E) (C • p c) x
  exact (continuous_finset_sum _ fun i _ ↦ (hp.continuous_seminorm i).const_smul (C : ℝ))
  -- 🎉 no goals
#align seminorm.continuous_from_bounded Seminorm.continuous_from_bounded

theorem cont_withSeminorms_normedSpace (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F]
    [TopologicalSpace E] {p : ι → Seminorm 𝕝 E} (hp : WithSeminorms p)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∃ (s : Finset ι) (C : ℝ≥0), (normSeminorm 𝕝₂ F).comp f ≤ C • s.sup p) :
    Continuous f := by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  -- ⊢ Continuous ↑f
  exact continuous_from_bounded hp (norm_withSeminorms 𝕝₂ F) f hf
  -- 🎉 no goals
#align seminorm.cont_with_seminorms_normed_space Seminorm.cont_withSeminorms_normedSpace

theorem cont_normedSpace_to_withSeminorms (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E]
    [TopologicalSpace F] {q : ι → Seminorm 𝕝₂ F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i : ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • normSeminorm 𝕝 E) :
    Continuous f := by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  -- ⊢ Continuous ↑f
  exact continuous_from_bounded (norm_withSeminorms 𝕝 E) hq f hf
  -- 🎉 no goals
#align seminorm.cont_normed_space_to_with_seminorms Seminorm.cont_normedSpace_to_withSeminorms

/-- Let `E` and `F` be two topological vector spaces over a `NontriviallyNormedField`, and assume
that the topology of `F` is generated by some family of seminorms `q`. For a family `f` of linear
maps from `E` to `F`, the following are equivalent:
* `f` is equicontinuous at `0`.
* `f` is equicontinuous.
* `f` is uniformly equicontinuous.
* For each `q i`, the family of seminorms `k ↦ (q i) ∘ (f k)` is bounded by some continuous
  seminorm `p` on `E`.
* For each `q i`, the seminorm `⊔ k, (q i) ∘ (f k)` is well-defined and continuous.

In particular, if you can determine all continuous seminorms on `E`, that gives you a complete
characterization of equicontinuity for linear maps from `E` to `F`. For example `E` and `F` are
both normed spaces, you get `NormedSpace.equicontinuous_TFAE`. -/
protected theorem _root_.WithSeminorms.equicontinuous_TFAE {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [hu : UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) : TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p,
      ∀ i, BddAbove (range fun k ↦ (q i).comp (f k)) ∧ Continuous (⨆ k, (q i).comp (f k)) ] := by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq, uniformEquicontinuous_iInf_rng,
      equicontinuous_iInf_rng, equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i ↦ ?_
  -- ⊢ TFAE (List.map (fun p => p i) [fun k => EquicontinuousAt (FunLike.coe ∘ f) 0 …
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  -- ⊢ TFAE (List.map (fun p => p i) [fun k => EquicontinuousAt (FunLike.coe ∘ f) 0 …
  clear u hu hq
  -- ⊢ TFAE (List.map (fun p => p i) [fun k => EquicontinuousAt (FunLike.coe ∘ f) 0 …
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  -- ⊢ TFAE [EquicontinuousAt (FunLike.coe ∘ f) 0, Equicontinuous (FunLike.coe ∘ f) …
  tfae_have 1 → 3
  -- ⊢ EquicontinuousAt (FunLike.coe ∘ f) 0 → UniformEquicontinuous (FunLike.coe ∘ f)
  · exact uniformEquicontinuous_of_equicontinuousAt_zero f
    -- 🎉 no goals
  tfae_have 3 → 2
  -- ⊢ UniformEquicontinuous (FunLike.coe ∘ f) → Equicontinuous (FunLike.coe ∘ f)
  · exact UniformEquicontinuous.equicontinuous
    -- 🎉 no goals
  tfae_have 2 → 1
  -- ⊢ Equicontinuous (FunLike.coe ∘ f) → EquicontinuousAt (FunLike.coe ∘ f) 0
  · exact fun H ↦ H 0
    -- 🎉 no goals
  tfae_have 3 → 5
  -- ⊢ UniformEquicontinuous (FunLike.coe ∘ f) → BddAbove (Set.range fun k => comp  …
  · intro H
    -- ⊢ BddAbove (Set.range fun k => comp (q i) (f k)) ∧ Continuous (⨆ (k : κ), ↑(co …
    have : ∀ᶠ x in 𝓝 0, ∀ k, q i (f k x) ≤ 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using (hx k).le
    have bdd : BddAbove (range fun k ↦ (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx ↦ ⟨1, forall_range_iff.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    -- ⊢ BddAbove (Set.range fun k => comp (q i) (f k)) ∧ Continuous ↑(⨆ (i_1 : κ), c …
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    -- ⊢ closedBall (⨆ (i_1 : κ), comp (q i) (f i_1)) 0 1 ∈ 𝓝 0
    filter_upwards [this] with x hx
    -- ⊢ x ∈ closedBall (⨆ (i_1 : κ), comp (q i) (f i_1)) 0 1
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using hx
    -- 🎉 no goals
  tfae_have 5 → 4
  -- ⊢ BddAbove (Set.range fun k => comp (q i) (f k)) ∧ Continuous (⨆ (k : κ), ↑(co …
  · exact fun H ↦ ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
    -- 🎉 no goals
  tfae_have 4 → 1 -- This would work over any `NormedField`
  -- ⊢ (∃ p, Continuous ↑p ∧ ∀ (k : κ), comp (q i) (f k) ≤ p) → EquicontinuousAt (F …
  · intro ⟨p, hp, hfp⟩
    -- ⊢ EquicontinuousAt (FunLike.coe ∘ f) 0
    exact Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _ <|
      eventually_of_forall fun x k ↦ by simpa using hfp k x
  tfae_finish
  -- 🎉 no goals

theorem _root_.WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [hu : UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔
    ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p :=
  (hq.equicontinuous_TFAE f).out 2 3

theorem _root_.WithSeminorms.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [hu : UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔ ∀ i,
    BddAbove (range fun k ↦ (q i).comp (f k)) ∧
      Continuous (⨆ k, (q i).comp (f k)) :=
  (hq.equicontinuous_TFAE f).out 2 4

end Seminorm

section Congr

namespace WithSeminorms

variable [Nonempty ι] [Nonempty ι']
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- Two families of seminorms `p` and `q` on the same space generate the same topology
if each `p i` is bounded by some `C • Finset.sup s q` and vice-versa.

We formulate these boundedness assumptions as `Seminorm.IsBounded q p LinearMap.id` (and
vice-versa) to reuse the API. Furthermore, we don't actually state it as an equality of topologies
but as a way to deduce `WithSeminorms q` from `WithSeminorms p`, since this should be more
useful in practice. -/
protected theorem congr {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
    [t : TopologicalSpace E] (hp : WithSeminorms p) (hpq : Seminorm.IsBounded p q LinearMap.id)
    (hqp : Seminorm.IsBounded q p LinearMap.id) : WithSeminorms q := by
  constructor
  -- ⊢ t = ModuleFilterBasis.topology (SeminormFamily.moduleFilterBasis q)
  rw [hp.topology_eq_withSeminorms]
  -- ⊢ ModuleFilterBasis.topology (SeminormFamily.moduleFilterBasis p) = ModuleFilt …
  clear hp t
  -- ⊢ ModuleFilterBasis.topology (SeminormFamily.moduleFilterBasis p) = ModuleFilt …
  refine le_antisymm ?_ ?_ <;>
  -- ⊢ ModuleFilterBasis.topology (SeminormFamily.moduleFilterBasis p) ≤ ModuleFilt …
  rw [← continuous_id_iff_le] <;>
  -- ⊢ Continuous id
  -- ⊢ Continuous id
  refine continuous_from_bounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)

protected theorem finset_sups {p : SeminormFamily 𝕜 E ι} [TopologicalSpace E]
    (hp : WithSeminorms p) : WithSeminorms (fun s : Finset ι ↦ s.sup p) := by
  refine hp.congr ?_ ?_
  -- ⊢ Seminorm.IsBounded p (fun s => Finset.sup s p) LinearMap.id
  · intro s
    -- ⊢ ∃ s_1 C, comp ((fun s => Finset.sup s p) s) LinearMap.id ≤ C • Finset.sup s_ …
    refine ⟨s, 1, ?_⟩
    -- ⊢ comp ((fun s => Finset.sup s p) s) LinearMap.id ≤ 1 • Finset.sup s p
    rw [one_smul]
    -- ⊢ comp ((fun s => Finset.sup s p) s) LinearMap.id ≤ Finset.sup s p
    rfl
    -- 🎉 no goals
  · intro i
    -- ⊢ ∃ s C, comp (p i) LinearMap.id ≤ C • Finset.sup s fun s => Finset.sup s p
    refine ⟨{{i}}, 1, ?_⟩
    -- ⊢ comp (p i) LinearMap.id ≤ 1 • Finset.sup {{i}} fun s => Finset.sup s p
    rw [Finset.sup_singleton, Finset.sup_singleton, one_smul]
    -- ⊢ comp (p i) LinearMap.id ≤ p i
    rfl
    -- 🎉 no goals

protected theorem partial_sups [Preorder ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
    [TopologicalSpace E] (hp : WithSeminorms p) : WithSeminorms (fun i ↦ (Finset.Iic i).sup p) := by
  refine hp.congr ?_ ?_
  -- ⊢ Seminorm.IsBounded p (fun i => Finset.sup (Finset.Iic i) p) LinearMap.id
  · intro i
    -- ⊢ ∃ s C, comp ((fun i => Finset.sup (Finset.Iic i) p) i) LinearMap.id ≤ C • Fi …
    refine ⟨Finset.Iic i, 1, ?_⟩
    -- ⊢ comp ((fun i => Finset.sup (Finset.Iic i) p) i) LinearMap.id ≤ 1 • Finset.su …
    rw [one_smul]
    -- ⊢ comp ((fun i => Finset.sup (Finset.Iic i) p) i) LinearMap.id ≤ Finset.sup (F …
    rfl
    -- 🎉 no goals
  · intro i
    -- ⊢ ∃ s C, comp (p i) LinearMap.id ≤ C • Finset.sup s fun i => Finset.sup (Finse …
    refine ⟨{i}, 1, ?_⟩
    -- ⊢ comp (p i) LinearMap.id ≤ 1 • Finset.sup {i} fun i => Finset.sup (Finset.Iic …
    rw [Finset.sup_singleton, one_smul]
    -- ⊢ comp (p i) LinearMap.id ≤ Finset.sup (Finset.Iic i) p
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i ≤ (Finset.Iic i).sup p)
    -- 🎉 no goals

protected theorem congr_equiv {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) (e : ι' ≃ ι) : WithSeminorms (p ∘ e) := by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp
  -- 🎉 no goals
  -- 🎉 no goals

end WithSeminorms

end Congr

end continuous_of_bounded

section bounded_of_continuous

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : SeminormFamily 𝕜 E ι}

/-- In a semi-`NormedSpace`, a continuous seminorm is zero on elements of norm `0`. -/
lemma map_eq_zero_of_norm_zero (q : Seminorm 𝕜 F)
    (hq : Continuous q) {x : F} (hx : ‖x‖ = 0) : q x = 0 :=
  (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr $ mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

/-- Let `F` be a semi-`NormedSpace` over a `NontriviallyNormedField`, and let `q` be a
seminorm on `F`. If `q` is continuous, then it is uniformly controlled by the norm, that is there
is some `C > 0` such that `∀ x, q x ≤ C * ‖x‖`.
The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε[`, thus with a
controlled image by `q`. The control of `q` at the original element follows by rescaling. -/
lemma bound_of_continuous_normedSpace (q : Seminorm 𝕜 F)
    (hq : Continuous q) : ∃ C, 0 < C ∧ (∀ x : F, q x ≤ C * ‖x‖) := by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  -- ⊢ ∃ C, 0 < C ∧ ∀ (x : F), ↑q x ≤ C * ‖x‖
  rcases NormedAddCommGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' $ Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  -- ⊢ ∃ C, 0 < C ∧ ∀ (x : F), ↑q x ≤ C * ‖x‖
  have : 0 < ‖c‖ / ε := by positivity
  -- ⊢ ∃ C, 0 < C ∧ ∀ (x : F), ↑q x ≤ C * ‖x‖
  refine ⟨‖c‖ / ε, this, fun x ↦ ?_⟩
  -- ⊢ ↑q x ≤ ‖c‖ / ε * ‖x‖
  by_cases hx : ‖x‖ = 0
  -- ⊢ ↑q x ≤ ‖c‖ / ε * ‖x‖
  · rw [hx, mul_zero]
    -- ⊢ ↑q x ≤ 0
    exact le_of_eq (map_eq_zero_of_norm_zero q hq hx)
    -- 🎉 no goals
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt ↦ ?_) hx
    -- ⊢ ↑q x ≤ ‖c‖ / ε * ↑(normSeminorm 𝕜 F) x
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    -- ⊢ 1 ≤ ‖c‖ / ε * ↑(normSeminorm 𝕜 F) x
    rwa [← div_le_iff' this, one_div_div]
    -- 🎉 no goals

/-- Let `E` be a topological vector space (over a `NontriviallyNormedField`) whose topology is
generated by some family of seminorms `p`, and let `q` be a seminorm on `E`. If `q` is continuous,
then it is uniformly controlled by *finitely many* seminorms of `p`, that is there
is some finset `s` of the index set and some `C > 0` such that `q ≤ C • s.sup p`. -/
lemma bound_of_continuous [Nonempty ι] [t : TopologicalSpace E] (hp : WithSeminorms p)
    (q : Seminorm 𝕜 E) (hq : Continuous q) :
    ∃ s : Finset ι, ∃ C : ℝ≥0, C ≠ 0 ∧ q ≤ C • s.sup p := by
  -- The continuity of `q` gives us a finset `s` and a real `ε > 0`
  -- such that `hε : (s.sup p).ball 0 ε ⊆ q.ball 0 1`.
  rcases hp.hasBasis.mem_iff.mp (ball_mem_nhds hq one_pos) with ⟨V, hV, hε⟩
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  rcases p.basisSets_iff.mp hV with ⟨s, ε, ε_pos, rfl⟩
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  -- Now forget that `E` already had a topology and view it as the (semi)normed space
  -- `(E, s.sup p)`.
  clear hp hq t
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  let _ : SeminormedAddCommGroup E := (s.sup p).toSeminormedAddCommGroup
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  let _ : NormedSpace 𝕜 E := { norm_smul_le := fun a b ↦ le_of_eq (map_smul_eq_mul (s.sup p) a b) }
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  -- The inclusion `hε` tells us exactly that `q` is *still* continuous for this new topology
  have : Continuous q :=
    Seminorm.continuous (r := 1) (mem_of_superset (Metric.ball_mem_nhds _ ε_pos) hε)
  -- Hence we can conclude by applying `bound_of_continuous_normed_space`.
  rcases bound_of_continuous_normedSpace q this with ⟨C, C_pos, hC⟩
  -- ⊢ ∃ s C, C ≠ 0 ∧ q ≤ C • Finset.sup s p
  exact ⟨s, ⟨C, C_pos.le⟩, fun H ↦ C_pos.ne.symm (congr_arg NNReal.toReal H), hC⟩
  -- 🎉 no goals
  -- Note that the key ingredient for this proof is that, by scaling arguments hidden in
  -- `seminorm.continuous`, we only have to look at the `q`-ball of radius one, and the `s` we get
  -- from that will automatically work for all other radii.

end Seminorm

end bounded_of_continuous

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty ι] [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

theorem WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    LocallyConvexSpace ℝ E := by
  have := hp.topologicalAddGroup
  -- ⊢ LocallyConvexSpace ℝ E
  apply ofBasisZero ℝ E id fun s => s ∈ p.basisSets
  -- ⊢ HasBasis (𝓝 0) (fun s => s ∈ SeminormFamily.basisSets p) id
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    -- ⊢ HasBasis (FilterBasis.filter AddGroupFilterBasis.toFilterBasis) (fun s => s  …
    exact FilterBasis.hasBasis _
    -- 🎉 no goals
  · intro s hs
    -- ⊢ Convex ℝ (id s)
    change s ∈ Set.iUnion _ at hs
    -- ⊢ Convex ℝ (id s)
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    -- ⊢ Convex ℝ (id s)
    rcases hs with ⟨I, r, _, rfl⟩
    -- ⊢ Convex ℝ (id (ball (Finset.sup I p) 0 r))
    exact convex_ball _ _ _
    -- 🎉 no goals
#align with_seminorms.to_locally_convex_space WithSeminorms.toLocallyConvexSpace

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SeminormedAddCommGroup E]

/-- Not an instance since `𝕜` can't be inferred. See `NormedSpace.toLocallyConvexSpace` for a
slightly weaker instance version. -/
theorem NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  (norm_withSeminorms 𝕜 E).toLocallyConvexSpace
#align normed_space.to_locally_convex_space' NormedSpace.toLocallyConvexSpace'

/-- See `NormedSpace.toLocallyConvexSpace'` for a slightly stronger version which is not an
instance. -/
instance NormedSpace.toLocallyConvexSpace [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.toLocallyConvexSpace' ℝ
#align normed_space.to_locally_convex_space NormedSpace.toLocallyConvexSpace

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f
#align seminorm_family.comp SeminormFamily.comp

theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl
#align seminorm_family.comp_apply SeminormFamily.comp_apply

theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  -- ⊢ ↑(Seminorm.comp (Finset.sup s q) f) x = ↑(Finset.sup s (comp q f)) x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  -- ⊢ ↑(Finset.sup s fun i => { val := ↑(q i) (↑f x), property := (_ : 0 ≤ ↑(q i)  …
  rfl
  -- 🎉 no goals
#align seminorm_family.finset_sup_comp SeminormFamily.finset_sup_comp

variable [TopologicalSpace F]

theorem LinearMap.withSeminorms_induced [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    WithSeminorms (topology := induced f inferInstance) (q.comp f) := by
  have := hq.topologicalAddGroup
  -- ⊢ WithSeminorms (SeminormFamily.comp q f)
  let _ : TopologicalSpace E := induced f inferInstance
  -- ⊢ WithSeminorms (SeminormFamily.comp q f)
  have : TopologicalAddGroup E := topologicalAddGroup_induced f
  -- ⊢ WithSeminorms (SeminormFamily.comp q f)
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf, nhds_induced, map_zero,
    q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.comap_iInf]
  refine' iInf_congr fun i => _
  -- ⊢ comap (↑f) (comap (↑(q i)) (𝓝 0)) = comap (↑(SeminormFamily.comp q f i)) (𝓝 0)
  exact Filter.comap_comap
  -- 🎉 no goals
#align linear_map.with_seminorms_induced LinearMap.withSeminorms_induced

theorem Inducing.withSeminorms [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q)
    [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : Inducing f) : WithSeminorms (q.comp f) := by
  rw [hf.induced]
  -- ⊢ WithSeminorms (SeminormFamily.comp q f)
  exact f.withSeminorms_induced hq
  -- 🎉 no goals
#align inducing.with_seminorms Inducing.withSeminorms

/-- (Disjoint) union of seminorm families. -/
protected def SeminormFamily.sigma {κ : ι → Type*} (p : (i : ι) → SeminormFamily 𝕜 E (κ i)) :
    SeminormFamily 𝕜 E ((i : ι) × κ i) :=
  fun ⟨i, k⟩ => p i k

theorem withSeminorms_iInf {κ : ι → Type*} [Nonempty ((i : ι) × κ i)] [∀ i, Nonempty (κ i)]
    {p : (i : ι) → SeminormFamily 𝕜 E (κ i)} {t : ι → TopologicalSpace E}
    [∀ i, @TopologicalAddGroup E (t i) _] (hp : ∀ i, WithSeminorms (topology := t i) (p i)) :
    WithSeminorms (topology := ⨅ i, t i) (SeminormFamily.sigma p) := by
  have : @TopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf (fun i ↦ inferInstance)
  -- ⊢ WithSeminorms (SeminormFamily.sigma p)
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  -- ⊢ ⨅ (i : ι), t i = ⨅ (i : (i : ι) × κ i), UniformSpace.toTopologicalSpace
  rw [iInf_sigma]
  -- ⊢ ⨅ (i : ι), t i = ⨅ (i : ι) (j : κ i), UniformSpace.toTopologicalSpace
  exact iInf_congr hp
  -- 🎉 no goals

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [Countable ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [TopologicalSpace E]

/-- If the topology of a space is induced by a countable family of seminorms, then the topology
is first countable. -/
theorem WithSeminorms.first_countable (hp : WithSeminorms p) :
    TopologicalSpace.FirstCountableTopology E := by
  have := hp.topologicalAddGroup
  -- ⊢ FirstCountableTopology E
  let _ : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  -- ⊢ FirstCountableTopology E
  have : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  -- ⊢ FirstCountableTopology E
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := UniformAddGroup.uniformity_countably_generated
  -- ⊢ FirstCountableTopology E
  exact UniformSpace.firstCountableTopology E
  -- 🎉 no goals
#align with_seminorms.first_countable WithSeminorms.first_countable

end TopologicalProperties
