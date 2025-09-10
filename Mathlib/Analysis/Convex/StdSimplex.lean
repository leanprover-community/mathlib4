/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.UnitInterval

/-!
# The standard simplex

In this file, given an ordered semiring `𝕜` and a finite type `ι`,
we define `stdSimplex : Set (ι → 𝕜)` as the set of vectors with non-negative
coordinates with total sum `1`.

-/

open Set Convex Bornology

section OrderedSemiring

variable (𝕜) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def stdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

theorem stdSimplex_eq_inter : stdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | ∑ x, f x = 1 } := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]

theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

@[nontriviality] lemma stdSimplex_of_subsingleton [Subsingleton 𝕜] : stdSimplex 𝕜 ι = univ :=
  eq_univ_of_forall fun _ ↦ ⟨fun _ ↦ (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩

/-- The standard simplex in the zero-dimensional space is empty. -/
lemma stdSimplex_of_isEmpty_index [IsEmpty ι] [Nontrivial 𝕜] : stdSimplex 𝕜 ι = ∅ :=
  eq_empty_of_forall_notMem <| by rintro f ⟨-, hf⟩; simp at hf

lemma stdSimplex_unique [ZeroLEOneClass 𝕜] [Nonempty ι] [Subsingleton ι] :
    stdSimplex 𝕜 ι = {fun _ ↦ 1} := by
  cases nonempty_unique ι
  refine eq_singleton_iff_unique_mem.2 ⟨⟨fun _ ↦ zero_le_one, Fintype.sum_unique _⟩, ?_⟩
  rintro f ⟨-, hf⟩
  rw [Fintype.sum_unique] at hf
  exact funext (Unique.forall_iff.2 hf)

variable {ι}

variable {𝕜} in
/-- All values of a function `f ∈ stdSimplex 𝕜 ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜]
    {f : ι → 𝕜} (hf : f ∈ stdSimplex 𝕜 ι) (x) :
    f x ∈ Icc (0 : 𝕜) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

variable [DecidableEq ι] [ZeroLEOneClass 𝕜]

theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

theorem ite_eq_mem_stdSimplex (i : ι) : (if i = · then (1 : 𝕜) else 0) ∈ stdSimplex 𝕜 ι := by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i

variable [IsOrderedRing 𝕜]

#adaptation_note /-- nightly-2024-03-11
we need a type annotation on the segment in the following two lemmas. -/

/-- The edges are contained in the simplex. -/
lemma segment_single_subset_stdSimplex (i j : ι) :
    ([Pi.single i 1 -[𝕜] Pi.single j 1] : Set (ι → 𝕜)) ⊆ stdSimplex 𝕜 ι :=
  (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

lemma stdSimplex_fin_two :
    stdSimplex 𝕜 (Fin 2) = ([Pi.single 0 1 -[𝕜] Pi.single 1 1] : Set (Fin 2 → 𝕜)) := by
  refine Subset.antisymm ?_ (segment_single_subset_stdSimplex 𝕜 (0 : Fin 2) 1)
  rintro f ⟨hf₀, hf₁⟩
  rw [Fin.sum_univ_two] at hf₁
  refine ⟨f 0, f 1, hf₀ 0, hf₀ 1, hf₁, funext <| Fin.forall_fin_two.2 ?_⟩
  simp

end OrderedSemiring

section OrderedRing

variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

/-- The standard one-dimensional simplex in `Fin 2 → 𝕜` is equivalent to the unit interval.
This bijection sends the zeroth vertex `Pi.single 0 1` to `0` and
the first vertex `Pi.single 1 1` to `1`. -/
@[simps -fullyApplied]
def stdSimplexEquivIcc : stdSimplex 𝕜 (Fin 2) ≃ Icc (0 : 𝕜) 1 where
  toFun f := ⟨f.1 1, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ ↦ f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.2.2, x.2.1⟩, by simp⟩
  left_inv f := Subtype.eq <| funext <| Fin.forall_fin_two.2 <| by
    simp [← (show f.1 0 + f.1 1 = 1 by simpa using f.2.2)]

@[simp]
lemma stdSimplexEquivIcc_zero :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 0⟩ = 0 := rfl

@[simp]
lemma stdSimplexEquivIcc_one :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 1⟩ = 1 := rfl

end OrderedRing

section Field

variable (R : Type*) (ι : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]

/-- `stdSimplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
theorem convexHull_basis_eq_stdSimplex [DecidableEq ι] :
    convexHull R (range fun i j : ι => if i = j then (1 : R) else 0) = stdSimplex R ι := by
  refine Subset.antisymm (convexHull_min ?_ (convex_stdSimplex R ι)) ?_
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_stdSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w]
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i) (hw₁.symm ▸ zero_lt_one)
      fun i _ => mem_range_self i

/-- `stdSimplex 𝕜 ι` is the convex hull of the points `Pi.single i 1` for `i : `i`. -/
theorem convexHull_rangle_single_eq_stdSimplex [DecidableEq ι] :
    convexHull R (range fun i : ι ↦ Pi.single i 1) = stdSimplex R ι := by
  convert convexHull_basis_eq_stdSimplex R ι
  aesop

variable {ι R}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x ∈ s, w x • x`.

Since we have no sums over finite sets, we use sum over `@Finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem Set.Finite.convexHull_eq_image {E : Type*} [AddCommGroup E] [Module R E]
    {s : Set E} (hs : s.Finite) : convexHull R s =
    haveI := hs.fintype
    (⇑(∑ x : s, (LinearMap.proj (R := R) x).smulRight x.1)) '' stdSimplex R s := by
  classical
  letI := hs.fintype
  rw [← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  apply congr_arg
  aesop

end Field

section Topology

variable {ι : Type*} [Fintype ι]

/-- Every vector in `stdSimplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem stdSimplex_subset_closedBall : stdSimplex ℝ ι ⊆ Metric.closedBall 0 1 := fun f hf ↦ by
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply, Real.dist_0_eq_abs, abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

variable (ι)

/-- `stdSimplex ℝ ι` is bounded. -/
theorem bounded_stdSimplex : IsBounded (stdSimplex ℝ ι) :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

/-- `stdSimplex ℝ ι` is closed. -/
theorem isClosed_stdSimplex : IsClosed (stdSimplex ℝ ι) :=
  (stdSimplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
      (isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const)

/-- `stdSimplex ℝ ι` is compact. -/
theorem isCompact_stdSimplex : IsCompact (stdSimplex ℝ ι) :=
  Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_stdSimplex ι, bounded_stdSimplex ι⟩

instance stdSimplex.instCompactSpace_coe : CompactSpace ↥(stdSimplex ℝ ι) :=
  isCompact_iff_compactSpace.mp <| isCompact_stdSimplex _

/-- The standard one-dimensional simplex in `ℝ² = Fin 2 → ℝ`
is homeomorphic to the unit interval. -/
@[simps! -fullyApplied]
def stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := stdSimplexEquivIcc ℝ
  continuous_toFun := .subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_const.sub continuous_subtype_val, continuous_subtype_val⟩)

@[simp]
lemma stdSimplexHomeomorphUnitInterval_zero :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 0⟩ = 0 := rfl

@[simp]
lemma stdSimplexHomeomorphUnitInterval_one :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 1⟩ = 1 := rfl

end Topology
