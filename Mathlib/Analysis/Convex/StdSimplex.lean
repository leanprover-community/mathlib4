/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies, Joël Riou
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# The standard simplex

In this file, given an ordered semiring `𝕜` and a finite type `ι`,
we define `stdSimplex : Set (ι → 𝕜)` as the set of vectors with non-negative
coordinates with total sum `1`.

When `f : X → Y` is a map between finite types, we define the map
`stdSimplex.map f : stdSimplex 𝕜 X → stdSimplex 𝕜 Y`.

-/

@[expose] public section

open Set Convex Bornology Convexity

section OrderedSemiring

variable (𝕜) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
@[deprecated StdSimplex (since := "2026-08-29")]
def stdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

@[deprecated StdSimplex.range_toFun_comp_weights (since := "2026-08-29")]
theorem stdSimplex_eq_inter : stdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | ∑ x, f x = 1 } := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

@[deprecated StdSimplex.instConvexSpace (since := "2026-08-29")]
theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

@[nontriviality, deprecated "no replacement" (since := "2026-08-29")]
lemma stdSimplex_of_subsingleton [Subsingleton 𝕜] : stdSimplex 𝕜 ι = univ :=
  eq_univ_of_forall fun _ ↦ ⟨fun _ ↦ (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩

/-- The standard simplex in the zero-dimensional space is empty. -/
@[deprecated "no replacement" (since := "2026-08-29")]
lemma stdSimplex_of_isEmpty_index [IsEmpty ι] [Nontrivial 𝕜] : stdSimplex 𝕜 ι = ∅ :=
  eq_empty_of_forall_notMem <| by rintro f ⟨-, hf⟩; simp at hf

@[deprecated StdSimplex.instUnique (since := "2026-08-29")]
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
@[deprecated "no replacement" (since := "2026-08-29")]
theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜]
    {f : ι → 𝕜} (hf : f ∈ stdSimplex 𝕜 ι) (x) :
    f x ∈ Icc (0 : 𝕜) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

/-- `stdSimplex 𝕜 ι` is a subset of the unit cube -/
@[deprecated "no replacement" (since := "2026-08-29")]
theorem stdSimplex_subset_Icc [IsOrderedAddMonoid 𝕜] : stdSimplex 𝕜 ι ⊆ Icc 0 1 := by
  intro f h
  rw [← pi_univ_Icc, univ_pi_eq_iInter, mem_iInter]
  simpa using fun i ↦ mem_Icc_of_mem_stdSimplex h i

variable [DecidableEq ι] [ZeroLEOneClass 𝕜]

@[deprecated StdSimplex.single (since := "2026-08-29")]
theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

@[deprecated "no replacement" (since := "2026-08-29")]
theorem ite_eq_mem_stdSimplex (i : ι) : (if i = · then (1 : 𝕜) else 0) ∈ stdSimplex 𝕜 ι := by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i

variable [IsOrderedRing 𝕜]

set_option linter.overlappingInstances false
/-- The edges are contained in the simplex. -/
@[deprecated "no replacement" (since := "2026-08-29")]
lemma segment_single_subset_stdSimplex (i j : ι) :
    [Pi.single i 1 -[𝕜] Pi.single j 1] ⊆ stdSimplex 𝕜 ι :=
  (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

@[deprecated "no replacement" (since := "2026-08-29")]
lemma stdSimplex_fin_two :
    stdSimplex 𝕜 (Fin 2) = [Pi.single 0 1 -[𝕜] Pi.single 1 1] := by
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
@[simps -fullyApplied, deprecated StdSimplex.equivIcc (since := "2026-08-29")]
def stdSimplexEquivIcc : stdSimplex 𝕜 (Fin 2) ≃ Icc (0 : 𝕜) 1 where
  toFun f := ⟨f.1 1, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ ↦ f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.2.2, x.2.1⟩, by simp⟩
  left_inv f := Subtype.ext <| funext <| Fin.forall_fin_two.2 <| by
    simp [← (show f.1 0 + f.1 1 = 1 by simpa using f.2.2)]

@[simp, deprecated StdSimplex.equivIcc_single_zero (since := "2026-08-29")]
lemma stdSimplexEquivIcc_zero :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 0⟩ = 0 := rfl

@[simp, deprecated StdSimplex.equivIcc_single_one (since := "2026-08-29")]
lemma stdSimplexEquivIcc_one :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 1⟩ = 1 := rfl

end OrderedRing

section Field

variable (R : Type*) (ι : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]

/-- `stdSimplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
@[deprecated "no replacement" (since := "2026-08-29")]
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

/-- `stdSimplex 𝕜 ι` is the convex hull of the points `Pi.single i 1` for `i : ι`. -/
@[deprecated "no replacement" (since := "2026-08-29")]
theorem convexHull_rangle_single_eq_stdSimplex [DecidableEq ι] :
    convexHull R (range fun i : ι ↦ Pi.single i 1) = stdSimplex R ι := by
  convert! convexHull_basis_eq_stdSimplex R ι
  aesop

variable {ι R}

lemma Convexity.ConvexSpace.AffineMap.convex_range {X : Type*}
    [ConvexSpace R X] {E : Type*} [AddCommGroup E] [Module R E]
    [ConvexSpace R E] [IsModuleConvexSpace R E] (f : ConvexSpace.AffineMap R X E) :
    Convex R (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb h
  exact ⟨convexCombPair a b ha hb h x y, by simp [f.isAffineMap.map_convexCombPair]⟩

/-- The convex hull of a set `s` is the range of the affine map
`StdSimplex R s → E` which sends `x : s` to `x : E`. -/
theorem Set.convexHull_eq_range_iConvexComb
    {E : Type*} [AddCommGroup E] [Module R E]
    [ConvexSpace R E] [IsModuleConvexSpace R E] (s : Set E) :
    convexHull R s =
      Set.range (StdSimplex.affineMapMk (R := R) (fun (x : s) ↦ x.val)) := by
  refine subset_antisymm ?_ ?_
  · rw [Convex.convexHull_subset_iff (ConvexSpace.AffineMap.convex_range _)]
    intro x hx
    exact ⟨.single ⟨x, hx⟩, by simp⟩
  · rintro _ ⟨w, rfl⟩
    rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum, Finsupp.sum]
    convert affineCombination_mem_convexHull (s := w.weights.support) (v := fun x ↦ x.val)
      (w := w.weights) (by simp) w.total
    · aesop
    · rw [Finset.affineCombination_eq_linear_combination]
      exact w.total

@[deprecated (since := "2026-08-29")] alias Set.Finite.convexHull_eq_image :=
  Set.convexHull_eq_range_iConvexComb

end Field

section GeneralTopology
variable (𝕜 ι : Type*) [Fintype ι]
  [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜]

/-- `stdSimplex 𝕜 ι` is closed. -/
@[deprecated StdSimplex.isClosedEmbedding_toFun_comp_weights (since := "2026-08-29")]
theorem isClosed_stdSimplex : IsClosed (stdSimplex 𝕜 ι) := by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · apply isClosed_iInter
    exact fun i ↦ isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

/-- `stdSimplex 𝕜 ι` is compact. -/
@[deprecated StdSimplex.compactSpace (since := "2026-08-29")]
theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    IsCompact (stdSimplex 𝕜 ι) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

@[deprecated StdSimplex.compactSpace (since := "2026-08-29")]
instance stdSimplex.instCompactSpace_coe [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    CompactSpace (stdSimplex 𝕜 ι) :=
  isCompact_iff_compactSpace.mp <| isCompact_stdSimplex 𝕜 _

end GeneralTopology

section Topology

variable {ι : Type*} [Fintype ι]

/-- Every vector in `stdSimplex 𝕜 ι` has `max`-norm at most `1`. -/
@[deprecated StdSimplex.range_toFun_comp_weights_subset_closedBall (since := "2026-08-29")]
theorem stdSimplex_subset_closedBall : stdSimplex ℝ ι ⊆ Metric.closedBall 0 1 := fun f hf ↦ by
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply, Real.dist_0_eq_abs, abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

variable (ι)

/-- `stdSimplex ℝ ι` is bounded. -/
@[deprecated StdSimplex.isBounded_range_toFun_comp_weights (since := "2026-08-29")]
theorem bounded_stdSimplex : IsBounded (stdSimplex ℝ ι) :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

/-- `stdSimplex ℝ ι` is path connected. -/
@[deprecated StdSimplex.pathConnectedSpace (since := "2026-08-29")]
theorem isPathConnected_stdSimplex [Nonempty ι] :
    IsPathConnected (stdSimplex ℝ ι) :=
  (convex_stdSimplex ℝ ι).isPathConnected (by
    classical
    exact ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩)

@[deprecated StdSimplex.pathConnectedSpace (since := "2026-08-29")]
instance [Nonempty ι] : PathConnectedSpace (stdSimplex ℝ ι) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_stdSimplex _)

/-- The standard one-dimensional simplex in `ℝ² = Fin 2 → ℝ`
is homeomorphic to the unit interval. -/
@[simps! -fullyApplied, deprecated StdSimplex.homeomorphI (since := "2026-08-29")]
def stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := stdSimplexEquivIcc ℝ
  continuous_toFun := .subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_const.sub continuous_subtype_val, continuous_subtype_val⟩)

@[simp, deprecated StdSimplex.homeomorphI_single_zero (since := "2026-08-29")]
lemma stdSimplexHomeomorphUnitInterval_zero :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 0⟩ = 0 := rfl

@[simp, deprecated StdSimplex.homeomorphI_single_one (since := "2026-08-29")]
lemma stdSimplexHomeomorphUnitInterval_one :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 1⟩ = 1 := rfl

/-! ### Diameter of a Standard Simplex (sup metric) -/

variable {ι}

/-- The (sup metric) diameter of a standard simplex is less than or equal to 1. -/
@[deprecated StdSimplex.diam_range_toFun_comp_weights_subset_closedBall (since := "2026-08-29")]
theorem diam_stdSimplex_le : Metric.diam (stdSimplex ℝ ι) ≤ 1 :=
  Metric.diam_le_of_forall_dist_le zero_le_one fun x hx y hy ↦
    (dist_pi_le_iff zero_le_one).2 fun i ↦ by
      have hx := mem_Icc_of_mem_stdSimplex hx i
      have hy := mem_Icc_of_mem_stdSimplex hy i
      grind [Real.dist_eq]

/-- The (sup metric) diameter of a standard simplex indexed by a subsingleton is 0. -/
@[simp, deprecated StdSimplex.diam_range_toFun_comp_weights_subset_closedBall_eq_zero
  (since := "2026-08-29")]
theorem diam_stdSimplex_of_subsingleton [Subsingleton ι] : Metric.diam (stdSimplex ℝ ι) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl h => rw [stdSimplex_of_isEmpty_index, Metric.diam_empty]
  | inr h => rw [stdSimplex_unique, Metric.diam_singleton]

/-- The (sup metric) diameter of a standard simplex indexed by a nontrivial index is 1. -/
@[simp, deprecated StdSimplex.diam_range_toFun_comp_weights_subset_closedBall_eq_one
  (since := "2026-08-29")]
theorem diam_stdSimplex [Nontrivial ι] : Metric.diam (stdSimplex ℝ ι) = 1 := by
  refine le_antisymm diam_stdSimplex_le ?_
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  classical
  rw [show (1 : ℝ) = dist (Pi.single i 1 : ι → ℝ) (Pi.single j 1) by
    simp [dist_single_single i j (1 : ℝ) 1 hij, Real.dist_eq]]
  exact Metric.dist_le_diam_of_mem (bounded_stdSimplex _)
    (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

end Topology

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

@[deprecated "no replacement" (since := "2026-08-29")]
instance : FunLike (stdSimplex S X) X S where
  coe s := s.val
  coe_injective := by aesop

@[ext high, deprecated StdSimplex.ext (since := "2026-08-29")]
lemma ext {s t : stdSimplex S X} (h : (s : X → S) = t) : s = t := by
  ext : 1
  assumption

@[simp, deprecated StdSimplex.weights_nonneg (since := "2026-08-29")]
lemma zero_le (s : stdSimplex S X) (x : X) : 0 ≤ s x := s.2.1 x

@[simp, deprecated StdSimplex.total (since := "2026-08-29")]
lemma sum_eq_one (s : stdSimplex S X) : ∑ x, s x = 1 := s.2.2

@[simp, deprecated StdSimplex.total_fin_two (since := "2026-08-29")]
lemma add_eq_one (s : stdSimplex S (Fin 2)) :
    s 0 + s 1 = 1 := by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

section

variable [IsOrderedRing S]

@[simp, deprecated StdSimplex.weights_apply_le_one (since := "2026-08-29")]
lemma le_one (s : stdSimplex S X) (x : X) : s x ≤ 1 := by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

@[deprecated StdSimplex.map (since := "2026-08-29")]
lemma image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap S S f) (stdSimplex S X) ⊆ stdSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y ↦ ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/-- The map `stdSimplex S X → stdSimplex S Y` that is induced by a map `f : X → Y`. -/
@[deprecated StdSimplex.map (since := "2026-08-29")]
noncomputable def map (f : X → Y) (s : stdSimplex S X) : stdSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp, deprecated "no replacement" (since := "2026-08-29")]
lemma map_coe (f : X → Y) (s : stdSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

@[simp, deprecated StdSimplex.map_id (since := "2026-08-29")]
lemma map_id_apply (x : stdSimplex S X) : map id x = x := by
  aesop

@[deprecated StdSimplex.map_comp (since := "2026-08-29")]
lemma map_comp_apply (f : X → Y) (g : Y → Z) (x : stdSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

/-- The vertex corresponding to `x : X` in `stdSimplex S X`. -/
@[deprecated StdSimplex.single (since := "2026-08-29")]
abbrev vertex [DecidableEq X] (x : X) : stdSimplex S X :=
  ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp, deprecated "no replacement" (since := "2026-08-29")]
lemma vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

@[simp, deprecated StdSimplex.map_single (since := "2026-08-29")]
lemma map_vertex [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  aesop

@[deprecated StdSimplex.continuous_map (since := "2026-08-29")]
lemma continuous_map [TopologicalSpace S] [IsTopologicalSemiring S] (f : X → Y) :
    Continuous (map (S := S) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

@[deprecated StdSimplex.single_injective (since := "2026-08-29")]
lemma vertex_injective [Nontrivial S] [DecidableEq X] :
    Function.Injective (vertex (S := S) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

@[deprecated StdSimplex.instNonempty (since := "2026-08-29")]
instance [Nonempty X] : Nonempty (stdSimplex S X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

@[deprecated StdSimplex.instNontrivial (since := "2026-08-29")]
instance [Nontrivial S] [Nontrivial X] : Nontrivial (stdSimplex S X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h ↦ hxy (vertex_injective h)⟩

@[deprecated StdSimplex.instSubsingleton (since := "2026-08-29")]
instance [Subsingleton X] : Subsingleton (stdSimplex S X) where
  allEq s t := by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u, Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

@[deprecated StdSimplex.instUnique (since := "2026-08-29")]
instance [Unique X] : Unique (stdSimplex S X) where
  default := ⟨1, by simp, by simp⟩
  uniq := by subsingleton

@[simp, deprecated StdSimplex.weights_apply_eq_one (since := "2026-08-29")]
lemma eq_one_of_unique [Unique X] (s : stdSimplex S X) (x : X) :
    s x = 1 := by
  obtain rfl : s = default := by subsingleton
  rfl

end

/-! ### Barycenter of a Standard Simplex -/

section Barycenter

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Nonempty X]

/-- The barycenter of a standard simplex is the center of mass of
the set of vertices (equally weighted). -/
@[deprecated StdSimplex.barycenter (since := "2026-08-29")]
def barycenter : stdSimplex 𝕜 X :=
  ⟨fun i => (Fintype.card X : 𝕜)⁻¹, by simp [stdSimplex]⟩

/-- The barycenter of a standard simplex has coordinates `(Fintype.card X)⁻¹` at each index. -/
@[simp, deprecated StdSimplex.weights_barycenter_apply (since := "2026-08-29")]
theorem barycenter_apply (x : X) :
    (barycenter : stdSimplex 𝕜 X).val x = (Fintype.card X : 𝕜)⁻¹ := rfl

/-- The barycenter equals the (equal weight) center of mass of vertices (`Finset.centerMass`). -/
@[deprecated "no replacement" (since := "2026-08-29")]
theorem barycenter_eq_centerMass [DecidableEq X] :
    (barycenter : stdSimplex 𝕜 X).val =
      Finset.centerMass Finset.univ (fun _ => (1 : 𝕜)) (fun i => Pi.single i 1) := by
  simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ]
  ext x
  simp [barycenter, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

end Barycenter

end stdSimplex
