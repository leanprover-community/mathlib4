/-
Copyright (c) 2026 Matti Sarjala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matti Sarjala
-/
module
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Codimension-one faces of finite geometric simplicial complexes

This file develops geometric lemmas for finite simplicial complexes and proves
that a codimension-one face in a triangulation of the standard simplex belongs
to at most two top-dimensional faces.

## Main declarations

* `Geometry.SimplicialComplex.affineSpan_eq_affineSpan_space_of_mem_facets`:
  a facet spans the affine hull of the space of a finite convex simplicial complex.
* `Geometry.SimplicialComplex.cofaceApices`: the vertices that extend a face
  by one vertex.
* `Geometry.SimplicialComplex.mem_facets_of_mem_faces_card_eq`: a face of
  maximal cardinality in a triangulation of the standard simplex is a facet.
* `Geometry.SimplicialComplex.card_cofaceApices_le_two_stdSimplex`: a face
  with `n` vertices has at most two one-vertex extensions in a triangulation
  of the standard `n`-simplex.
-/

@[expose] public section
open Finset Set Filter
open scoped Topology Convex

noncomputable section

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E} {s t : Finset E}

/--
The centroid of a face cannot lie in the affine span of the intersection with another
finite set unless the whole face is contained in that set.

This is the support-rigidity step used in the local-star argument for a finite
geometric simplicial complex.
-/
private theorem centroid_mem_affineSpan_inter_imp_subset
    (hs : s ∈ K.faces)
    (hcent : s.centroid ℝ id ∈ affineSpan ℝ (s ∩ t : Set E)) :
    s ⊆ t := by
  intro x hx
  by_contra hxt
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  let u : Set s := {y | (y : E) ∈ t}
  have himage : ((fun y : s => (y : E)) '' u) = (s ∩ t : Set E) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hys, hyt⟩
      exact ⟨⟨y, hys⟩, hyt, rfl⟩
  haveI : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  have hcent' :
      (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) ∈
        affineSpan ℝ ((fun y : s => (y : E)) '' u) := by
    rw [Finset.centroid_univ ℝ s, himage]
    exact hcent
  have hcomb :
      (Finset.univ : Finset s).affineCombination ℝ ((↑) : s → E)
          ((Finset.univ : Finset s).centroidWeights ℝ) ∈
        affineSpan ℝ ((fun y : s => (y : E)) '' u) := by
    simpa [Finset.centroid_def] using hcent'
  have hsum :
      ∑ y ∈ (Finset.univ : Finset s),
          (Finset.univ : Finset s).centroidWeights ℝ y = 1 :=
    (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ
      Finset.univ_nonempty
  let xi : s := ⟨x, hx⟩
  have hxi_not : xi ∉ u := by
    simpa [xi, u] using hxt
  have hzero := (K.indep hs).eq_zero_of_affineCombination_mem_affineSpan
    hsum hcomb (Finset.mem_univ xi) hxi_not
  have hcardNat : #(Finset.univ : Finset s) ≠ 0 :=
    Finset.card_ne_zero.mpr Finset.univ_nonempty
  have hcard : ((#(Finset.univ : Finset s) : ℝ)) ≠ 0 := by
    exact_mod_cast hcardNat
  exact (inv_ne_zero hcard) (by
    simpa [Finset.centroidWeights_apply] using hzero)

/--
If the centroid of one face of a geometric simplicial complex belongs to the convex
hull of another face, then the first face is a subface of the second.
-/
private theorem centroid_mem_convexHull_imp_subset
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hcent : s.centroid ℝ id ∈ convexHull ℝ (t : Set E)) :
    s ⊆ t := by
  apply centroid_mem_affineSpan_inter_imp_subset (K := K) hs
  have hscent : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
    Finset.centroid_mem_convexHull s (K.nonempty_of_mem_faces hs)
  have hboth :
      s.centroid ℝ id ∈
        convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) :=
    ⟨hscent, hcent⟩
  rw [K.convexHull_inter_convexHull hs ht] at hboth
  exact convexHull_subset_affineSpan (s ∩ t : Set E) hboth

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [ContinuousSMul ℝ E] [T2Space E]

/--
A finite geometric simplicial complex is locally equal, near the centroid of a face,
to the union of the simplices containing that face.
-/
private theorem exists_mem_nhds_inter_space_subset_star
    (hK : K.faces.Finite) (hs : s ∈ K.faces) :
    ∃ U ∈ 𝓝 (s.centroid ℝ id),
      ∀ ⦃x⦄, x ∈ U ∩ K.space →
        ∃ t ∈ K.faces, s ⊆ t ∧ x ∈ convexHull ℝ (t : Set E) := by
  let bad : Set (Finset E) := {t | t ∈ K.faces ∧ ¬s ⊆ t}
  let B : Set E := ⋃ t ∈ bad, convexHull ℝ (t : Set E)
  have hbad : bad.Finite := hK.subset (by
    intro t ht
    exact ht.1)
  have hBclosed : IsClosed B := by
    exact hbad.isClosed_biUnion fun t _ =>
      (show (t : Set E).Finite from t.finite_toSet).isClosed_convexHull ℝ
  have hcent_not : s.centroid ℝ id ∉ B := by
    intro hcent
    rcases Set.mem_iUnion₂.mp hcent with ⟨t, htbad, hct⟩
    exact htbad.2 (centroid_mem_convexHull_imp_subset (K := K) hs htbad.1 hct)
  have hnhds : Bᶜ ∈ 𝓝 (s.centroid ℝ id) :=
    hBclosed.isOpen_compl.mem_nhds hcent_not
  refine ⟨Bᶜ, hnhds, ?_⟩
  intro x hx
  rcases hx with ⟨hxB, hxspace⟩
  rcases K.mem_space_iff.mp hxspace with ⟨t, ht, hxt⟩
  refine ⟨t, ht, ?_, hxt⟩
  by_contra hst
  exact hxB (Set.mem_iUnion₂.mpr ⟨t, ⟨ht, hst⟩, hxt⟩)

end Topology

end Geometry.SimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E} {s : Finset E}

/--
Every facet of a finite geometric simplicial complex with convex underlying space
spans the affine hull of the whole space.

This is the purity step in the geometric proof of Sperner's lemma.  The argument is
local: near the centroid of a facet, the complex consists only of simplices containing
that facet; maximality then forces the nearby part of the space to lie in the facet.
Convexity rules out a proper affine span.
-/
theorem affineSpan_eq_affineSpan_space_of_mem_facets
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space) (hs : s ∈ K.facets) :
    affineSpan ℝ (s : Set E) = affineSpan ℝ K.space := by
  rcases mem_facets.mp hs with ⟨hsface, hsmax⟩
  apply le_antisymm
  · exact affineSpan_mono ℝ (K.subset_space hsface)
  · apply affineSpan_le_of_subset_coe
    intro q hq
    by_contra hqspan
    have hsne : s.Nonempty := K.nonempty_of_mem_faces hsface
    have hcconv : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
      Finset.centroid_mem_convexHull s hsne
    have hcspace : s.centroid ℝ id ∈ K.space :=
      K.convexHull_subset_space hsface hcconv
    have hcspan : s.centroid ℝ id ∈ affineSpan ℝ (s : Set E) :=
      convexHull_subset_affineSpan (s : Set E) hcconv
    obtain ⟨U, hU, hstar⟩ :=
      exists_mem_nhds_inter_space_subset_star (K := K) hK hsface
    have hlocal : U ∩ K.space ⊆ convexHull ℝ (s : Set E) := by
      intro x hx
      rcases hstar hx with ⟨t, ht, hst, hxt⟩
      have hst' : s = t := hsmax t ht hst
      simpa [hst'] using hxt
    have hline_nhds :
        {r : ℝ | AffineMap.lineMap (s.centroid ℝ id) q r ∈ U} ∈ 𝓝 0 := by
      have hcont :
          ContinuousAt (AffineMap.lineMap (s.centroid ℝ id) q : ℝ → E) (0 : ℝ) :=
        AffineMap.lineMap_continuous.continuousAt
      have hU0 : U ∈ 𝓝 (AffineMap.lineMap (s.centroid ℝ id) q (0 : ℝ)) := by
        simpa using hU
      exact hcont hU0
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hline_nhds
    let r : ℝ := min (ε / 2) (1 / 2)
    have hrpos : 0 < r := by
      dsimp [r]
      exact lt_min (by positivity) (by norm_num)
    have hrltε : r < ε := by
      calc
        r ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    have hrlt1 : r < 1 := by
      calc
        r ≤ 1 / 2 := min_le_right _ _
        _ < 1 := by norm_num
    have hrball : r ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hrpos]
      exact hrltε
    have hrU : AffineMap.lineMap (s.centroid ℝ id) q r ∈ U :=
      hεU hrball
    have hrspace : AffineMap.lineMap (s.centroid ℝ id) q r ∈ K.space :=
      hconv.segment_subset hcspace hq
        (lineMap_mem_segment ℝ (s.centroid ℝ id) q ⟨hrpos.le, hrlt1.le⟩)
    have hrhull :
        AffineMap.lineMap (s.centroid ℝ id) q r ∈ convexHull ℝ (s : Set E) :=
      hlocal ⟨hrU, hrspace⟩
    have hrspan :
        AffineMap.lineMap (s.centroid ℝ id) q r ∈ affineSpan ℝ (s : Set E) :=
      convexHull_subset_affineSpan (s : Set E) hrhull
    have hsmul : r • (q -ᵥ s.centroid ℝ id) ∈
        (affineSpan ℝ (s : Set E)).direction := by
      have hv := (affineSpan ℝ (s : Set E)).vsub_mem_direction hrspan hcspan
      simpa [AffineMap.lineMap_apply] using hv
    have hv : q -ᵥ s.centroid ℝ id ∈
        (affineSpan ℝ (s : Set E)).direction := by
      rwa [(affineSpan ℝ (s : Set E)).direction.smul_mem_iff hrpos.ne'] at hsmul
    apply hqspan
    rw [← vsub_vadd q (s.centroid ℝ id)]
    exact (affineSpan ℝ (s : Set E)).vadd_mem_of_mem_direction hv hcspan

end Geometry.SimplicialComplex

namespace Affine.Simplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} [NeZero n]

/--
Let `w` be affine coordinates of a point lying strictly on the same side of the
facet opposite `i` as the vertex `i`.  A sufficiently small positive mixture of
`w` with the uniform weights on the opposite facet has every coordinate positive.

This is the finite-dimensional epsilon step in the same-side overlap argument.
-/
private theorem exists_small_pos_all_coordinates
    (i : Fin (n + 1)) {w : Fin (n + 1) → ℝ} (hwi : 0 < w i) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      ∀ j,
        0 < (1 - r) * (({i}ᶜ : Finset (Fin (n + 1))).centroidWeightsIndicator ℝ j) +
          r * w j := by
  let μ : Fin (n + 1) → ℝ :=
    ({i}ᶜ : Finset (Fin (n + 1))).centroidWeightsIndicator ℝ
  have hμpos : ∀ j, j ≠ i → 0 < μ j := by
    intro j hji
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    simp only [μ, Finset.centroidWeightsIndicator_def, Set.indicator_of_mem,
      Finset.mem_coe, Finset.mem_compl, Finset.mem_singleton, not_false_eq_true,
      hji, Finset.centroidWeights_apply]
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton,
      Nat.add_sub_cancel]
    exact inv_pos.mpr hnpos
  have hnear :
      ∀ᶠ r in 𝓝 (0 : ℝ),
        ∀ j, j ≠ i → 0 < (1 - r) * μ j + r * w j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · filter_upwards [] with r
      intro hne
      exact (hne hji).elim
    · have hcont :
          ContinuousAt (fun r : ℝ => (1 - r) * μ j + r * w j) (0 : ℝ) := by
        fun_prop
      have h0 : 0 < (1 - (0 : ℝ)) * μ j + 0 * w j := by
        simpa using hμpos j hji
      have hev :
          {r : ℝ | 0 < (1 - r) * μ j + r * w j} ∈ 𝓝 (0 : ℝ) := by
        exact hcont (Ioi_mem_nhds h0)
      filter_upwards [hev] with r hr
      intro _
      exact hr
  have hlt_one : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds zero_lt_one
  have hgood :
      ({r : ℝ | ∀ j, j ≠ i → 0 < (1 - r) * μ j + r * w j} ∩ Set.Iio 1) ∈
        𝓝 (0 : ℝ) :=
    inter_mem hnear hlt_one
  obtain ⟨r, hrGood, hrpos⟩ :=
    nonempty_nhds_inter_Ioi hgood (by simp : ¬ IsMax (0 : ℝ))
  refine ⟨r, ⟨hrpos, hrGood.2⟩, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    have hμi : μ i = 0 := by
      simp [μ, Finset.centroidWeightsIndicator_def]
    simp [μ, hμi, mul_pos hrpos hwi]
  · simpa [μ] using hrGood.1 j hji

/--
If `q` is strictly on the same side of the facet opposite `i` as the vertex `i`,
then the open segment from the opposite-facet centroid towards `q` enters the
interior of the simplex.

The witness is an explicit sufficiently small positive line-map parameter.  This
is the core overlap lemma needed to show that two top-dimensional simplices in a
geometric simplicial complex cannot share a facet and have their opposite vertices
on the same side of that facet.
-/
private theorem exists_lineMap_faceOppositeCentroid_mem_interior
    (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)) {q : E}
    (hq : q ∈ affineSpan ℝ (Set.range s.points))
    (hsame :
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide
        (s.points i) q) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (s.faceOppositeCentroid i) q r ∈ s.interior := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  have hwi : 0 < w i :=
    (s.sSameSide_affineSpan_faceOpposite_point_left_iff hw).mp hsame
  obtain ⟨r, hr, hpos⟩ := exists_small_pos_all_coordinates (n := n) i hwi
  let μ : Fin (n + 1) → ℝ :=
    ({i}ᶜ : Finset (Fin (n + 1))).centroidWeightsIndicator ℝ
  let ν : Fin (n + 1) → ℝ :=
    fun j => (1 - r) * μ j + r * w j
  have hcomp : ({i}ᶜ : Finset (Fin (n + 1))).Nonempty := by
    obtain ⟨j, hji⟩ := exists_ne i
    exact ⟨j, by simp [hji]⟩
  have hμsum : ∑ j, μ j = 1 := by
    simpa [μ] using
      (({i}ᶜ : Finset (Fin (n + 1))).sum_centroidWeightsIndicator_eq_one_of_nonempty
        ℝ hcomp)
  have hνsum : ∑ j, ν j = 1 := by
    simp only [ν, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hμsum, hw]
    ring
  have hνpos : ∀ j, 0 < ν j := by
    intro j
    simpa [ν, μ] using hpos j
  have hνlt : ∀ j, ν j < 1 := by
    intro j
    rw [← hνsum]
    obtain ⟨k, hkj⟩ := exists_ne j
    exact Finset.single_lt_sum hkj (Finset.mem_univ j) (Finset.mem_univ k)
      (hνpos k) (fun z _ _ => (hνpos z).le)
  have hνinterior :
      Finset.univ.affineCombination ℝ s.points ν ∈ s.interior := by
    rw [s.affineCombination_mem_interior_iff hνsum]
    intro j
    exact ⟨hνpos j, hνlt j⟩
  have hface :
      s.faceOppositeCentroid i =
        Finset.univ.affineCombination ℝ s.points μ := by
    calc
      s.faceOppositeCentroid i
          = ({i}ᶜ : Finset (Fin (n + 1))).centroid ℝ s.points := by
              rw [s.faceOppositeCentroid_eq_affineCombination]
              simp [Finset.centroid_def, Finset.centroidWeights_apply,
                Finset.card_compl, Fintype.card_fin]
      _ = Finset.univ.affineCombination ℝ s.points μ := by
            simpa [μ] using
              (({i}ᶜ : Finset (Fin (n + 1))).centroid_eq_affineCombination_fintype
                ℝ s.points)
  have hline :
      AffineMap.lineMap (s.faceOppositeCentroid i)
          (Finset.univ.affineCombination ℝ s.points w) r =
        Finset.univ.affineCombination ℝ s.points ν := by
    rw [hface, ← AffineMap.apply_lineMap]
    congr 1
    ext j
    simp [ν, μ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    ring
  refine ⟨r, hr, ?_⟩
  rw [hline]
  exact hνinterior

end Affine.Simplex

namespace Affine.Simplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}


/-- The closed interior of a simplex is exactly the convex hull of its vertices. -/
private theorem closedInterior_eq_convexHull_range
    (s : Affine.Simplex ℝ E n) :
    s.closedInterior = convexHull ℝ (Set.range s.points) := by
  apply Set.Subset.antisymm
  · rintro p ⟨w, hw, hwI, rfl⟩
    exact affineCombination_mem_convexHull (fun i _ => (hwI i).1) hw
  · apply convexHull_min
    · rintro p ⟨i, rfl⟩
      exact s.point_mem_closedInterior i
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨wx, hwx, hxI, rfl⟩
      rcases hy with ⟨wy, hwy, hyI, rfl⟩
      let w : Fin (n + 1) → ℝ := fun i => a * wx i + b * wy i
      have hwsum : ∑ i, w i = 1 := by
        simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hwx, hwy]
        simpa only [mul_one] using hab
      refine ⟨w, hwsum, ?_, ?_⟩
      · intro i
        constructor
        · exact add_nonneg (mul_nonneg ha (hxI i).1) (mul_nonneg hb (hyI i).1)
        · calc
            a * wx i + b * wy i ≤ a * 1 + b * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left (hxI i).2 ha)
                (mul_le_mul_of_nonneg_left (hyI i).2 hb)
            _ = 1 := by simpa using hab
      · simp only [Finset.affineCombination_eq_linear_combination _ _ _ hwsum,
          Finset.affineCombination_eq_linear_combination _ _ _ hwx,
          Finset.affineCombination_eq_linear_combination _ _ _ hwy,
          w, Finset.sum_add_distrib, add_smul, mul_smul]
        rw [← Finset.smul_sum, ← Finset.smul_sum]

/-- The interior of a positive-dimensional simplex is disjoint from the convex hull
of any opposite facet. -/
private theorem disjoint_interior_convexHull_faceOpposite
    [NeZero n] (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)) :
    Disjoint s.interior (convexHull ℝ (Set.range (s.faceOpposite i).points)) := by
  rw [← closedInterior_eq_convexHull_range (s.faceOpposite i)]
  exact disjoint_interior_closedInterior_faceOpposite s i

/-- The centroid of the facet opposite `i` belongs to the convex hull of that facet. -/
private theorem faceOppositeCentroid_mem_convexHull_range
    [NeZero n] (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈
      convexHull ℝ (Set.range (s.faceOpposite i).points) := by
  unfold faceOppositeCentroid
  rw [Affine.Simplex.centroid_eq_affineCombination]
  apply affineCombination_mem_convexHull
  · intro j _
    rw [Finset.centroidWeights_apply]
    positivity
  · have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hindexpos : 0 < n - 1 + 1 := by
      rw [Nat.sub_add_cancel hnpos]
      exact hnpos
    have hnonempty :
        (Finset.univ : Finset (Fin (n - 1 + 1))).Nonempty := by
      exact ⟨⟨0, hindexpos⟩, Finset.mem_univ _⟩
    exact
      ((Finset.univ : Finset (Fin (n - 1 + 1))).sum_centroidWeights_eq_one_of_nonempty
        ℝ hnonempty)

/--
A point strictly on the same side of a facet as the opposite vertex generates,
together with the facet, a convex set whose interior overlaps the reference simplex.

The conclusion is stated without constructing a second indexed simplex: the second
cell is represented by the convex hull of the new apex and the common facet.
-/
private theorem interior_inter_convexHull_insert_faceOpposite_nonempty
    [NeZero n] (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)) {q : E}
    (hq : q ∈ affineSpan ℝ (Set.range s.points))
    (hsame :
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide
        (s.points i) q) :
    (s.interior ∩
      convexHull ℝ (insert q (Set.range (s.faceOpposite i).points))).Nonempty := by
  obtain ⟨r, hr, hpint⟩ :=
    exists_lineMap_faceOppositeCentroid_mem_interior s i hq hsame
  refine ⟨AffineMap.lineMap (s.faceOppositeCentroid i) q r, hpint, ?_⟩
  have hface :
      s.faceOppositeCentroid i ∈
        convexHull ℝ (insert q (Set.range (s.faceOpposite i).points)) := by
    exact convexHull_mono (Set.subset_insert q _) (faceOppositeCentroid_mem_convexHull_range s i)
  have hqmem :
      q ∈ convexHull ℝ (insert q (Set.range (s.faceOpposite i).points)) :=
    subset_convexHull ℝ _ (Set.mem_insert q _)
  exact
    (convex_convexHull ℝ (insert q (Set.range (s.faceOpposite i).points))).segment_subset
      hface hqmem
      (lineMap_mem_segment ℝ (s.faceOppositeCentroid i) q ⟨hr.1.le, hr.2.le⟩)

end Affine.Simplex

namespace Affine.Simplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} [NeZero n]

/--
If the convex hull of a simplex and the convex hull generated by a new apex and an
opposite facet may intersect only inside that facet, then the new apex cannot lie
strictly on the same side of the facet as the old opposite vertex.

This packages the exact contradiction used by the gluing axiom of a geometric
simplicial complex.
-/
private theorem not_sSameSide_of_inter_subset_convexHull_faceOpposite
    (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)) {q : E}
    (hq : q ∈ affineSpan ℝ (Set.range s.points))
    (hglue :
      convexHull ℝ (Set.range s.points) ∩
          convexHull ℝ (insert q (Set.range (s.faceOpposite i).points)) ⊆
        convexHull ℝ (Set.range (s.faceOpposite i).points)) :
    ¬(affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide
        (s.points i) q := by
  intro hsame
  obtain ⟨p, hpint, hpsecond⟩ :=
    interior_inter_convexHull_insert_faceOpposite_nonempty s i hq hsame
  have hpfirst : p ∈ convexHull ℝ (Set.range s.points) := by
    rw [← closedInterior_eq_convexHull_range s]
    exact s.interior_subset_closedInterior hpint
  have hpface : p ∈ convexHull ℝ (Set.range (s.faceOpposite i).points) :=
    hglue ⟨hpfirst, hpsecond⟩
  exact
    Set.disjoint_left.mp (disjoint_interior_convexHull_faceOpposite s i)
      hpint hpface

end Affine.Simplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E}
variable {n : ℕ} [NeZero n]

/-- Classical decidable equality used while indexing a top-dimensional face. -/
local instance topFaceIndexDecidableEq :
    DecidableEq E := Classical.decEq E

/--
A top face written as `insert a F`, where `F` has `n` vertices, can be indexed as an
`n`-simplex so that one distinguished index is the apex `a` and the opposite facet
has exactly the vertex set `F`.
-/
private theorem exists_simplex_index_range_eq_insert_and_faceOpposite_eq
    {F : Finset E} {a : E} (ha : a ∉ F) (hFcard : #F = n)
    (ht : insert a F ∈ K.faces) :
    ∃ (s : Affine.Simplex ℝ E n) (i : Fin (n + 1)),
      s.points i = a ∧
      Set.range s.points = (insert a F : Set E) ∧
      Set.range (s.faceOpposite i).points = (F : Set E) := by
  classical
  have hcard : Fintype.card (insert a F : Finset E) = n + 1 := by
    simp [Fintype.card_coe, Finset.card_insert_of_notMem ha, hFcard]
  let e : (insert a F : Finset E) ≃ Fin (n + 1) :=
    Fintype.equivFinOfCardEq hcard
  let s : Affine.Simplex ℝ E n :=
    { points := fun j => (e.symm j : E)
      independent := (K.indep ht).comp_embedding e.symm.toEmbedding }
  let i : Fin (n + 1) := e ⟨a, Finset.mem_insert_self a F⟩
  refine ⟨s, i, ?_, ?_, ?_⟩
  · simp [s, i]
  · ext x
    constructor
    · rintro ⟨j, rfl⟩
      change (e.symm j : E) = a ∨ (e.symm j : E) ∈ (F : Set E)
      rcases Finset.mem_insert.mp (e.symm j).property with hja | hjF
      · exact Or.inl hja
      · exact Or.inr hjF
    · intro hx
      refine ⟨e ⟨x, ?_⟩, ?_⟩
      · simpa using hx
      · simp [s]
  · rw [Affine.Simplex.range_faceOpposite_points s i]
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjne : j ≠ i := by simpa using hj
      have hmem : s.points j ∈ insert a F := by
        change (e.symm j : E) ∈ insert a F
        exact (e.symm j).property
      rw [Finset.mem_insert] at hmem
      rcases hmem with hja | hjF
      · exfalso
        apply hjne
        apply e.symm.injective
        apply Subtype.ext
        simpa [s, i] using hja
      · exact hjF
    · intro hxF
      let y : (insert a F : Finset E) :=
        ⟨x, Finset.mem_insert_of_mem hxF⟩
      let j : Fin (n + 1) := e y
      have hjne : j ≠ i := by
        intro hji
        have hya : y = ⟨a, Finset.mem_insert_self a F⟩ := e.injective hji
        have hxa : x = a := by
          simpa [y] using congrArg Subtype.val hya
        exact ha (by simpa [hxa] using hxF)
      refine ⟨j, by simpa using hjne, ?_⟩
      simp [s, j, y]

/--
Two distinct top faces of a geometric simplicial complex that share the codimension-one
face `F` cannot have their opposite vertices on the same strict side of `affineSpan F`.

The only ambient-dimensional input is that the second apex lies in the affine span of
the first top face.  In a pure triangulation this follows from the purity theorem.
-/
private theorem not_sSameSide_of_two_insert_faces
    {F : Finset E} {a₁ a₂ : E}
    (ha₁ : a₁ ∉ F) (ha₂ : a₂ ∉ F) (ha : a₁ ≠ a₂)
    (hFcard : #F = n)
    (ht₁ : insert a₁ F ∈ K.faces) (ht₂ : insert a₂ F ∈ K.faces)
    (ha₂span : a₂ ∈ affineSpan ℝ (insert a₁ F : Set E)) :
    ¬(affineSpan ℝ (F : Set E)).SSameSide a₁ a₂ := by
  classical
  obtain ⟨s, i, hsi, hsrange, hsface⟩ :=
    exists_simplex_index_range_eq_insert_and_faceOpposite_eq
      (K := K) (n := n) ha₁ hFcard ht₁
  have hinter : insert a₁ F ∩ insert a₂ F = F := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h₁ | hF₁, h₂ | hF₂⟩
      · exact (ha (h₁.symm.trans h₂)).elim
      · exact (ha₁ (h₁ ▸ hF₂)).elim
      · exact (ha₂ (h₂ ▸ hF₁)).elim
      · exact hF₁
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  have hinterSet :
      insert a₁ (F : Set E) ∩ insert a₂ (F : Set E) = (F : Set E) := by
    ext x
    simpa using congrArg (fun G : Finset E => x ∈ G) hinter
  have hq : a₂ ∈ affineSpan ℝ (Set.range s.points) := by
    rw [hsrange]
    exact ha₂span
  have hglue :
      convexHull ℝ (Set.range s.points) ∩
          convexHull ℝ (insert a₂ (Set.range (s.faceOpposite i).points)) ⊆
        convexHull ℝ (Set.range (s.faceOpposite i).points) := by
    simpa only [Finset.coe_insert, hsrange, hsface, hinterSet] using
      K.inter_subset_convexHull ht₁ ht₂
  have hnot :=
    Affine.Simplex.not_sSameSide_of_inter_subset_convexHull_faceOpposite
      s i hq hglue
  simpa only [hsface, hsi] using hnot

end Geometry.SimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E}
variable {n : ℕ} [NeZero n]

/-- Classical decidable equality used in the three-top-faces argument. -/
local instance threeTopFacesDecidableEq :
    DecidableEq E := Classical.decEq E

/--
Three distinct top faces of the form `insert a F` cannot occur around the same
codimension-one face when their affine spans agree.

The proof uses one face as a reference simplex.  The two other apices cannot have
positive opposite-vertex coordinates, by the same-side prohibition.  They also
cannot have zero coordinates, because each enlarged face is affinely independent.
Thus both coordinates are negative, forcing those two apices to lie on the same
side of `affineSpan F`, a contradiction.
-/
private theorem not_three_insert_faces
    {F : Finset E} {a₀ a₁ a₂ : E}
    (ha₀F : a₀ ∉ F) (ha₁F : a₁ ∉ F) (ha₂F : a₂ ∉ F)
    (ha₀₁ : a₀ ≠ a₁) (ha₀₂ : a₀ ≠ a₂) (ha₁₂ : a₁ ≠ a₂)
    (hFcard : #F = n)
    (ht₀ : insert a₀ F ∈ K.faces)
    (ht₁ : insert a₁ F ∈ K.faces)
    (ht₂ : insert a₂ F ∈ K.faces)
    (ha₁span₀ : a₁ ∈ affineSpan ℝ (insert a₀ F : Set E))
    (ha₂span₀ : a₂ ∈ affineSpan ℝ (insert a₀ F : Set E))
    (ha₂span₁ : a₂ ∈ affineSpan ℝ (insert a₁ F : Set E)) : False := by
  obtain ⟨s₀, i₀, hsi₀, hs₀range, hs₀face⟩ :=
    Geometry.SimplicialComplex.exists_simplex_index_range_eq_insert_and_faceOpposite_eq
      (K := K) (n := n) ha₀F hFcard ht₀
  have ha₁spanS : a₁ ∈ affineSpan ℝ (Set.range s₀.points) := by
    rw [hs₀range]
    exact ha₁span₀
  have ha₂spanS : a₂ ∈ affineSpan ℝ (Set.range s₀.points) := by
    rw [hs₀range]
    exact ha₂span₀
  obtain ⟨w₁, hw₁, hrep₁⟩ :=
    eq_affineCombination_of_mem_affineSpan_of_fintype ha₁spanS
  obtain ⟨w₂, hw₂, hrep₂⟩ :=
    eq_affineCombination_of_mem_affineSpan_of_fintype ha₂spanS
  obtain ⟨s₁, i₁, hsi₁, -, hs₁face⟩ :=
    Geometry.SimplicialComplex.exists_simplex_index_range_eq_insert_and_faceOpposite_eq
      (K := K) (n := n) ha₁F hFcard ht₁
  obtain ⟨s₂, i₂, hsi₂, -, hs₂face⟩ :=
    Geometry.SimplicialComplex.exists_simplex_index_range_eq_insert_and_faceOpposite_eq
      (K := K) (n := n) ha₂F hFcard ht₂
  have ha₁notH : a₁ ∉ affineSpan ℝ (F : Set E) := by
    intro ha₁H
    apply Affine.Simplex.points_notMem_affineSpan_faceOpposite s₁ i₁
    rw [hsi₁, hs₁face]
    exact ha₁H
  have ha₂notH : a₂ ∉ affineSpan ℝ (F : Set E) := by
    intro ha₂H
    apply Affine.Simplex.points_notMem_affineSpan_faceOpposite s₂ i₂
    rw [hsi₂, hs₂face]
    exact ha₂H
  have hw₁ne : w₁ i₀ ≠ 0 := by
    intro hwzero
    apply ha₁notH
    rw [← hs₀face, hrep₁]
    exact (s₀.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).2 hwzero
  have hw₂ne : w₂ i₀ ≠ 0 := by
    intro hwzero
    apply ha₂notH
    rw [← hs₀face, hrep₂]
    exact (s₀.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).2 hwzero
  have hnot₀₁ : ¬(affineSpan ℝ (F : Set E)).SSameSide a₀ a₁ :=
    Geometry.SimplicialComplex.not_sSameSide_of_two_insert_faces
      (K := K) (n := n) ha₀F ha₁F ha₀₁ hFcard ht₀ ht₁ ha₁span₀
  have hnot₀₂ : ¬(affineSpan ℝ (F : Set E)).SSameSide a₀ a₂ :=
    Geometry.SimplicialComplex.not_sSameSide_of_two_insert_faces
      (K := K) (n := n) ha₀F ha₂F ha₀₂ hFcard ht₀ ht₂ ha₂span₀
  have hw₁notpos : ¬0 < w₁ i₀ := by
    intro hwpos
    apply hnot₀₁
    have href :=
      (s₀.sSameSide_affineSpan_faceOpposite_point_left_iff hw₁).2 hwpos
    simpa [hsi₀, hs₀face, hrep₁] using href
  have hw₂notpos : ¬0 < w₂ i₀ := by
    intro hwpos
    apply hnot₀₂
    have href :=
      (s₀.sSameSide_affineSpan_faceOpposite_point_left_iff hw₂).2 hwpos
    simpa [hsi₀, hs₀face, hrep₂] using href
  have hw₁le : w₁ i₀ ≤ 0 := le_of_not_gt hw₁notpos
  have hw₂le : w₂ i₀ ≤ 0 := le_of_not_gt hw₂notpos
  have hw₁neg : w₁ i₀ < 0 := lt_of_le_of_ne hw₁le hw₁ne
  have hw₂neg : w₂ i₀ < 0 := lt_of_le_of_ne hw₂le hw₂ne
  have hsign : SignType.sign (w₁ i₀) = SignType.sign (w₂ i₀) := by
    rw [sign_neg hw₁neg, sign_neg hw₂neg]
  have href₁₂ :
      (affineSpan ℝ (Set.range (s₀.faceOpposite i₀).points)).SSameSide
        (Finset.univ.affineCombination ℝ s₀.points w₁)
        (Finset.univ.affineCombination ℝ s₀.points w₂) :=
    s₀.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hsign hw₁ne
  have hsame₁₂ : (affineSpan ℝ (F : Set E)).SSameSide a₁ a₂ := by
    simpa [hs₀face, hrep₁, hrep₂] using href₁₂
  exact
    (Geometry.SimplicialComplex.not_sSameSide_of_two_insert_faces
      (K := K) (n := n) ha₁F ha₂F ha₁₂ hFcard ht₁ ht₂ ha₂span₁) hsame₁₂

end Geometry.SimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E}
variable {n : ℕ} [NeZero n]

/-- Classical decidable equality used for finite families of coface apices. -/
local instance finiteApexFamilyDecidableEq :
    DecidableEq E := Classical.decEq E

/--
A finite family of apices producing top faces around one codimension-one face has
cardinality at most two, provided all those top faces span one common affine space.
-/
private theorem card_apices_le_two
    {F A : Finset E} {H : AffineSubspace ℝ E}
    (hFcard : #F = n)
    (hA : ∀ a ∈ A, a ∉ F ∧ insert a F ∈ K.faces)
    (hspan : ∀ a ∈ A, affineSpan ℝ (insert a F : Set E) = H) :
    #A ≤ 2 := by
  by_contra hle
  have hthree : 3 ≤ #A := by
    exact Nat.lt_of_not_ge hle
  let eA : A ≃ Fin (#A) :=
    Fintype.equivFinOfCardEq (by
      simp)
  let emb : Fin 3 ↪ E :=
    (Fin.castLEEmb hthree).trans
      (eA.symm.toEmbedding.trans (Function.Embedding.subtype _))
  let a₀ : E := emb 0
  let a₁ : E := emb 1
  let a₂ : E := emb 2
  have ha₀A : a₀ ∈ A := by
    change (eA.symm (Fin.castLE hthree 0) : E) ∈ A
    exact (eA.symm (Fin.castLE hthree 0)).property
  have ha₁A : a₁ ∈ A := by
    change (eA.symm (Fin.castLE hthree 1) : E) ∈ A
    exact (eA.symm (Fin.castLE hthree 1)).property
  have ha₂A : a₂ ∈ A := by
    change (eA.symm (Fin.castLE hthree 2) : E) ∈ A
    exact (eA.symm (Fin.castLE hthree 2)).property
  have ha₀₁ : a₀ ≠ a₁ := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (emb.injective h)
  have ha₀₂ : a₀ ≠ a₂ := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (emb.injective h)
  have ha₁₂ : a₁ ≠ a₂ := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (emb.injective h)
  obtain ⟨ha₀F, ht₀⟩ := hA a₀ ha₀A
  obtain ⟨ha₁F, ht₁⟩ := hA a₁ ha₁A
  obtain ⟨ha₂F, ht₂⟩ := hA a₂ ha₂A
  have ha₁span₀ : a₁ ∈ affineSpan ℝ (insert a₀ F : Set E) := by
    rw [hspan a₀ ha₀A, ← hspan a₁ ha₁A]
    exact mem_affineSpan ℝ (Set.mem_insert a₁ _)
  have ha₂span₀ : a₂ ∈ affineSpan ℝ (insert a₀ F : Set E) := by
    rw [hspan a₀ ha₀A, ← hspan a₂ ha₂A]
    exact mem_affineSpan ℝ (Set.mem_insert a₂ _)
  have ha₂span₁ : a₂ ∈ affineSpan ℝ (insert a₁ F : Set E) := by
    rw [hspan a₁ ha₁A, ← hspan a₂ ha₂A]
    exact mem_affineSpan ℝ (Set.mem_insert a₂ _)
  exact Geometry.SimplicialComplex.not_three_insert_faces
    (K := K) (n := n)
    ha₀F ha₁F ha₂F ha₀₁ ha₀₂ ha₁₂ hFcard
    ht₀ ht₁ ht₂ ha₁span₀ ha₂span₀ ha₂span₁

end Geometry.SimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : Geometry.SimplicialComplex ℝ E}
variable {n : ℕ}

/-- Classical decidable equality used for finite vertices and coface apices. -/
local instance finiteComplexVerticesDecidableEq :
    DecidableEq E := Classical.decEq E

/-- The finite set of all vertices occurring in a finite geometric simplicial complex. -/
noncomputable def finiteVertices (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) : Finset E :=
  hK.toFinset.biUnion fun s => s

@[simp]
theorem mem_finiteVertices_iff (hK : K.faces.Finite) {x : E} :
    x ∈ K.finiteVertices hK ↔ ∃ s ∈ K.faces, x ∈ s := by
  rw [finiteVertices]
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hxs⟩
    exact ⟨s, by simpa using hs, hxs⟩
  · rintro ⟨s, hs, hxs⟩
    exact Finset.mem_biUnion.mpr ⟨s, by simpa using hs, hxs⟩

/--
The possible opposite vertices of top cofaces of `F`. An apex `a` represents the
coface `insert a F`.
-/
noncomputable def cofaceApices (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (F : Finset E) : Finset E := by
  classical
  exact
    (K.finiteVertices hK).filter fun a =>
      a ∉ F ∧ insert a F ∈ K.faces

private theorem mem_cofaceApices_iff_internal
    (hK : K.faces.Finite) {F : Finset E} {a : E} :
    a ∈ K.cofaceApices hK F ↔ a ∉ F ∧ insert a F ∈ K.faces := by
  classical
  rw [cofaceApices, Finset.mem_filter]
  constructor
  · intro ha
    exact ha.2
  · intro ha
    refine ⟨?_, ha⟩
    apply (Geometry.SimplicialComplex.mem_finiteVertices_iff
      (K := K) hK).2
    exact ⟨insert a F, ha.2, Finset.mem_insert_self a F⟩

@[simp]
theorem mem_cofaceApices_iff [DecidableEq E]
    (hK : K.faces.Finite) {F : Finset E} {a : E} :
    a ∈ K.cofaceApices hK F ↔ a ∉ F ∧ insert a F ∈ K.faces := by
  constructor
  · intro ha
    obtain ⟨haF, haFace⟩ :=
      (mem_cofaceApices_iff_internal (K := K) hK).1 ha
    refine ⟨haF, ?_⟩
    convert haFace using 1
    ext x
    simp
  · rintro ⟨haF, haFace⟩
    apply (mem_cofaceApices_iff_internal (K := K) hK).2
    refine ⟨haF, ?_⟩
    convert haFace using 1
    ext x
    simp
/--
If every top coface represented by `cofaceApices` is a facet of a finite complex with
convex space, then a codimension-one face has at most two such cofaces.
-/
private theorem card_cofaceApices_le_two
    [NeZero n]
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    {F : Finset E} (hFcard : #F = n)
    (hfacet : ∀ a ∈ K.cofaceApices hK F, insert a F ∈ K.facets) :
    #(K.cofaceApices hK F) ≤ 2 := by
  refine Geometry.SimplicialComplex.card_apices_le_two
    (K := K) (n := n) (H := affineSpan ℝ K.space) hFcard ?_ ?_
  · intro a ha
    exact
      (Geometry.SimplicialComplex.mem_cofaceApices_iff
        (K := K) hK).1 ha
  · intro a ha
    have hspan :=
      Geometry.SimplicialComplex.affineSpan_eq_affineSpan_space_of_mem_facets
        (K := K) hK hconv (hfacet a ha)
    simpa only [Finset.coe_insert] using hspan

end Geometry.SimplicialComplex

namespace Geometry.SimplicialComplex

variable {n : ℕ}

/-- The canonical vertices of the standard `n`-simplex. -/
private noncomputable def stdSimplexVertices (n : ℕ) :
    Finset (Fin (n + 1) → ℝ) := by
  classical
  exact Finset.univ.image fun i : Fin (n + 1) => Pi.single i 1

private theorem stdSimplexVertex_injective (n : ℕ) :
    Function.Injective (fun i : Fin (n + 1) => Pi.single i (1 : ℝ)) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij j
  simp [hne] at h

@[simp]
private theorem card_stdSimplexVertices (n : ℕ) :
    #(stdSimplexVertices n) = n + 1 := by
  classical
  rw [stdSimplexVertices,
    Finset.card_image_of_injective _ (stdSimplexVertex_injective n)]
  simp

@[simp]
private theorem coe_stdSimplexVertices (n : ℕ) :
    (stdSimplexVertices n : Set (Fin (n + 1) → ℝ)) =
      Set.range (fun i : Fin (n + 1) => Pi.single i 1) := by
  classical
  ext x
  simp [stdSimplexVertices]

/-- The affine span of the canonical vertices is the affine span of the standard simplex. -/
private theorem affineSpan_stdSimplexVertices (n : ℕ) :
    affineSpan ℝ (stdSimplexVertices n : Set (Fin (n + 1) → ℝ)) =
      affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) := by
  rw [coe_stdSimplexVertices n,
    ← convexHull_rangle_single_eq_stdSimplex ℝ (Fin (n + 1)),
    affineSpan_convexHull]

variable {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
variable {s : Finset (Fin (n + 1) → ℝ)}

/--
A face with `n + 1` vertices in a triangulation of the standard `n`-simplex spans
that standard simplex. The proof avoids an explicit dimension computation: a strict
affine-span inclusion into the canonical `n + 1` vertices would force a strict
cardinality inequality between two finsets of the same size.
-/
private theorem affineSpan_eq_affineSpan_stdSimplex_of_mem_faces_card
    (hspace : K.space = stdSimplex ℝ (Fin (n + 1)))
    (hs : s ∈ K.faces) (hscard : #s = n + 1) :
    affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) =
      affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) := by
  classical
  have hsubset :
      (s : Set (Fin (n + 1) → ℝ)) ⊆
        stdSimplex ℝ (Fin (n + 1)) := by
    intro x hx
    rw [← hspace]
    exact K.subset_space hs hx
  have hle :
      affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) ≤
        affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) :=
    affineSpan_mono ℝ hsubset
  apply le_antisymm hle
  by_contra hnot
  have hlt :
      affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) <
        affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) := by
    exact lt_of_le_of_ne hle (fun heq => hnot heq.ge)
  have hlt' :
      affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) <
        affineSpan ℝ
          (stdSimplexVertices n : Set (Fin (n + 1) → ℝ)) := by
    rw [affineSpan_stdSimplexVertices n]
    exact hlt
  have hcardlt :
      #s < #(stdSimplexVertices n) :=
    (K.indep hs).card_lt_card_of_affineSpan_lt_affineSpan hlt'
  rw [hscard, card_stdSimplexVertices n] at hcardlt
  exact (Nat.lt_irrefl (n + 1)) hcardlt

/-- Every face of a finite simplicial complex is contained in a facet. -/
private theorem exists_mem_facets_superset
    (hK : K.faces.Finite) (hs : s ∈ K.faces) :
    ∃ t ∈ K.facets, s ⊆ t := by
  classical
  obtain ⟨t, hst, htmax⟩ := hK.exists_le_maximal hs
  refine ⟨t, ?_, hst⟩
  apply (Geometry.SimplicialComplex.mem_facets (K := K)).2
  refine ⟨htmax.1, ?_⟩
  intro u hu htu
  exact Finset.Subset.antisymm htu (htmax.2 hu htu)

/--
In a finite triangulation of the standard `n`-simplex, every face with `n + 1`
vertices is a facet.
-/
theorem mem_facets_of_mem_faces_card_eq
    (hK : K.faces.Finite)
    (hspace : K.space = stdSimplex ℝ (Fin (n + 1)))
    (hs : s ∈ K.faces) (hscard : #s = n + 1) :
    s ∈ K.facets := by
  classical
  obtain ⟨t, htFacet, hst⟩ :=
    Geometry.SimplicialComplex.exists_mem_facets_superset
      (K := K) hK hs
  have htFaces : t ∈ K.faces :=
    Geometry.SimplicialComplex.facets_subset htFacet
  have hconv : Convex ℝ K.space := by
    rw [hspace]
    exact convex_stdSimplex ℝ (Fin (n + 1))
  have hsspan :
      affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) =
        affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) :=
    Geometry.SimplicialComplex.affineSpan_eq_affineSpan_stdSimplex_of_mem_faces_card
      (K := K) hspace hs hscard
  have htspan :
      affineSpan ℝ (t : Set (Fin (n + 1) → ℝ)) =
        affineSpan ℝ K.space :=
    Geometry.SimplicialComplex.affineSpan_eq_affineSpan_space_of_mem_facets
      (K := K) hK hconv htFacet
  have htspan_s :
      affineSpan ℝ (t : Set (Fin (n + 1) → ℝ)) =
        affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) := by
    calc
      affineSpan ℝ (t : Set (Fin (n + 1) → ℝ)) =
          affineSpan ℝ K.space := htspan
      _ = affineSpan ℝ (stdSimplex ℝ (Fin (n + 1))) := by
        rw [hspace]
      _ = affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) :=
        hsspan.symm
  have htsub :
      (t : Set (Fin (n + 1) → ℝ)) ⊆
        affineSpan ℝ (s : Set (Fin (n + 1) → ℝ)) := by
    rw [← htspan_s]
    exact subset_affineSpan ℝ (t : Set (Fin (n + 1) → ℝ))
  have hcardle : #t ≤ #s :=
    (K.indep htFaces).card_le_card_of_subset_affineSpan htsub
  have hstEq : s = t :=
    Finset.eq_of_subset_of_card_le hst hcardle
  rw [hstEq]
  exact htFacet

variable [NeZero n]

/--
A codimension-one face of a finite triangulation of the standard `n`-simplex has
at most two top-dimensional cofaces.
-/
theorem card_cofaceApices_le_two_stdSimplex
    (hK : K.faces.Finite)
    (hspace : K.space = stdSimplex ℝ (Fin (n + 1)))
    {F : Finset (Fin (n + 1) → ℝ)} (hFcard : #F = n) :
    #(K.cofaceApices hK F) ≤ 2 := by
  have hconv : Convex ℝ K.space := by
    rw [hspace]
    exact convex_stdSimplex ℝ (Fin (n + 1))
  refine
    Geometry.SimplicialComplex.card_cofaceApices_le_two
      (K := K) (n := n) hK hconv hFcard ?_
  intro a ha
  obtain ⟨haF, haFace⟩ :=
    (Geometry.SimplicialComplex.mem_cofaceApices_iff
      (K := K) hK).1 ha
  have hfacet_of_insert_like :
      ∀ t : Finset (Fin (n + 1) → ℝ),
        t ∈ K.faces →
        (∀ x, x ∈ t ↔ x = a ∨ x ∈ F) →
        t ∈ K.facets := by
    intro t htFace htMem
    have htEq : t = insert a F := by
      ext x
      rw [htMem]
      simp
    apply
      Geometry.SimplicialComplex.mem_facets_of_mem_faces_card_eq
        (K := K) hK hspace htFace
    rw [htEq, Finset.card_insert_of_notMem haF, hFcard]
  have hfacet := hfacet_of_insert_like _ haFace (by
    intro x
    simp)
  convert hfacet using 1
  ext x
  simp

end Geometry.SimplicialComplex
