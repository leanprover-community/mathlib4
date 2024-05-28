/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.DeriveFintype

#align_import geometry.euclidean.circumcenter from "leanprover-community/mathlib"@"2de9c37fa71dde2f1c6feff19876dd6a7b1519f0"

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/


noncomputable section

open scoped Classical

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineSubspace

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonalProjection` is. -/
theorem dist_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {p1 p2 : P} (p3 : P) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
    dist p1 p3 = dist p2 p3 ↔
      dist p1 (orthogonalProjection s p3) = dist p2 (orthogonalProjection s p3) := by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, ←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p3 hp1,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p3 hp2]
  simp
#align euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonalProjection` is. -/
theorem dist_set_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (Set.Pairwise ps fun p1 p2 => dist p1 p = dist p2 p) ↔
      Set.Pairwise ps fun p1 p2 =>
        dist p1 (orthogonalProjection s p) = dist p2 (orthogonalProjection s p) :=
  ⟨fun h _ hp1 _ hp2 hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp1) (hps hp2)).1 (h hp1 hp2 hne),
    fun h _ hp1 _ hp2 hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp1) (hps hp2)).2 (h hp1 hp2 hne)⟩
#align euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq EuclideanGeometry.dist_set_eq_iff_dist_orthogonalProjection_eq

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonalProjection` has that distance
from all the points in that set. -/
theorem exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [HasOrthogonalProjection s.direction] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (∃ r, ∀ p1 ∈ ps, dist p1 p = r) ↔ ∃ r, ∀ p1 ∈ ps, dist p1 ↑(orthogonalProjection s p) = r := by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h
#align euclidean_geometry.exists_dist_eq_iff_exists_dist_orthogonal_projection_eq EuclideanGeometry.exists_dist_eq_iff_exists_dist_orthogonalProjection_eq

/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
theorem existsUnique_dist_eq_of_insert {s : AffineSubspace ℝ P}
    [HasOrthogonalProjection s.direction] {ps : Set P} (hnps : ps.Nonempty) {p : P} (hps : ps ⊆ s)
    (hp : p ∉ s) (hu : ∃! cs : Sphere P, cs.center ∈ s ∧ ps ⊆ (cs : Set P)) :
    ∃! cs₂ : Sphere P,
      cs₂.center ∈ affineSpan ℝ (insert p (s : Set P)) ∧ insert p ps ⊆ (cs₂ : Set P) := by
  haveI : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y ≠ 0 := dist_orthogonalProjection_ne_zero_of_not_mem hp
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y)
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonalProjection s p : V) +ᵥ cc
  let cr₂ := √(cr * cr + ycc₂ * ycc₂)
  use ⟨cc₂, cr₂⟩
  simp (config := { zeta := false, proj := false }) only
  have hpo : p = (1 : ℝ) • (p -ᵥ orthogonalProjection s p : V) +ᵥ (orthogonalProjection s p : P) :=
    by simp
  constructor
  · constructor
    · refine vadd_mem_of_mem_direction ?_ (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hcc))
      rw [direction_affineSpan]
      exact
        Submodule.smul_mem _ _
          (vsub_mem_vectorSpan ℝ (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ (orthogonalProjection_mem _)))
    · intro p1 hp1
      rw [Sphere.mem_coe, mem_sphere, ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
      cases' hp1 with hp1 hp1
      · rw [hp1]
        rw [hpo,
          dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc _ _
            (vsub_orthogonalProjection_mem_direction_orthogonal s p),
          ← dist_eq_norm_vsub V p, dist_comm _ cc]
        field_simp [ycc₂, hy0]
        ring
      · rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp1),
          orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc, Subtype.coe_mk,
          dist_of_mem_subset_mk_sphere hp1 hcr, dist_eq_norm_vsub V cc₂ cc, vadd_vsub, norm_smul, ←
          dist_eq_norm_vsub V, Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg,
          div_mul_cancel₀ _ hy0, abs_mul_abs_self]
  · rintro ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩
    simp only at hcc₃ hcr₃
    obtain ⟨t₃, cc₃', hcc₃', hcc₃''⟩ :
      ∃ r : ℝ, ∃ p0 ∈ s, cc₃ = r • (p -ᵥ ↑((orthogonalProjection s) p)) +ᵥ p0 := by
      rwa [mem_affineSpan_insert_iff (orthogonalProjection_mem p)] at hcc₃
    have hcr₃' : ∃ r, ∀ p1 ∈ ps, dist p1 cc₃ = r :=
      ⟨cr₃, fun p1 hp1 => dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp1) hcr₃⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq hps cc₃, hcc₃'',
      orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃'] at hcr₃'
    cases' hcr₃' with cr₃' hcr₃'
    have hu := hcccru ⟨cc₃', cr₃'⟩
    simp only at hu
    replace hu := hu ⟨hcc₃', hcr₃'⟩
    -- Porting note: was
    -- cases' hu with hucc hucr
    -- substs hucc hucr
    cases' hu
    have hcr₃val : cr₃ = √(cr * cr + t₃ * y * (t₃ * y)) := by
      cases' hnps with p0 hp0
      have h' : ↑(⟨cc, hcc₃'⟩ : s) = cc := rfl
      rw [← dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp0) hcr₃, hcc₃'', ←
        mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
        dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp0),
        orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃', h',
        dist_of_mem_subset_mk_sphere hp0 hcr, dist_eq_norm_vsub V _ cc, vadd_vsub, norm_smul, ←
        dist_eq_norm_vsub V p, Real.norm_eq_abs, ← mul_assoc, mul_comm _ |t₃|, ← mul_assoc,
        abs_mul_abs_self]
      ring
    replace hcr₃ := dist_of_mem_subset_mk_sphere (Set.mem_insert _ _) hcr₃
    rw [hpo, hcc₃'', hcr₃val, ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
      dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc₃' _ _
        (vsub_orthogonalProjection_mem_direction_orthogonal s p),
      dist_comm, ← dist_eq_norm_vsub V p,
      Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at hcr₃
    change x * x + _ * (y * y) = _ at hcr₃
    rw [show
        x * x + (1 - t₃) * (1 - t₃) * (y * y) = x * x + y * y - 2 * y * (t₃ * y) + t₃ * y * (t₃ * y)
        by ring,
      add_left_inj] at hcr₃
    have ht₃ : t₃ = ycc₂ / y := by field_simp [ycc₂, ← hcr₃, hy0]
    subst ht₃
    change cc₃ = cc₂ at hcc₃''
    congr
    rw [hcr₃val]
    congr 2
    field_simp [hy0]
#align euclidean_geometry.exists_unique_dist_eq_of_insert EuclideanGeometry.existsUnique_dist_eq_of_insert

/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
theorem _root_.AffineIndependent.existsUnique_dist_eq {ι : Type*} [hne : Nonempty ι] [Finite ι]
    {p : ι → P} (ha : AffineIndependent ℝ p) :
    ∃! cs : Sphere P, cs.center ∈ affineSpan ℝ (Set.range p) ∧ Set.range p ⊆ (cs : Set P) := by
  cases nonempty_fintype ι
  induction' hn : Fintype.card ι with m hm generalizing ι
  · exfalso
    have h := Fintype.card_pos_iff.2 hne
    rw [hn] at h
    exact lt_irrefl 0 h
  · cases' m with m
    · rw [Fintype.card_eq_one_iff] at hn
      cases' hn with i hi
      haveI : Unique ι := ⟨⟨i⟩, hi⟩
      use ⟨p i, 0⟩
      simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton]
      constructor
      · simp_rw [hi default, Set.singleton_subset_iff]
        exact ⟨⟨⟩, by simp only [Metric.sphere_zero, Set.mem_singleton_iff]⟩
      · rintro ⟨cc, cr⟩
        simp only
        rintro ⟨rfl, hdist⟩
        simp? [Set.singleton_subset_iff] at hdist says
          simp only [Set.singleton_subset_iff, Metric.mem_sphere, dist_self] at hdist
        rw [hi default, hdist]
    · have i := hne.some
      let ι2 := { x // x ≠ i }
      have hc : Fintype.card ι2 = m + 1 := by
        rw [Fintype.card_of_subtype (Finset.univ.filter fun x => x ≠ i)]
        · rw [Finset.filter_not]
          -- Porting note: removed `simp_rw [eq_comm]` and used `filter_eq'` instead of `filter_eq`
          rw [Finset.filter_eq' _ i, if_pos (Finset.mem_univ _),
            Finset.card_sdiff (Finset.subset_univ _), Finset.card_singleton, Finset.card_univ, hn]
          simp
        · simp
      haveI : Nonempty ι2 := Fintype.card_pos_iff.1 (hc.symm ▸ Nat.zero_lt_succ _)
      have ha2 : AffineIndependent ℝ fun i2 : ι2 => p i2 := ha.subtype _
      replace hm := hm ha2 _ hc
      have hr : Set.range p = insert (p i) (Set.range fun i2 : ι2 => p i2) := by
        change _ = insert _ (Set.range fun i2 : { x | x ≠ i } => p i2)
        rw [← Set.image_eq_range, ← Set.image_univ, ← Set.image_insert_eq]
        congr with j
        simp [Classical.em]
      rw [hr, ← affineSpan_insert_affineSpan]
      refine existsUnique_dist_eq_of_insert (Set.range_nonempty _) (subset_spanPoints ℝ _) ?_ hm
      convert ha.not_mem_affineSpan_diff i Set.univ
      change (Set.range fun i2 : { x | x ≠ i } => p i2) = _
      rw [← Set.image_eq_range]
      congr with j
      simp
#align affine_independent.exists_unique_dist_eq AffineIndependent.existsUnique_dist_eq

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The circumsphere of a simplex. -/
def circumsphere {n : ℕ} (s : Simplex ℝ P n) : Sphere P :=
  s.independent.existsUnique_dist_eq.choose
#align affine.simplex.circumsphere Affine.Simplex.circumsphere

/-- The property satisfied by the circumsphere. -/
theorem circumsphere_unique_dist_eq {n : ℕ} (s : Simplex ℝ P n) :
    (s.circumsphere.center ∈ affineSpan ℝ (Set.range s.points) ∧
        Set.range s.points ⊆ s.circumsphere) ∧
      ∀ cs : Sphere P,
        cs.center ∈ affineSpan ℝ (Set.range s.points) ∧ Set.range s.points ⊆ cs →
          cs = s.circumsphere :=
  s.independent.existsUnique_dist_eq.choose_spec
#align affine.simplex.circumsphere_unique_dist_eq Affine.Simplex.circumsphere_unique_dist_eq

/-- The circumcenter of a simplex. -/
def circumcenter {n : ℕ} (s : Simplex ℝ P n) : P :=
  s.circumsphere.center
#align affine.simplex.circumcenter Affine.Simplex.circumcenter

/-- The circumradius of a simplex. -/
def circumradius {n : ℕ} (s : Simplex ℝ P n) : ℝ :=
  s.circumsphere.radius
#align affine.simplex.circumradius Affine.Simplex.circumradius

/-- The center of the circumsphere is the circumcenter. -/
@[simp]
theorem circumsphere_center {n : ℕ} (s : Simplex ℝ P n) : s.circumsphere.center = s.circumcenter :=
  rfl
#align affine.simplex.circumsphere_center Affine.Simplex.circumsphere_center

/-- The radius of the circumsphere is the circumradius. -/
@[simp]
theorem circumsphere_radius {n : ℕ} (s : Simplex ℝ P n) : s.circumsphere.radius = s.circumradius :=
  rfl
#align affine.simplex.circumsphere_radius Affine.Simplex.circumsphere_radius

/-- The circumcenter lies in the affine span. -/
theorem circumcenter_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.circumcenter ∈ affineSpan ℝ (Set.range s.points) :=
  s.circumsphere_unique_dist_eq.1.1
#align affine.simplex.circumcenter_mem_affine_span Affine.Simplex.circumcenter_mem_affineSpan

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    dist (s.points i) s.circumcenter = s.circumradius :=
  dist_of_mem_subset_sphere (Set.mem_range_self _) s.circumsphere_unique_dist_eq.1.2
#align affine.simplex.dist_circumcenter_eq_circumradius Affine.Simplex.dist_circumcenter_eq_circumradius

/-- All points lie in the circumsphere. -/
theorem mem_circumsphere {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ∈ s.circumsphere :=
  s.dist_circumcenter_eq_circumradius i
#align affine.simplex.mem_circumsphere Affine.Simplex.mem_circumsphere

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius' {n : ℕ} (s : Simplex ℝ P n) :
    ∀ i, dist s.circumcenter (s.points i) = s.circumradius := by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _
#align affine.simplex.dist_circumcenter_eq_circumradius' Affine.Simplex.dist_circumcenter_eq_circumradius'

/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
theorem eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
    p = s.circumcenter := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, eq_self_iff_true, subset_sphere, Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  -- Porting note: added the next three lines (`simp` less powerful)
  rw [subset_sphere (s := ⟨p, r⟩)] at h
  simp only [hp, hr, forall_const, eq_self_iff_true, subset_sphere, Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.1
#align affine.simplex.eq_circumcenter_of_dist_eq Affine.Simplex.eq_circumcenter_of_dist_eq

/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
theorem eq_circumradius_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
    r = s.circumradius := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, eq_self_iff_true, subset_sphere, Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and_iff] at h
  -- Porting note: added the next three lines (`simp` less powerful)
  rw [subset_sphere (s := ⟨p, r⟩)] at h
  simp only [hp, hr, forall_const, eq_self_iff_true, subset_sphere, Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and_iff] at h
  exact h.2
#align affine.simplex.eq_circumradius_of_dist_eq Affine.Simplex.eq_circumradius_of_dist_eq

/-- The circumradius is non-negative. -/
theorem circumradius_nonneg {n : ℕ} (s : Simplex ℝ P n) : 0 ≤ s.circumradius :=
  s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg
#align affine.simplex.circumradius_nonneg Affine.Simplex.circumradius_nonneg

/-- The circumradius of a simplex with at least two points is
positive. -/
theorem circumradius_pos {n : ℕ} (s : Simplex ℝ P (n + 1)) : 0 < s.circumradius := by
  refine lt_of_le_of_ne s.circumradius_nonneg ?_
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 := s.independent.injective.ne (by simp : (0 : Fin (n + 2)) ≠ 1)
  simp [hr] at h01
#align affine.simplex.circumradius_pos Affine.Simplex.circumradius_pos

/-- The circumcenter of a 0-simplex equals its unique point. -/
theorem circumcenter_eq_point (s : Simplex ℝ P 0) (i : Fin 1) : s.circumcenter = s.points i := by
  have h := s.circumcenter_mem_affineSpan
  have : Unique (Fin 1) := ⟨⟨0, by decide⟩, fun a => by simp only [Fin.eq_zero]⟩
  simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton] at h
  rw [h]
  congr
  simp only [eq_iff_true_of_subsingleton]
#align affine.simplex.circumcenter_eq_point Affine.Simplex.circumcenter_eq_point

/-- The circumcenter of a 1-simplex equals its centroid. -/
theorem circumcenter_eq_centroid (s : Simplex ℝ P 1) :
    s.circumcenter = Finset.univ.centroid ℝ s.points := by
  have hr :
    Set.Pairwise Set.univ fun i j : Fin 2 =>
      dist (s.points i) (Finset.univ.centroid ℝ s.points) =
        dist (s.points j) (Finset.univ.centroid ℝ s.points) := by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin, dist_eq_norm_vsub V (s.points i),
      dist_eq_norm_vsub V (s.points j), vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, ←
      one_smul ℝ (s.points i -ᵥ s.points 0), ← one_smul ℝ (s.points j -ᵥ s.points 0)]
    fin_cases i <;> fin_cases j <;> simp [-one_smul, ← sub_smul] <;> norm_num
  rw [Set.pairwise_eq_iff_exists_eq] at hr
  cases' hr with r hr
  exact
    (s.eq_circumcenter_of_dist_eq
        (centroid_mem_affineSpan_of_card_eq_add_one ℝ _ (Finset.card_fin 2)) fun i =>
        hr i (Set.mem_univ _)).symm
#align affine.simplex.circumcenter_eq_centroid Affine.Simplex.circumcenter_eq_centroid

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumsphere. -/
@[simp]
theorem circumsphere_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumsphere = s.circumsphere := by
  refine s.circumsphere_unique_dist_eq.2 _ ⟨?_, ?_⟩ <;> rw [← s.reindex_range_points e]
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.1
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.2
#align affine.simplex.circumsphere_reindex Affine.Simplex.circumsphere_reindex

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumcenter. -/
@[simp]
theorem circumcenter_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumcenter = s.circumcenter := by simp_rw [circumcenter, circumsphere_reindex]
#align affine.simplex.circumcenter_reindex Affine.Simplex.circumcenter_reindex

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumradius. -/
@[simp]
theorem circumradius_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumradius = s.circumradius := by simp_rw [circumradius, circumsphere_reindex]
#align affine.simplex.circumradius_reindex Affine.Simplex.circumradius_reindex

attribute [local instance] AffineSubspace.toAddTorsor

/-- The orthogonal projection of a point `p` onto the hyperplane spanned by the simplex's points. -/
def orthogonalProjectionSpan {n : ℕ} (s : Simplex ℝ P n) :
    P →ᵃ[ℝ] affineSpan ℝ (Set.range s.points) :=
  orthogonalProjection (affineSpan ℝ (Set.range s.points))
#align affine.simplex.orthogonal_projection_span Affine.Simplex.orthogonalProjectionSpan

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} (s : Simplex ℝ P n)
    {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ affineSpan ℝ (Set.range s.points)) :
    s.orthogonalProjectionSpan (r • (p2 -ᵥ s.orthogonalProjectionSpan p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
  EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _
#align affine.simplex.orthogonal_projection_vadd_smul_vsub_orthogonal_projection Affine.Simplex.orthogonalProjection_vadd_smul_vsub_orthogonalProjection

theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} {r₁ : ℝ}
    (s : Simplex ℝ P n) {p p₁o : P} (hp₁o : p₁o ∈ affineSpan ℝ (Set.range s.points)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congrArg ((↑) : _ → P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)
#align affine.simplex.coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection Affine.Simplex.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection

theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {n : ℕ}
    (s : Simplex ℝ P n) {p1 : P} (p2 : P) (hp1 : p1 ∈ affineSpan ℝ (Set.range s.points)) :
    dist p1 p2 * dist p1 p2 =
      dist p1 (s.orthogonalProjectionSpan p2) * dist p1 (s.orthogonalProjectionSpan p2) +
        dist p2 (s.orthogonalProjectionSpan p2) * dist p2 (s.orthogonalProjectionSpan p2) := by
  rw [PseudoMetricSpace.dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _,
    dist_eq_norm_vsub V _ p2, ← vsub_add_vsub_cancel p1 (s.orthogonalProjectionSpan p2) p2,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p2 hp1)
      (orthogonalProjection_vsub_mem_direction_orthogonal _ p2)
#align affine.simplex.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq Affine.Simplex.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq

theorem dist_circumcenter_sq_eq_sq_sub_circumradius {n : ℕ} {r : ℝ} (s : Simplex ℝ P n) {p₁ : P}
    (h₁ : ∀ i : Fin (n + 1), dist (s.points i) p₁ = r)
    (h₁' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter)
    (h : s.points 0 ∈ affineSpan ℝ (Set.range s.points)) :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius := by
  rw [dist_comm, ← h₁ 0,
    s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel_left, Simplex.dist_circumcenter_eq_circumradius]
#align affine.simplex.dist_circumcenter_sq_eq_sq_sub_circumradius Affine.Simplex.dist_circumcenter_sq_eq_sq_sub_circumradius

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  -/
theorem orthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hr : ∃ r, ∀ i, dist (s.points i) p = r) :
    ↑(s.orthogonalProjectionSpan p) = s.circumcenter := by
  change ∃ r : ℝ, ∀ i, (fun x => dist x p = r) (s.points i) at hr
  have hr : ∃ (r : ℝ), ∀ (a : P),
      a ∈ Set.range (fun (i : Fin (n + 1)) => s.points i) → dist a p = r := by
    cases' hr with r hr
    use r
    refine Set.forall_mem_range.mpr ?_
    exact hr
  rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq (subset_affineSpan ℝ _) p] at hr
  cases' hr with r hr
  exact
    s.eq_circumcenter_of_dist_eq (orthogonalProjection_mem p) fun i => hr _ (Set.mem_range_self i)
#align affine.simplex.orthogonal_projection_eq_circumcenter_of_exists_dist_eq Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  -/
theorem orthogonalProjection_eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P} {r : ℝ}
    (hr : ∀ i, dist (s.points i) p = r) : ↑(s.orthogonalProjectionSpan p) = s.circumcenter :=
  s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩
#align affine.simplex.orthogonal_projection_eq_circumcenter_of_dist_eq Affine.Simplex.orthogonalProjection_eq_circumcenter_of_dist_eq

/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
theorem orthogonalProjection_circumcenter {n : ℕ} (s : Simplex ℝ P n) {fs : Finset (Fin (n + 1))}
    {m : ℕ} (h : fs.card = m + 1) :
    ↑((s.face h).orthogonalProjectionSpan s.circumcenter) = (s.face h).circumcenter :=
  haveI hr : ∃ r, ∀ i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  orthogonalProjection_eq_circumcenter_of_exists_dist_eq _ hr
#align affine.simplex.orthogonal_projection_circumcenter Affine.Simplex.orthogonalProjection_circumcenter

/-- Two simplices with the same points have the same circumcenter. -/
theorem circumcenter_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex ℝ P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.circumcenter = s₂.circumcenter := by
  have hs : s₁.circumcenter ∈ affineSpan ℝ (Set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affineSpan
  have hr : ∀ i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i ∈ Set.range s₂.points := Set.mem_range_self _
    rw [← h, Set.mem_range] at hi
    rcases hi with ⟨j, hj⟩
    rw [← hj, s₁.dist_circumcenter_eq_circumradius j]
  exact s₂.eq_circumcenter_of_dist_eq hs hr
#align affine.simplex.circumcenter_eq_of_range_eq Affine.Simplex.circumcenter_eq_of_range_eq

/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
inductive PointsWithCircumcenterIndex (n : ℕ)
  | pointIndex : Fin (n + 1) → PointsWithCircumcenterIndex n
  | circumcenterIndex : PointsWithCircumcenterIndex n
  deriving Fintype
#align affine.simplex.points_with_circumcenter_index Affine.Simplex.PointsWithCircumcenterIndex

open PointsWithCircumcenterIndex

instance pointsWithCircumcenterIndexInhabited (n : ℕ) : Inhabited (PointsWithCircumcenterIndex n) :=
  ⟨circumcenterIndex⟩
#align affine.simplex.points_with_circumcenter_index_inhabited Affine.Simplex.pointsWithCircumcenterIndexInhabited

/-- `pointIndex` as an embedding. -/
def pointIndexEmbedding (n : ℕ) : Fin (n + 1) ↪ PointsWithCircumcenterIndex n :=
  ⟨fun i => pointIndex i, fun _ _ h => by injection h⟩
#align affine.simplex.point_index_embedding Affine.Simplex.pointIndexEmbedding

/-- The sum of a function over `PointsWithCircumcenterIndex`. -/
theorem sum_pointsWithCircumcenter {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : PointsWithCircumcenterIndex n → α) :
    ∑ i, f i = (∑ i : Fin (n + 1), f (pointIndex i)) + f circumcenterIndex := by
  have h : univ = insert circumcenterIndex (univ.map (pointIndexEmbedding n)) := by
    ext x
    refine ⟨fun h => ?_, fun _ => mem_univ _⟩
    cases' x with i
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
    · exact mem_insert_self _ _
  change _ = (∑ i, f (pointIndexEmbedding n i)) + _
  rw [add_comm, h, ← sum_map, sum_insert]
  simp_rw [Finset.mem_map, not_exists]
  rintro x ⟨_, h⟩
  injection h
#align affine.simplex.sum_points_with_circumcenter Affine.Simplex.sum_pointsWithCircumcenter

/-- The vertices of a simplex plus its circumcenter. -/
def pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n) : PointsWithCircumcenterIndex n → P
  | pointIndex i => s.points i
  | circumcenterIndex => s.circumcenter
#align affine.simplex.points_with_circumcenter Affine.Simplex.pointsWithCircumcenter

/-- `pointsWithCircumcenter`, applied to a `pointIndex` value,
equals `points` applied to that value. -/
@[simp]
theorem pointsWithCircumcenter_point {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.pointsWithCircumcenter (pointIndex i) = s.points i :=
  rfl
#align affine.simplex.points_with_circumcenter_point Affine.Simplex.pointsWithCircumcenter_point

/-- `pointsWithCircumcenter`, applied to `circumcenterIndex`, equals the
circumcenter. -/
@[simp]
theorem pointsWithCircumcenter_eq_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.pointsWithCircumcenter circumcenterIndex = s.circumcenter :=
  rfl
#align affine.simplex.points_with_circumcenter_eq_circumcenter Affine.Simplex.pointsWithCircumcenter_eq_circumcenter

/-- The weights for a single vertex of a simplex, in terms of
`pointsWithCircumcenter`. -/
def pointWeightsWithCircumcenter {n : ℕ} (i : Fin (n + 1)) : PointsWithCircumcenterIndex n → ℝ
  | pointIndex j => if j = i then 1 else 0
  | circumcenterIndex => 0
#align affine.simplex.point_weights_with_circumcenter Affine.Simplex.pointWeightsWithCircumcenter

/-- `point_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_pointWeightsWithCircumcenter {n : ℕ} (i : Fin (n + 1)) :
    ∑ j, pointWeightsWithCircumcenter i j = 1 := by
  convert sum_ite_eq' univ (pointIndex i) (Function.const _ (1 : ℝ)) with j
  · cases j <;> simp [pointWeightsWithCircumcenter]
  · simp
#align affine.simplex.sum_point_weights_with_circumcenter Affine.Simplex.sum_pointWeightsWithCircumcenter

/-- A single vertex, in terms of `pointsWithCircumcenter`. -/
theorem point_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.points i =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (pointWeightsWithCircumcenter i) := by
  rw [← pointsWithCircumcenter_point]
  symm
  refine
    affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by simp [pointWeightsWithCircumcenter]) ?_
  intro i hi hn
  cases i
  · have h : _ ≠ i := fun h => hn (h ▸ rfl)
    simp [pointWeightsWithCircumcenter, h]
  · rfl
#align affine.simplex.point_eq_affine_combination_of_points_with_circumcenter Affine.Simplex.point_eq_affineCombination_of_pointsWithCircumcenter

/-- The weights for the centroid of some vertices of a simplex, in
terms of `pointsWithCircumcenter`. -/
def centroidWeightsWithCircumcenter {n : ℕ} (fs : Finset (Fin (n + 1))) :
    PointsWithCircumcenterIndex n → ℝ
  | pointIndex i => if i ∈ fs then (card fs : ℝ)⁻¹ else 0
  | circumcenterIndex => 0
#align affine.simplex.centroid_weights_with_circumcenter Affine.Simplex.centroidWeightsWithCircumcenter

/-- `centroidWeightsWithCircumcenter` sums to 1, if the `Finset` is nonempty. -/
@[simp]
theorem sum_centroidWeightsWithCircumcenter {n : ℕ} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty) :
    ∑ i, centroidWeightsWithCircumcenter fs i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter, add_zero, ←
    fs.sum_centroidWeights_eq_one_of_nonempty ℝ h, ← sum_indicator_subset _ fs.subset_univ]
  rcongr
#align affine.simplex.sum_centroid_weights_with_circumcenter Affine.Simplex.sum_centroidWeightsWithCircumcenter

/-- The centroid of some vertices of a simplex, in terms of `pointsWithCircumcenter`. -/
theorem centroid_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n)
    (fs : Finset (Fin (n + 1))) :
    fs.centroid ℝ s.points =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (centroidWeightsWithCircumcenter fs) := by
  simp_rw [centroid_def, affineCombination_apply, weightedVSubOfPoint_apply,
    sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter,
    pointsWithCircumcenter_point, zero_smul, add_zero, centroidWeights,
    ← sum_indicator_subset_of_eq_zero (Function.const (Fin (n + 1)) (card fs : ℝ)⁻¹)
      (fun i wi => wi • (s.points i -ᵥ Classical.choice AddTorsor.nonempty)) fs.subset_univ fun _ =>
      zero_smul ℝ _,
    Set.indicator_apply]
  congr
#align affine.simplex.centroid_eq_affine_combination_of_points_with_circumcenter Affine.Simplex.centroid_eq_affineCombination_of_pointsWithCircumcenter

/-- The weights for the circumcenter of a simplex, in terms of `pointsWithCircumcenter`. -/
def circumcenterWeightsWithCircumcenter (n : ℕ) : PointsWithCircumcenterIndex n → ℝ
  | pointIndex _ => 0
  | circumcenterIndex => 1
#align affine.simplex.circumcenter_weights_with_circumcenter Affine.Simplex.circumcenterWeightsWithCircumcenter

/-- `circumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
theorem sum_circumcenterWeightsWithCircumcenter (n : ℕ) :
    ∑ i, circumcenterWeightsWithCircumcenter n i = 1 := by
  convert sum_ite_eq' univ circumcenterIndex (Function.const _ (1 : ℝ)) with j
  · cases j <;> simp [circumcenterWeightsWithCircumcenter]
  · simp
#align affine.simplex.sum_circumcenter_weights_with_circumcenter Affine.Simplex.sum_circumcenterWeightsWithCircumcenter

/-- The circumcenter of a simplex, in terms of `pointsWithCircumcenter`. -/
theorem circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (circumcenterWeightsWithCircumcenter n) := by
  rw [← pointsWithCircumcenter_eq_circumcenter]
  symm
  refine affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl ?_
  rintro ⟨i⟩ _ hn <;> tauto
#align affine.simplex.circumcenter_eq_affine_combination_of_points_with_circumcenter Affine.Simplex.circumcenter_eq_affineCombination_of_pointsWithCircumcenter

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
def reflectionCircumcenterWeightsWithCircumcenter {n : ℕ} (i₁ i₂ : Fin (n + 1)) :
    PointsWithCircumcenterIndex n → ℝ
  | pointIndex i => if i = i₁ ∨ i = i₂ then 1 else 0
  | circumcenterIndex => -1
#align affine.simplex.reflection_circumcenter_weights_with_circumcenter Affine.Simplex.reflectionCircumcenterWeightsWithCircumcenter

/-- `reflectionCircumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
theorem sum_reflectionCircumcenterWeightsWithCircumcenter {n : ℕ} {i₁ i₂ : Fin (n + 1)}
    (h : i₁ ≠ i₂) : ∑ i, reflectionCircumcenterWeightsWithCircumcenter i₁ i₂ i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, reflectionCircumcenterWeightsWithCircumcenter, sum_ite,
    sum_const, filter_or, filter_eq']
  rw [card_union_of_disjoint]
  · set_option simprocs false in simp
  · simpa only [if_true, mem_univ, disjoint_singleton] using h
#align affine.simplex.sum_reflection_circumcenter_weights_with_circumcenter Affine.Simplex.sum_reflectionCircumcenterWeightsWithCircumcenter

/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `pointsWithCircumcenter`. -/
theorem reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P n) {i₁ i₂ : Fin (n + 1)} (h : i₁ ≠ i₂) :
    reflection (affineSpan ℝ (s.points '' {i₁, i₂})) s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (reflectionCircumcenterWeightsWithCircumcenter i₁ i₂) := by
  have hc : card ({i₁, i₂} : Finset (Fin (n + 1))) = 2 := by simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace ℝ P := affineSpan ℝ (s.points '' {i₁, i₂})
  have h_faces :
    (orthogonalProjection W s.circumcenter : P) =
      ↑((s.face hc).orthogonalProjectionSpan s.circumcenter) := by
    apply eq_orthogonalProjection_of_eq_subspace
    simp
  rw [EuclideanGeometry.reflection_apply, h_faces, s.orthogonalProjection_circumcenter hc,
    circumcenter_eq_centroid, s.face_centroid_eq_centroid hc,
    centroid_eq_affineCombination_of_pointsWithCircumcenter,
    circumcenter_eq_affineCombination_of_pointsWithCircumcenter, ← @vsub_eq_zero_iff_eq V,
    affineCombination_vsub, weightedVSub_vadd_affineCombination, affineCombination_vsub,
    weightedVSub_apply, sum_pointsWithCircumcenter]
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.sub_apply, sub_smul, add_smul, sub_smul,
    centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter, ite_smul, zero_smul, sub_zero,
    apply_ite₂ (· + ·), add_zero, ← add_smul, hc, zero_sub, neg_smul, sub_self, add_zero]
  -- Porting note: was `convert sum_const_zero`
  rw [← sum_const_zero]
  congr
  norm_num
#align affine.simplex.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter Affine.Simplex.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter

end Simplex

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace FiniteDimensional

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace. -/
theorem cospherical_iff_exists_mem_of_complete {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] [HasOrthogonalProjection s.direction] :
    Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius := by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonalProjection_mem _, hcr⟩
  · exact fun ⟨c, _, hd⟩ => ⟨c, hd⟩
#align euclidean_geometry.cospherical_iff_exists_mem_of_complete EuclideanGeometry.cospherical_iff_exists_mem_of_complete

/-- Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace. -/
theorem cospherical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] [FiniteDimensional ℝ s.direction] :
    Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius :=
  cospherical_iff_exists_mem_of_complete h
#align euclidean_geometry.cospherical_iff_exists_mem_of_finite_dimensional EuclideanGeometry.cospherical_iff_exists_mem_of_finiteDimensional

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem exists_circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumradius = r := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (spanPoints_subset_coe_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumradius_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm
#align euclidean_geometry.exists_circumradius_eq_of_cospherical_subset EuclideanGeometry.exists_circumradius_eq_of_cospherical_subset

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumradius_eq_of_cospherical_subset EuclideanGeometry.circumradius_eq_of_cospherical_subset

/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem exists_circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumradius = r := by
  haveI : Nonempty (⊤ : AffineSubspace ℝ P) := Set.univ.nonempty
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumradius_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _
#align euclidean_geometry.exists_circumradius_eq_of_cospherical EuclideanGeometry.exists_circumradius_eq_of_cospherical

/-- Two n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumradius_eq_of_cospherical EuclideanGeometry.circumradius_eq_of_cospherical

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ c : P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumcenter = c := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (spanPoints_subset_coe_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumcenter_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm
#align euclidean_geometry.exists_circumcenter_eq_of_cospherical_subset EuclideanGeometry.exists_circumcenter_eq_of_cospherical_subset

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumcenter_eq_of_cospherical_subset EuclideanGeometry.circumcenter_eq_of_cospherical_subset

/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ c : P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumcenter = c := by
  haveI : Nonempty (⊤ : AffineSubspace ℝ P) := Set.univ.nonempty
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumcenter_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _
#align euclidean_geometry.exists_circumcenter_eq_of_cospherical EuclideanGeometry.exists_circumcenter_eq_of_cospherical

/-- Two n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumcenter_eq_of_cospherical EuclideanGeometry.circumcenter_eq_of_cospherical

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere. -/
theorem exists_circumsphere_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ c : Sphere P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumsphere = c := by
  obtain ⟨r, hr⟩ := exists_circumradius_eq_of_cospherical_subset h hd hc
  obtain ⟨c, hc⟩ := exists_circumcenter_eq_of_cospherical_subset h hd hc
  exact ⟨⟨c, r⟩, fun sx hsx => Sphere.ext _ _ (hc sx hsx) (hr sx hsx)⟩
#align euclidean_geometry.exists_circumsphere_eq_of_cospherical_subset EuclideanGeometry.exists_circumsphere_eq_of_cospherical_subset

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere. -/
theorem circumsphere_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumsphere_eq_of_cospherical_subset EuclideanGeometry.circumsphere_eq_of_cospherical_subset

/-- All n-simplices among cospherical points in n-space have the same
circumsphere. -/
theorem exists_circumsphere_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ c : Sphere P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumsphere = c := by
  haveI : Nonempty (⊤ : AffineSubspace ℝ P) := Set.univ.nonempty
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumsphere_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _
#align euclidean_geometry.exists_circumsphere_eq_of_cospherical EuclideanGeometry.exists_circumsphere_eq_of_cospherical

/-- Two n-simplices among cospherical points in n-space have the same
circumsphere. -/
theorem circumsphere_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
#align euclidean_geometry.circumsphere_eq_of_cospherical EuclideanGeometry.circumsphere_eq_of_cospherical

/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
theorem eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : Simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affineSpan ℝ (insert p (Set.range s.points)))
    (hp₂ : p₂ ∈ affineSpan ℝ (insert p (Set.range s.points))) (h₁ : ∀ i, dist (s.points i) p₁ = r)
    (h₂ : ∀ i, dist (s.points i) p₂ = r) :
    p₁ = p₂ ∨ p₁ = reflection (affineSpan ℝ (Set.range s.points)) p₂ := by
  set span_s := affineSpan ℝ (Set.range s.points)
  have h₁' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₂
  rw [← affineSpan_insert_affineSpan, mem_affineSpan_insert_iff (orthogonalProjection_mem p)]
    at hp₁ hp₂
  obtain ⟨r₁, p₁o, hp₁o, hp₁⟩ := hp₁
  obtain ⟨r₂, p₂o, hp₂o, hp₂⟩ := hp₂
  obtain rfl : ↑(s.orthogonalProjectionSpan p₁) = p₁o := by
    subst hp₁
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₁o
  rw [h₁'] at hp₁
  obtain rfl : ↑(s.orthogonalProjectionSpan p₂) = p₂o := by
    subst hp₂
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₂o
  rw [h₂'] at hp₂
  have h : s.points 0 ∈ span_s := mem_affineSpan ℝ (Set.mem_range_self _)
  have hd₁ :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₁ h₁' h
  have hd₂ :
    dist p₂ s.circumcenter * dist p₂ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₂ h₂' h
  rw [← hd₂, hp₁, hp₂, dist_eq_norm_vsub V _ s.circumcenter, dist_eq_norm_vsub V _ s.circumcenter,
    vadd_vsub, vadd_vsub, ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, ←
    mul_assoc, ← mul_assoc] at hd₁
  by_cases hp : p = s.orthogonalProjectionSpan p
  · rw [Simplex.orthogonalProjectionSpan] at hp
    rw [hp₁, hp₂, ← hp]
    simp only [true_or_iff, eq_self_iff_true, smul_zero, vsub_self]
  · have hz : ⟪p -ᵥ orthogonalProjection span_s p, p -ᵥ orthogonalProjection span_s p⟫ ≠ 0 := by
      simpa only [Ne, vsub_eq_zero_iff_eq, inner_self_eq_zero] using hp
    rw [mul_left_inj' hz, mul_self_eq_mul_self_iff] at hd₁
    rw [hp₁, hp₂]
    cases' hd₁ with hd₁ hd₁
    · left
      rw [hd₁]
    · right
      rw [hd₁, reflection_vadd_smul_vsub_orthogonalProjection p r₂ s.circumcenter_mem_affineSpan,
        neg_smul]
#align euclidean_geometry.eq_or_eq_reflection_of_dist_eq EuclideanGeometry.eq_or_eq_reflection_of_dist_eq

end EuclideanGeometry
