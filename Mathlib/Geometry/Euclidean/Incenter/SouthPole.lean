/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Incenter.Basic
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
# South and north poles of simplices.

This file defines the south and (generalized) north poles of a simplex, with respect to a vertex
of that simplex: the second intersection with the circumsphere of a line through that vertex and
the incenter or an excenter.

## Main definitions

* `Affine.Simplex.nsPole` for the second intersection with the circumsphere of a line through
  a vertex and the excenter with the given set of indices
* `Affine.Simplex.southPole` for the second intersection with the circumsphere of a line through
  a vertex and the incenter
* `Affine.Triangle.northPole` for the second intersection with the circumsphere of a line through
  a vertex and an excenter other than the one opposite that vertex

## References

* Paul Averous, [Problèmes du Club de Maths](https://doi.org/10.13140/RG.2.2.18317.10726)

-/

@[expose] public noncomputable section


open EuclideanGeometry
open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

namespace Affine

namespace Simplex

variable {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)

/-- The generalized north pole of a simplex with respect to a given vertex and excenter is the
second intersection with the circumsphere of the line through that vertex and excenter. -/
def nsPole (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : P :=
  s.circumsphere.secondInter (s.points i) (s.excenter signs -ᵥ s.points i)

lemma nsPole_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).nsPole signs i = s.nsPole (signs.map e.symm) (e.symm i) := by
  simp [nsPole, excenter_reindex]

variable {s} in
@[simp] lemma ExcenterExists.nsPole_map {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
    (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).nsPole signs i = f (s.nsPole signs i) := by
  simp only [nsPole, map_points, AffineIsometry.coe_toAffineMap, Function.comp_apply,
    h.excenter_map, ← Sphere.secondInter_map, ← AffineIsometry.map_vsub]
  convert rfl <;> simp

variable {s} in
@[simp] lemma ExcenterExists.nsPole_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).nsPole signs i = s.nsPole signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.nsPole_map S.subtypeₐᵢ i).symm

/-- The south pole of a simplex with respect to a given vertex is the second intersection with the
circumsphere of the line through that vertex and the incenter. -/
def southPole (i : Fin (n + 1)) : P :=
  s.circumsphere.secondInter (s.points i) (s.incenter -ᵥ s.points i)

lemma southPole_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (i : Fin (m + 1)) :
    (s.reindex e).southPole i = s.southPole (e.symm i) :=
  s.nsPole_reindex _ _ _

@[simp] lemma southPole_map (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).southPole i = f (s.southPole i) :=
  s.excenterExists_empty.nsPole_map _ _

@[simp] lemma southPole_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).southPole i = s.southPole i :=
  s.excenterExists_empty.nsPole_restrict S hS i

@[simp] lemma nsPole_empty (i : Fin (n + 1)) : s.nsPole ∅ i = s.southPole i :=
  rfl

@[simp] lemma nsPole_compl (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.nsPole signsᶜ i = s.nsPole signs i := by
  simp [nsPole]

variable {s} in
@[simp] lemma ExcenterExists.nsPole_insert {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} (hi : s.ExcenterExists (insert i signs)) :
    s.nsPole (insert i signs) i = s.nsPole signs i := by
  by_cases hs : i ∈ signs
  · simp [hs]
  simp_rw [nsPole]
  let r := (∑ j, s.excenterWeightsUnnorm signs j) / ∑ j, s.excenterWeightsUnnorm (insert i signs) j
  have hr : r ≠ 0 := div_ne_zero h hi
  convert Sphere.secondInter_smul _ _ _ hr
  simp_rw [excenter_eq_affineCombination,
    ← Finset.univ.affineCombination_piSingle ℝ s.points (Finset.mem_univ i),
    Finset.affineCombination_vsub, ← Finset.univ.weightedVSub_const_smul, r, excenterWeights]
  congr
  ext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · have hk' : s.excenterWeightsUnnorm (insert i signs) i = -(s.excenterWeightsUnnorm signs i) := by
      simp [excenterWeightsUnnorm, hs]
    rw [ExcenterExists] at h hi
    simp only [hk, hk', mul_neg, Pi.single_eq_same]
    have hu : ∑ j, s.excenterWeightsUnnorm (insert i signs) j =
        (∑ j, s.excenterWeightsUnnorm signs j) - 2 * s.excenterWeightsUnnorm signs i := by
      simp_rw [← Finset.sum_compl_add_sum {i}, Finset.sum_singleton, hk', add_sub_assoc]
      congr 1
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        simp_all [excenterWeightsUnnorm]
      · ring
    rw [hu] at hi ⊢
    field
  · have hk' : s.excenterWeightsUnnorm (insert i signs) k = s.excenterWeightsUnnorm signs k := by
      simp [excenterWeightsUnnorm, hk]
    rw [ExcenterExists] at h
    simp only [ne_eq, hk, not_false_eq_true, Pi.single_eq_of_ne, hk']
    field

variable {s} in
@[simp] lemma ExcenterExists.nsPole_erase {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} (hi : s.ExcenterExists (signs.erase i)) :
    s.nsPole (signs.erase i) i = s.nsPole signs i := by
  by_cases hs : i ∈ signs
  · rw [← Finset.insert_erase hs] at h
    nth_rw 2 [← Finset.insert_erase hs]
    exact (hi.nsPole_insert h).symm
  · simp [hs]

@[simp] lemma nsPole_singleton_self [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.nsPole {i} i = s.southPole i := by
  rw [← Finset.insert_empty, ← nsPole_empty, s.excenterExists_empty.nsPole_insert]
  rw [Finset.insert_empty]
  exact s.excenterExists_singleton _

lemma nsPole_mem_affineSpan_pair (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.nsPole signs i ∈ line[ℝ, s.points i, s.excenter signs] :=
  Sphere.secondInter_vsub_mem_affineSpan _ _ _

lemma southPole_mem_affineSpan_pair (i : Fin (n + 1)) :
    s.southPole i ∈ line[ℝ, s.points i, s.incenter] :=
  s.nsPole_mem_affineSpan_pair _ _

variable {s} in
lemma ExcenterExists.nsPole_mem_affineSpan_range {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.nsPole signs i ∈ affineSpan ℝ (Set.range s.points) :=
  IsConcreteLE.le_iff.1 (affineSpan_pair_le_of_mem_of_mem (mem_affineSpan _ (by simp))
    h.excenter_mem_affineSpan_range) (s.nsPole_mem_affineSpan_pair _ _)

lemma southPole_mem_affineSpan_range (i : Fin (n + 1)) :
    s.southPole i ∈ affineSpan ℝ (Set.range s.points) :=
  s.excenterExists_empty.nsPole_mem_affineSpan_range _

lemma nsPole_mem_circumsphere (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.nsPole signs i ∈ s.circumsphere := by
  simp [nsPole, mem_circumsphere]

lemma southPole_mem_circumsphere (i : Fin (n + 1)) : s.southPole i ∈ s.circumsphere :=
  s.nsPole_mem_circumsphere _ _

end Simplex

namespace Triangle

open Simplex

variable (t : Triangle ℝ P)

lemma nsPole_singleton_of_ne {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) :
    t.nsPole {i₂} i₁ = t.nsPole {i₃} i₁ := by
  by_cases h₂₃ : i₂ = i₃
  · rw [h₂₃]
  have h : ({i₃} : Finset (Fin 3)) = {i₁, i₂}ᶜ := by decide +revert
  rw [h, nsPole_compl, (t.excenterExists _).nsPole_insert (t.excenterExists _)]

/-- The north pole of a triangle with respect to a given vertex is the second intersection with the
circumsphere of the line through that vertex and an excenter other than the one opposite that
vertex. -/
def northPole (i : Fin 3) : P := t.nsPole {i + 1} i

lemma nsPole_singleton_eq_northPole {i j : Fin 3} (h : i ≠ j) :
    t.nsPole {j} i = t.northPole i := by
  rw [northPole]
  exact t.nsPole_singleton_of_ne h (by simp)

lemma northPole_reindex (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    northPole (t.reindex e) i = t.northPole (e.symm i) := by
  rw [northPole, nsPole_reindex]
  exact t.nsPole_singleton_eq_northPole (by simp)

@[simp] lemma northPole_map (f : P →ᵃⁱ[ℝ] P₂) (i : Fin 3) :
    northPole (t.map f.toAffineMap f.injective) i = f (t.northPole i) :=
  (t.excenterExists _).nsPole_map _ _

@[simp] lemma northPole_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range t.points) ≤ S) (i : Fin 3) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    northPole (t.restrict S hS) i = t.northPole i :=
  (t.excenterExists _).nsPole_restrict S hS i

lemma northPole_mem_affineSpan_pair {i j : Fin 3} (h : i ≠ j) :
    t.northPole i ∈ line[ℝ, t.points i, t.excenter {j}] := by
  rw [← t.nsPole_singleton_eq_northPole h]
  exact t.nsPole_mem_affineSpan_pair _ _

lemma northPole_mem_affineSpan_range (i : Fin 3) :
    t.northPole i ∈ affineSpan ℝ (Set.range t.points) :=
  (t.excenterExists _).nsPole_mem_affineSpan_range _

lemma northPole_mem_circumsphere (i : Fin 3) : t.northPole i ∈ t.circumsphere :=
  t.nsPole_mem_circumsphere _ _

end Triangle

end Affine
