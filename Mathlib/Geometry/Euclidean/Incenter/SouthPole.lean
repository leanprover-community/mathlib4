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

* `Affine.Simplex.northPole` for the second intersection with the circumsphere of a line through
  a vertex and the excenter with the given set of indices
* `Affine.Simplex.southPole` for the second intersection with the circumsphere of a line through
  a vertex and the incenter

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

/-- The north pole of a simplex with respect to a given vertex and excenter is the second
intersection with the circumsphere of the line through that vertex and excenter. -/
def northPole (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : P :=
  s.circumsphere.secondInter (s.points i) (s.excenter signs -ᵥ s.points i)

lemma northPole_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).northPole signs i = s.northPole (signs.map e.symm) (e.symm i) := by
  simp [northPole, excenter_reindex]

variable {s} in
@[simp] lemma ExcenterExists.northPole_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).northPole signs i = f (s.northPole signs i) := by
  simp only [northPole, map_points, AffineIsometry.coe_toAffineMap, Function.comp_apply,
    h.excenter_map, ← Sphere.secondInter_map, ← AffineIsometry.map_vsub]
  convert rfl <;> simp

variable {s} in
@[simp] lemma ExcenterExists.northPole_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).northPole signs i = s.northPole signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.northPole_map S.subtypeₐᵢ i).symm

/-- The south pole of a simplex with respect to a given vertex is the second intersection with the
circumsphere of the line through that vertex and the incenter. -/
def southPole (i : Fin (n + 1)) : P :=
  s.circumsphere.secondInter (s.points i) (s.incenter -ᵥ s.points i)

lemma southPole_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (i : Fin (m + 1)) :
    (s.reindex e).southPole i = s.southPole (e.symm i) :=
  s.northPole_reindex _ _ _

@[simp] lemma southPole_map (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).southPole i = f (s.southPole i) :=
  s.excenterExists_empty.northPole_map _ _

@[simp] lemma southPole_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).southPole i = s.southPole i :=
  s.excenterExists_empty.northPole_restrict S hS i

@[simp] lemma northPole_empty (i : Fin (n + 1)) : s.northPole ∅ i = s.southPole i :=
  rfl

@[simp] lemma northPole_compl (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.northPole signsᶜ i = s.northPole signs i := by
  simp [northPole]

variable {s} in
@[simp] lemma ExcenterExists.northPole_insert {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} (hi : s.ExcenterExists (insert i signs)) :
    s.northPole (insert i signs) i = s.northPole signs i := by
  by_cases hs : i ∈ signs
  · simp [hs]
  simp_rw [northPole]
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
@[simp] lemma ExcenterExists.northPole_erase {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} (hi : s.ExcenterExists (signs.erase i)) :
    s.northPole (signs.erase i) i = s.northPole signs i := by
  by_cases hs : i ∈ signs
  · rw [← Finset.insert_erase hs] at h
    nth_rw 2 [← Finset.insert_erase hs]
    exact (hi.northPole_insert h).symm
  · simp [hs]

@[simp] lemma northPole_singleton_self [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.northPole {i} i = s.southPole i := by
  rw [← Finset.insert_empty, ← northPole_empty, s.excenterExists_empty.northPole_insert]
  rw [Finset.insert_empty]
  exact s.excenterExists_singleton _

lemma northPole_mem_affineSpan_pair (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.northPole signs i ∈ line[ℝ, s.points i, s.excenter signs] :=
  Sphere.secondInter_vsub_mem_affineSpan _ _ _

lemma southPole_mem_affineSpan_pair (i : Fin (n + 1)) :
    s.southPole i ∈ line[ℝ, s.points i, s.incenter] :=
  s.northPole_mem_affineSpan_pair _ _

variable {s} in
lemma ExcenterExists.northPole_mem_affineSpan_range {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.northPole signs i ∈ affineSpan ℝ (Set.range s.points) :=
  IsConcreteLE.le_iff.1 (affineSpan_pair_le_of_mem_of_mem (mem_affineSpan _ (by simp))
    h.excenter_mem_affineSpan_range) (s.northPole_mem_affineSpan_pair _ _)

lemma southPole_mem_affineSpan_range (i : Fin (n + 1)) :
    s.southPole i ∈ affineSpan ℝ (Set.range s.points) :=
  s.excenterExists_empty.northPole_mem_affineSpan_range _

lemma northPole_mem_circumsphere (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.northPole signs i ∈ s.circumsphere := by
  simp [northPole, mem_circumsphere]

lemma southPole_mem_circumsphere (i : Fin (n + 1)) : s.southPole i ∈ s.circumsphere :=
  s.northPole_mem_circumsphere _ _

end Simplex

namespace Triangle

open Simplex

lemma northPole_singleton_of_ne (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) :
    t.northPole {i₂} i₁ = t.northPole {i₃} i₁ := by
  by_cases h₂₃ : i₂ = i₃
  · rw [h₂₃]
  have h : ({i₃} : Finset (Fin 3)) = {i₁, i₂}ᶜ := by decide +revert
  rw [h, northPole_compl, (t.excenterExists _).northPole_insert (t.excenterExists _)]

end Triangle

end Affine
