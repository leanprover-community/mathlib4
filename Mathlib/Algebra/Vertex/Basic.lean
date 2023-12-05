/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.HahnSeries
import Mathlib.Algebra.Vertex.Defs

/-!
# Basic results on Vertex algebras

In this file we prove some basic results about vertex algebras.

## Main results

* The Borcherds identity implies assocativity

## To do

In the non-unital setting:
* Commutator formula from Borcherds identity
* Locality from Borcherds identity
* Weak associativity from Borcherds identity
* Borcherds identity from (commutator or locality) and (associativity or weak associativity)

In the unital setting:
* Skew-symmetry
* Hasse-Schmidt differential
* creative fields?
* reconstruction?

## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
Matsuo-Nagatomo?
Borcherds's original paper?

-/
universe u v

variable {V : Type u} {R : Type v}

namespace VertexAlg

theorem associativity_left [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) :
    Borcherds_sum_1 R a b c 0 s t = index (Y R (index (Y R a) t b)) s c := by
  unfold Borcherds_sum_1
  cases h : (Int.toNat (-t - order R a b)) with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      have hab: - order R a b ≤ t := by
        rw [← @sub_nonpos, neg_sub_left, @neg_add']
        exact Int.toNat_eq_zero.mp h
      rw [index_zero_if_neg_order_leq a b t hab, LinearMap.map_zero, VertexAlg.zero_index,
        LinearMap.zero_apply]
    | succ n =>
      have supp_zero (i : ℕ) (hi : 1 ≤ i) :
          Ring.choose (0 : ℤ)  i • ((Y R) (((Y R) a⁅t + ↑i⁆) b)⁅0 + s - ↑i⁆) c = 0 := by
        rw [Ring.choose_zero_pos i (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
          zero_smul]
      rw [Finset.eventually_constant_sum supp_zero (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, zero_add, Ring.choose_zero_right, one_smul,
        Nat.cast_zero, add_zero, sub_zero]

theorem associativity_right [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) : Borcherds_sum_2 R a b c 0 s t + Borcherds_sum_3 R a b c 0 s t =
    Finset.sum (Finset.range (Int.toNat (-s - order R b c))) (fun i ↦ (-1)^i •
    (Ring.choose (0 : ℤ) i) • index (Y R a) (t-i) (index (Y R b) (s+i) c)) +
    Finset.sum (Finset.range (Int.toNat (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i) •
    (Ring.choose t i) • index (Y R b) (s+t-i) (index (Y R a) i c)) := by
  unfold Borcherds_sum_2 Borcherds_sum_3
  simp only [Nat.odd_iff_not_even, neg_zero, zero_sub, zero_add]

/-- The associativity property of vertex algebras - maybe put this in defs? -/
def associativity (R : Type v) [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) : Prop := ((Y R) (((Y R) a⁅t⁆) b)⁅s⁆) c = Finset.sum (Finset.range
    (Int.toNat (-s - order R b c))) (fun i ↦ (-1)^i • (Ring.choose (0 : ℤ)  i) •
    index (Y R a) (t-i) (index (Y R b) (s+i) c)) + Finset.sum (Finset.range (Int.toNat
    (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i) • (Ring.choose t i) • index (Y R b) (s+t-i)
    (index (Y R a) i c))

theorem Borcherds_id_implies_associativity [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (s t : ℤ) : Borcherds_id R a b c 0 s t →
    associativity R a b c s t := by
  intro hb
  unfold Borcherds_id at hb
  rw [associativity_left, associativity_right] at hb
  exact hb

/-!

theorem commutator_right_2 [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : borcherds2 u v w r s 0 = u r (v s w) := by
  sorry

theorem commutator_right_3 [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : borcherds3 u v w r s 0 = v s (u r w) := by
  sorry

theorem commutator_formula

-- theorem unit_left (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :


theorem borcherds1Induction [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_1 R a b c (r + 1) s t =
    Borcherds_sum_1 R a b c r (s + 1) t + Borcherds_sum_1 R a b c r s (t + 1) := by
  unfold Borcherds_sum_1
  -- decompose Ring.choose (r+1) i into Ring.choose r i and Ring.choose r (i-1).
  -- compare resulting sums with component sums.
  sorry

theorem borcherds2Induction [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_2 R a b c (r + 1) s t =
    Borcherds_sum_2 R a b c r (s + 1) t + Borcherds_sum_2 R a b c r s (t + 1) := by
  unfold Borcherds_sum_2
  -- decompose Ring.choose (r+1) i into Ring.choose r i and Ring.choose r (i-1).
  -- compare resulting sums with component sums.
  sorry

theorem borcherds3Induction [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_3 R a b c (r + 1) s t =
    Borcherds_sum_3 R a b c r (s + 1) t + Borcherds_sum_3 R a b c r s (t + 1) := by
  unfold Borcherds_sum_3
  -- decompose Ring.choose (t+1) i into Ring.choose t i and Ring.choose t (i-1).
  -- compare resulting sums with component sums.
  sorry



-/
