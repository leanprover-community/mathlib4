/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# The canonical bilinear form on a finite root pairing
Given a finite root pairing, we define a canonical map from weight space to coweight space, and the
corresponding bilinear form. This form is symmetric and Weyl-invariant, and if the base ring is
linearly ordered, then the form is root-positive, positive-semidefinite on the weight space, and
positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4. Thus, the pairings of roots and coroots in a crystallographic root pairing are
restricted to a small finite set of possibilities.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main definitions:
 * `Polarization`: A distinguished linear map from the weight space to the coweight space.
 * `CanonicalBilinear` : The bilinear form on weight space corresponding to `Polarization`.

## References:
 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:
 * `polarization_self_sum_of_squares` : The inner product of any weight vector is a sum of squares.
 * `canonicalBilinear_reflection_reflection_apply` : `CanonicalBilinear` is invariant with respect
   to reflections.
 * `canonicalBilinear_self_smul_coroot`: The inner product of a root with itself times the
   corresponding coroot is equal to two times Polarization applied to the root.

## TODO (possibly in other files)
 * Positivity and nondegeneracy
 * Weyl-invariance
 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.
-/

open Set Function
open Module hiding reflection

noncomputable section

variable {ι R M N : Type*}

lemma isSumSq_of_sum_of_squares [Mul R] [AddCommMonoid R] (s : Finset ι) (f : ι → R) :
    IsSumSq (∑ i ∈ s, f i * f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simpa only [Finset.sum_empty] using IsSumSq.zero
  | cons i s his h =>
    simp only [Finset.sum_cons]
    exact IsSumSq.sq_add (f i) (∑ i ∈ s, f i * f i) h
--#find_home! isSumSq_of_sum_of_squares --returns this file

namespace RootPairing

section CommRing

variable [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

/-- An invariant linear map from weight space to coweight space. -/
@[simps]
def Polarization : M →ₗ[R] N where
  toFun m := ∑ (i : ι), P.toPerfectPairing m (P.coroot i) • (P.coroot i)
  map_add' x y := by
    simp only [← toLin_toPerfectPairing, map_add, PerfectPairing.toLin_apply, LinearMap.add_apply,
      add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [← toLin_toPerfectPairing, map_smul, LinearMap.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_assoc]

/-- An invariant inner product on the weight space. -/
@[simps]
def CanonicalBilinear : M →ₗ[R] M →ₗ[R] R where
  toFun x := P.toLin x ∘ₗ P.Polarization
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' r x := by simp only [LinearMapClass.map_smul, RingHom.id_apply, LinearMap.smul_comp]

lemma canonicalBilinear_apply_apply (x y : M) : P.CanonicalBilinear x y =
    ∑ (i : ι), P.toPerfectPairing y (P.coroot i) * P.toPerfectPairing x (P.coroot i) := by
  simp

lemma canonicalBilinear_symmetric :
    LinearMap.IsSymm P.CanonicalBilinear := by
  simp [LinearMap.IsSymm, mul_comm]

lemma canonicalBilinear_reflection_reflection_apply (i : ι) (x y : M) :
    P.CanonicalBilinear (P.reflection i x) (P.reflection i y) = P.CanonicalBilinear x y := by
  simp only [CanonicalBilinear_apply, LinearMap.coe_comp, comp_apply, Polarization_apply, map_sum,
    LinearMapClass.map_smul, smul_eq_mul, reflection_coroot_perm, toLin_toPerfectPairing]
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun x_1 ↦ (P.toPerfectPairing y) (P.coroot ((P.reflection_perm i) x_1)) *
      (P.toPerfectPairing x) (P.coroot ((P.reflection_perm i) x_1)))
    (fun x_1 ↦ (P.toPerfectPairing y) (P.coroot x_1) *
      (P.toPerfectPairing x) (P.coroot x_1)) (congrFun rfl)

/-- This is SGA3 XXI Lemma 1.2.1 (10), key for proving nondegeneracy and positivity. -/
lemma canonicalBilinear_self_smul_coroot (P : RootPairing ι R M N) (i : ι) :
    (P.CanonicalBilinear (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have hP : P.Polarization (P.root i) =
      ∑ j : ι, P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j) := by
    simp_rw [Polarization_apply, root_coroot_eq_pairing]
    exact (Fintype.sum_equiv (P.reflection_perm i)
          (fun j ↦ P.pairing i ((P.reflection_perm i) j) • P.coroot ((P.reflection_perm i) j))
          (fun j ↦ P.pairing i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [Polarization_apply]
  simp only [root_coroot_eq_pairing, pairing_reflection_perm, pairing_reflection_perm_self,
    ← reflection_perm_coroot, smul_sub, neg_smul, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add]
  simp only [CanonicalBilinear_apply, LinearMap.coe_comp, comp_apply, Polarization_apply,
    root_coroot_eq_pairing, map_sum, LinearMapClass.map_smul, Finset.sum_neg_distrib, ← smul_assoc]
  rw [Finset.sum_smul, add_neg_eq_zero.mpr rfl]
  exact sub_eq_zero_of_eq rfl

lemma flip_canonicalBilinear_self_smul_root (P : RootPairing ι R M N) (i : ι) :
    (P.flip.CanonicalBilinear (P.coroot i) (P.coroot i)) • P.root i =
      2 • P.flip.Polarization (P.coroot i) :=
  canonicalBilinear_self_smul_coroot (P.flip) i

lemma canonicalBilinear_self_sum_of_squares (x : M) :
    IsSumSq (P.CanonicalBilinear x x) :=
  P.canonicalBilinear_apply_apply x x ▸ isSumSq_of_sum_of_squares Finset.univ _

lemma canonicalBilinear_root_self (j : ι) :
    P.CanonicalBilinear (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp

end CommRing

end RootPairing
