/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# The polarization of a finite root pairing

Given a finite root pairing, we define a canonical map from weight space to coweight space, and the
corresponding bilinear form.  This form is symmetric and Weyl-invariant, and if the base ring is
linearly ordered, the form is root-positive, positive-semidefinite on the weight space, and
positive-definite on the span of roots.

From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4.  Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`.  Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.

Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main definitions:

 * `Polarization`: A distinguished linear map from the weight space to the coweight space.
 * `PolInner` : The bilinear form on weight space corresponding to `Polarization`.

## References:

 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:
 * `polarization_self_sum_of_squares` : The inner product of any weight vector is a sum of squares.
 * `polInner_reflection_reflection_apply` : `PolInner` is invariant with respect to reflections.
 * `polInner_self_coroot`: Two times `PolInner` applied to a root is a multiple of the corresponding
  coroot.

## Todo

 * Weyl-invariance
 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}

theorem isSumSq_of_sum_of_squares [Mul R] [AddCommMonoid R] (s : Finset ι) (f : ι → R) :
    IsSumSq (∑ i ∈ s, f i * f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simpa only [Finset.sum_empty] using IsSumSq.zero
  | cons i s his h =>
    simp only [Finset.sum_cons]
    exact IsSumSq.sq_add (f i) (∑ i ∈ s, f i * f i) h
--#find_home! isSumSq_of_sum_of_squares --here

theorem sum_of_squares_eq_zero_iff [LinearOrderedCommRing R] (s : Finset ι) (f : ι → R) :
    ∑ i ∈ s, f i * f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his h =>
    simp only [Finset.sum_cons, Finset.mem_cons, forall_eq_or_imp]
    refine ⟨fun hc => ?_, fun hz => by simpa [hz.1] using h.mpr hz.2⟩
    have hhi : f i * f i = 0 := by
      linarith [mul_self_nonneg (f i), IsSumSq.nonneg <| isSumSq_of_sum_of_squares s f]
    exact ⟨zero_eq_mul_self.mp hhi.symm, h.mp (by linarith)⟩
--#find_home! sum_of_squares_eq_zero_iff -- here

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

theorem polarization_self (x : M) :
    P.toPerfectPairing x (P.Polarization x) =
      ∑ (i : ι), P.toPerfectPairing x (P.coroot i) * P.toPerfectPairing x (P.coroot i) := by
  simp

theorem polarization_self_sum_of_squares (x : M) :
    IsSumSq (P.toPerfectPairing x (P.Polarization x)) := by
  rw [polarization_self]
  exact isSumSq_of_sum_of_squares Finset.univ _

theorem polarization_root_self (j : ι) :
    P.toPerfectPairing (P.root j) (P.Polarization (P.root j)) =
      ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp

/-!
theorem polarization_reflection (i : ι) (x : M) :
    P.Polarization (P.reflection i x) = P.coreflection i (P.Polarization x) := by
  simp only [reflection_apply, Polarization_apply, map_sum, map_smul, coreflection_apply,
    root_coroot_eq_pairing, map_sub, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.smul_sum]

  sorry
-/

/-- An invariant inner product on the weight space. -/
@[simps]
def PolInner : M →ₗ[R] M →ₗ[R] R where
  toFun x := P.toLin x ∘ₗ P.Polarization
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' r x := by simp only [LinearMapClass.map_smul, RingHom.id_apply, LinearMap.smul_comp]

theorem polInner_symmetric (x y : M) :
    P.PolInner x y = P.PolInner y x := by
  simp [mul_comm]

theorem polInner_reflection_reflection_apply (i : ι) (x y : M) :
    P.PolInner (P.reflection i x) (P.reflection i y) = P.PolInner x y := by
  simp only [PolInner_apply, LinearMap.coe_comp, comp_apply, Polarization_apply, map_sum,
    LinearMapClass.map_smul, smul_eq_mul, reflection_coroot_perm, toLin_toPerfectPairing]
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun x_1 ↦ (P.toPerfectPairing y) (P.coroot ((P.reflection_perm i) x_1)) *
      (P.toPerfectPairing x) (P.coroot ((P.reflection_perm i) x_1)))
    (fun x_1 ↦ (P.toPerfectPairing y) (P.coroot x_1) *
      (P.toPerfectPairing x) (P.coroot x_1)) (congrFun rfl)

-- TODO : polInner_weyl_invariant
/-! lemma polInner_weyl_invariant (P : RootPairing ι R M N) [Finite ι]
    (w : Subgroup.closure {P.reflection i | i : ι}) :
    ∀ x y : M, P.PolInner (w.val x) (w.val y) = P.PolInner x y := by
  induction w.val using Subgroup.closure_induction (x := w.val) with
  | h => exact SetLike.coe_mem w
  | mem => sorry
  | one => simp
  | mul => sorry
  | inv => sorry
-/

/-- SGA3 XXI Lemma 1.2.1 (10) -/
lemma polInner_self_coroot (P : RootPairing ι R M N) (i : ι) :
    (P.PolInner (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
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
  simp only [PolInner_apply, LinearMap.coe_comp, comp_apply, Polarization_apply,
    root_coroot_eq_pairing, map_sum, LinearMapClass.map_smul, Finset.sum_neg_distrib, ← smul_assoc]
  rw [Finset.sum_smul, add_neg_eq_zero.mpr rfl]
  exact sub_eq_zero_of_eq rfl

lemma flip_polInner_self_root (P : RootPairing ι R M N) (i : ι) :
    (P.flip.PolInner (P.coroot i) (P.coroot i)) • P.root i =
      2 • P.flip.Polarization (P.coroot i) :=
  polInner_self_coroot (P.flip) i

lemma four_smul_flip_polarization_polarization (P : RootPairing ι R M N) (i : ι) :
    4 • P.flip.Polarization (P.Polarization (P.root i)) =
    (P.PolInner (P.root i) (P.root i)) •
      (P.flip.PolInner (P.coroot i) (P.coroot i)) • P.root i := by
  rw [show 4 = 2 • 2 by rfl, smul_assoc, ← map_nsmul, ← polInner_self_coroot, map_smul,
    flip_polInner_self_root, smul_comm]

end CommRing

end RootPairing
