/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive

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

 * `Polarization` is strictly positive on non-zero linear combinations of roots.  That is, it is
  positive-definite when restricted to the linear span of roots.  This gives us a convenient way to
  eliminate certain Dynkin diagrams from the classification, since it suffices to produce a nonzero
  linear combination of simple roots with non-positive norm.
 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.

## Todo

* Weyl group - how to do induction by subgroup closure?
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

section

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

/-!
theorem : if there is a nonzero vector with nonpositive norm in the span of roots, then the root
pairing is infinite.
Maybe better to say, given a finite root pairing, all nonzero combinations of simple roots have
strictly positive norm.
Then, we can say, a Dynkin diagram is not finite type if there is a nonzero combination of simple
roots that has nonpositive norm.
-/

/-- An invariant linear map from weight space to coweight space. -/
@[simps]
def Polarization [Finite ι] : M →ₗ[R] N where
  toFun m :=
    haveI := Fintype.ofFinite ι
    ∑ (i : ι), P.toLin m (P.coroot i) • (P.coroot i)
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc]

theorem polarization_self [Finite ι] (x : M) :
    haveI := Fintype.ofFinite ι
    P.toLin x (P.Polarization x) =
      ∑ (i : ι), P.toLin x (P.coroot i) * P.toLin x (P.coroot i) := by
  simp

theorem polarization_root_self [Finite ι] (j : ι) :
    haveI := Fintype.ofFinite ι
    P.toLin (P.root j) (P.Polarization (P.root j)) =
      ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp

-- reflections taken to coreflections.  polarization_self = sum of squares

/-- An invariant inner product on the weight space. -/
@[simps]
def PolInner [Finite ι] : M →ₗ[R] M →ₗ[R] R where
  toFun x := P.toLin x ∘ₗ P.Polarization
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' r x := by simp only [LinearMapClass.map_smul, RingHom.id_apply, LinearMap.smul_comp]

theorem polInner_symmetric [Finite ι] (x y : M) :
    P.PolInner x y = P.PolInner y x := by
  simp [mul_comm]

lemma reflection_coroot_perm {i j : ι} (y : M) :
    (P.toLin ((P.reflection i) y)) (P.coroot j) = P.toLin y (P.coroot (P.reflection_perm i j)) := by
  simp only [reflection_apply, map_sub, LinearMapClass.map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, root_coroot_eq_pairing, smul_eq_mul, mul_comm, coroot_reflection_perm,
    coreflection_apply_coroot]

theorem polInner_reflection_invariant [Finite ι] (i : ι) (x y : M) :
    P.PolInner (P.reflection i x) (P.reflection i y) = P.PolInner x y := by
  simp only [PolInner_apply, LinearMap.coe_comp, comp_apply, Polarization_apply, map_sum,
    LinearMapClass.map_smul, smul_eq_mul, reflection_coroot_perm]
  letI := Fintype.ofFinite ι
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun x_1 ↦ (P.toLin y) (P.coroot ((P.reflection_perm i) x_1)) *
      (P.toLin x) (P.coroot ((P.reflection_perm i) x_1)))
    (fun x_1 ↦ (P.toLin y) (P.coroot x_1) * (P.toLin x) (P.coroot x_1)) (congrFun rfl)

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

lemma root_covector_coroot (x : N) (i : ι) :
    (P.toLin (P.root i) x) • P.coroot i = (x - P.coreflection i x) := by
  rw [coreflection_apply, sub_sub_cancel]

lemma pairing_reflection_perm (P : RootPairing ι R M N) (i j k : ι) :
    P.pairing j (P.reflection_perm i k) = P.pairing (P.reflection_perm i j) k := by
  rw [pairing, ← reflection_perm_coroot, pairing, ← reflection_perm_root, map_sub, map_sub]
  simp [mul_comm]

@[simp]
lemma pairing_reflection_perm_self (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflection_perm i i) j = - P.pairing i j := by
  rw [pairing, ← reflection_perm_root, root_coroot_two, two_smul, sub_add_cancel_left,
    LinearMap.map_neg₂, root_coroot_eq_pairing]

/-- SGA3 XXI Lemma 1.2.1 (10) -/
lemma PolInner_self_coroot (P : RootPairing ι R M N) [Finite ι] (i : ι) :
    (P.PolInner (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  letI := Fintype.ofFinite ι
  have hP : P.Polarization (P.root i) =
      ∑ j : ι, P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j) := by
    simp_rw [Polarization_apply, root_coroot_eq_pairing]
    convert (Fintype.sum_equiv (P.reflection_perm i)
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

/-!
positive definite on R-span of roots, Weyl-invariant.  If `P` is crystallographic,
then this takes integer values.

LinearOrderedCommRing version of Cauchy-Schwarz:
`|(x,y) • x - (x,x) • y|^2 = |x|^2(|x|^2 * |y|^2 - (x,y)^2)` (easy cancellation)

This constrains coxeterWeight to at most 4, and proportionality when 4.
-/

-- faithful Weyl action on roots: for all x, w(x)-x lies in R-span of roots.
--If all roots are fixed by w, then (w(x)-x, r) = (x, w^-1r -r)=0. w(x) - w by nondeg on R-span.
-- finiteness of Weyl follows from finiteness of permutations of roots.

--positivity constraints for finite root pairings mean we restrict to weights between 0 and 4.

end

section linearOrderedCommRing

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

-- should I just say positive semi-definite?
theorem polInner_self_non_neg [Finite ι] (x : M) : 0 ≤ P.PolInner x x := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_self]
  exact Finset.sum_nonneg fun i _ =>
    (sq (P.toLin x (P.coroot i))) ▸ sq_nonneg (P.toLin x (P.coroot i))

--lemma coxeter_weight_leq_4 :


theorem polInner_root_self_pos [Finite ι] (j : ι) :
    0 < P.PolInner (P.root j) (P.root j) := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_root_self]
  refine Finset.sum_pos' ?_ ?_
  · exact fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)
  use j
  refine ⟨letI := Fintype.ofFinite ι; Finset.mem_univ j, ?_⟩
  rw [pairing, root_coroot_two]
  norm_num

theorem polInner_root_positive [Finite ι] : IsRootPositive P P.PolInner where
  zero_lt_apply_root i := P.polInner_root_self_pos i
  symm := P.polInner_symmetric
  apply_reflection_eq := P.polInner_reflection_invariant

end linearOrderedCommRing

end RootPairing
