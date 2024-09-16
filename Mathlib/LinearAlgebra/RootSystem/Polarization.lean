/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive
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

 * `polInner_rootPositive`: `PolInner` is strictly positive on roots.
 * `polInner_posDef` : `PolInner` is strictly positive on non-zero linear combinations of roots.
  That is, it is positive-definite when restricted to the linear span of roots.  This gives
  us a convenient way to eliminate certain Dynkin diagrams from the classification, since it
  suffices to produce a nonzero linear combination of simple roots with non-positive norm.

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

namespace RootPairing

section CommRing

variable [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
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

-- reflections taken to coreflections.

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

section LinearOrderedCommRing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

--use IsSumSq.nonneg ?
theorem polInner_self_non_neg (x : M) : 0 ≤ P.PolInner x x := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_self, toLin_toPerfectPairing]
  exact Finset.sum_nonneg fun i _ =>
    (sq (P.toPerfectPairing x (P.coroot i))) ▸ sq_nonneg (P.toPerfectPairing x (P.coroot i))

theorem polInner_self_zero_iff (x : M) :
    P.PolInner x x = 0 ↔ ∀ i, P.toPerfectPairing x (P.coroot i) = 0 := by
  simp only [PolInner_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert sum_of_squares_eq_zero_iff Finset.univ fun i => (P.toPerfectPairing x) (P.coroot i)
  constructor
  · intro x _
    exact x
  · rename_i i
    intro x
    refine x ?_
    exact Finset.mem_univ i

-- Use four_smul_flip_polarization_polarization to get injectivity of Polarization.

--lemma coxeter_weight_leq_4 :

lemma polInner_root_self_pos (j : ι) :
    0 < P.PolInner (P.root j) (P.root j) := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_root_self, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  refine ⟨Finset.mem_univ j, ?_⟩
  simp only [pairing_same, Nat.ofNat_pos, mul_pos_iff_of_pos_left]

lemma polInner_rootPositive : IsRootPositive P P.PolInner where
  zero_lt_apply_root i := P.polInner_root_self_pos i
  symm := P.polInner_symmetric
  apply_reflection_eq := P.polInner_reflection_reflection_apply

/-!
lemma positive_definite_polInner {x : M} (hx : x ∈ span R (range P.root)) (h : P.PolInner x x = 0) :
    x = 0 := by
  rw [mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  rw [← hc] at h
  simp at h

  sorry

For any bilinear form over a commutative ring,
`|(x,y) • x - (x,x) • y|^2 = |x|^2(|x|^2 * |y|^2 - (x,y)^2)` (easy cancellation)
LinearOrderedCommRing version of Cauchy-Schwarz: right side of above is non-neg, and only zero when
`(x,y) • x - (x,x) • y = 0`, i.e., linearly dependent.

This constrains coxeterWeight to at most 4, and proportionality when 4.
-/

-- faithful Weyl action on roots: for all x, w(x)-x lies in R-span of roots.
--If all roots are fixed by w, then (w(x)-x, r) = (x, w^-1r -r)=0. w(x) - w by nondeg on R-span.
-- finiteness of Weyl follows from finiteness of permutations of roots.

--positivity constraints for finite root pairings mean we restrict to weights between 0 and 4.

end LinearOrderedCommRing

end RootPairing
