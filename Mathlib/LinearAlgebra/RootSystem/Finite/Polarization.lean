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
 * `CanonicalBilinear` : The bilinear form on weight space corresponding to `Polarization`.

## References:

 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:
 * `polarization_self_sum_of_squares` : The inner product of any weight vector is a sum of squares.
 * `canonicalBilinear_reflection_reflection_apply` : `CanonicalBilinear` is invariant with respect
   to reflections.
 * `canonicalBilinear_self_coroot`: Two times `CanonicalBilinear` applied to a root is a multiple of
   the corresponding coroot.

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

lemma rank_le_of_injective_smul [CommRing R] [AddCommGroup M] [Module R M]
    (L L' : Submodule R M) {r : R} (hr : Injective fun (x : M) => r • x) (h : ∀ x ∈ L, r • x ∈ L') :
    Module.rank R L ≤ Module.rank R L' := by
  let f : L →ₗ[R] L' :=
    {
      toFun := fun x => ⟨r • x, h x x.2⟩
      map_add' := fun x y => by simp
      map_smul' := fun s x => by simp [← smul_assoc, mul_comm]
    }
  have hf : Injective f := by
    intro x y hxy
    have hx : f x = ⟨r • x, h x x.2⟩ := rfl
    have hy : f y = ⟨r • y, h y y.2⟩ := rfl
    rw [hx, hy] at hxy
    simp only [Subtype.mk.injEq] at hxy
    exact SetLike.coe_eq_coe.mp (hr (hr (congrArg (HSMul.hSMul r) hxy)))
  exact LinearMap.rank_le_of_injective (R := R) (M := L) f hf

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

theorem range_polarization_le_span_coroot :
    LinearMap.range P.Polarization ≤ (span R (range P.coroot)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, Polarization_apply]
  refine (mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)

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

-- TODO : canonicalBilinear_weyl_invariant
/-! lemma canonicalBilinear_weyl_invariant (P : RootPairing ι R M N) [Finite ι]
    (w : Subgroup.closure {P.reflection i | i : ι}) :
    ∀ x y : M, P.CanonicalBilinear (w.val x) (w.val y) = P.CanonicalBilinear x y := by
  induction w.val using Subgroup.closure_induction (x := w.val) with
  | h => exact SetLike.coe_mem w
  | mem => sorry
  | one => simp
  | mul => sorry
  | inv => sorry


lemma four_smul_flip_polarization_polarization (P : RootPairing ι R M N) (i : ι) :
    4 • P.flip.Polarization (P.Polarization (P.root i)) =
    (P.CanonicalBilinear (P.root i) (P.root i)) •
      (P.flip.CanonicalBilinear (P.coroot i) (P.coroot i)) • P.root i := by
  rw [show 4 = 2 • 2 by rfl, smul_assoc, ← map_nsmul, ← canonicalBilinear_self_coroot, map_smul,
    flip_canonicalBilinear_self_root, smul_comm]
-/

end CommRing

section LinearOrderedCommRing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

--use IsSumSq.nonneg ?
theorem canonicalBilinear_self_non_neg (x : M) : 0 ≤ P.CanonicalBilinear x x :=
  IsSumSq.nonneg (P.canonicalBilinear_self_sum_of_squares x)

theorem canonicalBilinear_self_zero_iff (x : M) :
    P.CanonicalBilinear x x = 0 ↔ ∀ i, P.toPerfectPairing x (P.coroot i) = 0 := by
  simp only [CanonicalBilinear_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert sum_of_squares_eq_zero_iff Finset.univ fun i => (P.toPerfectPairing x) (P.coroot i)
  constructor
  · intro x _
    exact x
  · rename_i i
    intro x
    refine x ?_
    exact Finset.mem_univ i

lemma canonicalBilinear_root_self_pos (j : ι) :
    0 < P.CanonicalBilinear (P.root j) (P.root j) := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    canonicalBilinear_apply_apply, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  exact ⟨Finset.mem_univ j, (by simp)⟩

lemma canonicalBilinear_rootPositive : IsRootPositive P P.CanonicalBilinear where
  zero_lt_apply_root i := P.canonicalBilinear_root_self_pos i
  symm := P.canonicalBilinear_symmetric
  apply_reflection_eq := P.canonicalBilinear_reflection_reflection_apply

lemma prod_canonicalBilinear_root_self_pos :
    0 < ∏ i, P.CanonicalBilinear (P.root i) (P.root i) :=
  Finset.prod_pos fun i _ => canonicalBilinear_root_self_pos P i

/-!
-- injectivity from lemma: reflexive modules over a domain have no torsion

lemma injective_smul {r : R} (hr : 0 < r) : Injective fun (x : M) => r • x := by
  intro x y hxy
  simp only at hxy

  sorry

lemma rank_polarization_eq_rank_span_coroot :
    LinearMap.rank P.Polarization = Module.rank R (span R (range P.coroot)) := by
  refine eq_of_le_of_le (rank_le_of_submodule (LinearMap.range P.Polarization)
    (span R (range ⇑P.coroot)) P.range_polarization_le_span_coroot) ?_
  refine rank_le_of_injective_smul (span R (range ⇑P.coroot)) (LinearMap.range P.Polarization)
    (injective_smul P.prod_canonicalBilinear_root_self_pos) ?_


  sorry


lemma rank_eq_zero_iff :
    Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by

theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by

lemma coxeter_weight_leq_4 (i j : ι) : coxeterWeight i j ≤ 4 := by
  sorry

-/

end LinearOrderedCommRing

end RootPairing
