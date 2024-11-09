/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.SumsOfSquares
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
 * `RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## References:

 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:
 * `polarization_self_sum_of_squares` : The inner product of any weight vector is a sum of squares.
 * `rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
   to reflections.
 * `rootForm_self_smul_coroot`: Two times `RootForm` applied to a root is a multiple of
   the corresponding coroot.

## TODO (possibly in other files)
 * Positivity and nondegeneracy
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

lemma rank_le_of_smul_regular [CommRing R] [AddCommGroup M] [Module R M]
    (L L' : Submodule R M) {r : R} (hr : IsSMulRegular M r) (h : ∀ x ∈ L, r • x ∈ L') :
    Module.rank R L ≤ Module.rank R L' := by
  let f : L →ₗ[R] L' :=
    { toFun := fun x => ⟨r • x, h x x.2⟩
      map_add' := fun x y => by simp
      map_smul' := fun s x => by simp [← smul_assoc, mul_comm] }
  refine LinearMap.rank_le_of_injective f (fun x y hxy => ?_)
  rw [show f x = ⟨r • x, h x x.2⟩ by rfl, show f y = ⟨r • y, h y y.2⟩ by rfl] at hxy
  simp only [Subtype.mk.injEq] at hxy
  exact SetLike.coe_eq_coe.mp (hr (hr (congrArg (HSMul.hSMul r) hxy)))
--#find_home! rank_le_of_smul_regular --[Mathlib.LinearAlgebra.Dimension.Basic]

lemma torsion_free_of_reflexive [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsReflexive R M] {r : R} {m : M} (h : r • m = 0) (hr : r ≠ 0) : m = 0 := by
  suffices Dual.eval R M m = Dual.eval R M 0 by exact (bijective_dual_eval R M).injective this
  ext n
  simp only [Dual.eval_apply, map_zero, LinearMap.zero_apply]
  suffices r • n m = 0 by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hr this
  rw [← LinearMap.map_smul_of_tower, h, LinearMap.map_zero]
--#find_home! torsion_free_of_reflexive -- [Mathlib.LinearAlgebra.Dual]

lemma injective_smul_pos_of_reflexive [LinearOrderedCommRing R] [AddCommGroup M] [Module R M]
    [IsReflexive R M] {r : R} (hr : 0 < r) : Injective fun (x : M) => r • x := by
  intro x y hxy
  simp only at hxy
  have hrxy : r • (x - y) = 0 := by rw [smul_sub, hxy, sub_eq_zero]
  exact sub_eq_zero.mp <| torsion_free_of_reflexive hrxy <| Ne.symm (ne_of_lt hr)

namespace RootPairing

section CommRing

variable [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

/-- An invariant linear map from weight space to coweight space. -/
def Polarization : M →ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]
lemma Polarization_apply (x : M) :
    P.Polarization x = ∑ i, P.coroot' i x • P.coroot i := by
  simp [Polarization]

/-- An invariant linear map from coweight space to weight space. -/
def CoPolarization : N →ₗ[R] M :=
  ∑ i, LinearMap.toSpanSingleton R M (P.root i) ∘ₗ P.root' i

@[simp]
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.root' i x • P.root i := by
  simp [CoPolarization]

lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization :=
  rfl

/-- An invariant inner product on the weight space. -/
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (P.coroot' i).smulRight (P.coroot' i)

/-- An invariant inner product on the coweight space. -/
def CorootForm : LinearMap.BilinForm R N :=
  ∑ i, (P.root' i).smulRight (P.root' i)

@[simp]
lemma flip_RootForm_eq_CorootForm : P.flip.RootForm = P.CorootForm :=
  rfl

lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ (i : ι), P.coroot' i x * P.coroot' i y := by
  simp [RootForm]

lemma Polarization_apply_apply (x y : M) :
    P.toPerfectPairing y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]

lemma rootForm_symmetric :
    LinearMap.IsSymm P.RootForm := by
  simp [LinearMap.IsSymm, mul_comm, rootForm_apply_apply]

@[simp]
lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun j ↦ (P.coroot' (P.reflection_perm i j) x) * (P.coroot' (P.reflection_perm i j) y))
    (fun j ↦ P.coroot' j x * P.coroot' j y) (congrFun rfl)

/-- This is SGA3 XXI Lemma 1.2.1 (10), key for proving nondegeneracy and positivity. -/
lemma rootForm_self_smul_coroot (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have hP : P.Polarization (P.root i) =
      ∑ j : ι, P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j) := by
    simp_rw [Polarization_apply, root_coroot'_eq_pairing]
    exact (Fintype.sum_equiv (P.reflection_perm i)
          (fun j ↦ P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j))
          (fun j ↦ P.pairing i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [Polarization_apply]
  simp only [root_coroot'_eq_pairing, pairing_reflection_perm, pairing_reflection_perm_self_left,
    ← reflection_perm_coroot, smul_sub, neg_smul, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add]
  simp only [rootForm_apply_apply, LinearMap.coe_comp, comp_apply, Polarization_apply,
    root_coroot_eq_pairing, map_sum, LinearMapClass.map_smul, Finset.sum_neg_distrib, ← smul_assoc]
  rw [Finset.sum_smul, add_neg_eq_zero.mpr rfl]
  exact sub_eq_zero_of_eq rfl

lemma corootForm_self_smul_root (i : ι) :
    (P.CorootForm (P.coroot i) (P.coroot i)) • P.root i = 2 • P.CoPolarization (P.coroot i) :=
  rootForm_self_smul_coroot (P.flip) i

lemma rootForm_mul_pairing (i j : ι) : P.RootForm (P.root i) (P.root i) * P.pairing j i =
    P.RootForm (P.root j) (P.root j) * P.pairing i j := by
  rw [pairing, root', ← smul_eq_mul, ← map_smul, rootForm_self_smul_coroot, map_nsmul,
    Polarization_apply_apply, pairing, root', ← smul_eq_mul,
    ← map_smul _ ((P.RootForm (P.root j)) (P.root j)), rootForm_self_smul_coroot, map_nsmul,
    Polarization_apply_apply]
  simp [RootForm, mul_comm]

lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ isSumSq_sum_mul_self Finset.univ _

lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]

theorem range_polarization_le_span_coroot :
    LinearMap.range P.Polarization ≤ (span R (range P.coroot)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, Polarization_apply]
  refine (mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)
  simp

theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict (span R (range P.root))) ≤
      (span R (range P.coroot)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, LinearMap.domRestrict_apply, Polarization_apply]
  refine (mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)
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

-- TODO : rootForm_weyl_invariant
/-! lemma rootForm_weyl_invariant (P : RootPairing ι R M N) [Finite ι]
    (w : Subgroup.closure {P.reflection i | i : ι}) :
    ∀ x y : M, P.RootForm (w.val x) (w.val y) = P.RootForm x y := by
  induction w.val using Subgroup.closure_induction (x := w.val) with
  | h => exact SetLike.coe_mem w
  | mem => sorry
  | one => simp
  | mul => sorry
  | inv => sorry
-/

end CommRing

section LinearOrderedCommRing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

theorem rootForm_self_non_neg (x : M) : 0 ≤ P.RootForm x x :=
  IsSumSq.nonneg (P.rootForm_self_sum_of_squares x)

theorem rootForm_self_zero_iff (x : M) :
    P.RootForm x x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  simp only [rootForm_apply_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert sum_mul_self_eq_zero_iff Finset.univ fun i => P.coroot' i x
  refine { mp := fun x _ => x, mpr := ?_ }
  rename_i i
  exact fun x => x (Finset.mem_univ i)

lemma rootForm_root_self_pos (j : ι) :
    0 < P.RootForm (P.root j) (P.root j) := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    rootForm_apply_apply, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  exact ⟨Finset.mem_univ j, by simp⟩

instance : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply

lemma prod_rootForm_root_self_pos :
    0 < ∏ i, P.RootForm (P.root i) (P.root i) :=
  Finset.prod_pos fun i _ => rootForm_root_self_pos P i

lemma prod_rootForm_smul_coroot_in_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈
      LinearMap.range (P.Polarization.domRestrict (span R (range P.root))) := by
  have hdvd : P.RootForm (P.root i) (P.root i) ∣ ∏ a : ι, P.RootForm (P.root a) (P.root a) :=
    Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a)) (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨(c • 2 • P.root i), by aesop⟩
  simp

end LinearOrderedCommRing

end RootPairing
