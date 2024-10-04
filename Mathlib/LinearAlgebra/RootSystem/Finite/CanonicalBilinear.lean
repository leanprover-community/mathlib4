/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.Dimension.LinearMap

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
 * `rootForm_self_coroot`: Two times `RootForm` applied to a root is a multiple of
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
--#find_home! rank_le_of_injective_smul --[Mathlib.LinearAlgebra.Dimension.Basic]

lemma injective_smul_pos_of_reflective [LinearOrderedCommRing R] [AddCommGroup M] [Module R M]
    [IsReflexive R M] {r : R} (hr : 0 < r) : Injective fun (x : M) => r • x := by
  intro x y hxy
  simp only at hxy

  sorry

namespace RootPairing

section CommRing

variable [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

/-- An invariant linear map from weight space to coweight space. -/
def Polarization : M →ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]
lemma Polarization_apply (x : M) :
    P.Polarization x = ∑ i, P.toPerfectPairing x (P.coroot i) • P.coroot i := by
  simp [Polarization]

/-- An invariant linear map from coweight space to weight space. -/
def CoPolarization : N →ₗ[R] M :=
  ∑ i, LinearMap.toSpanSingleton R M (P.root i) ∘ₗ P.root' i

@[simp]
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.toPerfectPairing (P.root i) x • P.root i := by
  simp [CoPolarization]

lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization := by
  ext x
  simp only [CoPolarization, LinearMap.coeFn_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization, PerfectPairing.flip_apply_apply]
  exact rfl

/-- An invariant inner product on the weight space. -/
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (LinearMap.lsmul R R).compl₁₂ (P.coroot' i) (P.coroot' i)

/-- An invariant inner product on the coweight space. -/
def CorootForm : LinearMap.BilinForm R N :=
  ∑ i, (LinearMap.lsmul R R).compl₁₂ (P.root' i) (P.root' i)

@[simp]
lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ (i : ι), P.toPerfectPairing x (P.coroot i) * P.toPerfectPairing y (P.coroot i) := by
  simp [RootForm]

lemma rootForm_symmetric :
    LinearMap.IsSymm P.RootForm := by
  simp [LinearMap.IsSymm, mul_comm]

lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, reflection_coroot_perm]
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun x_1 ↦ (P.toPerfectPairing x) (P.coroot ((P.reflection_perm i) x_1)) *
      (P.toPerfectPairing y) (P.coroot ((P.reflection_perm i) x_1)))
    (fun x_1 ↦ (P.toPerfectPairing x) (P.coroot x_1) *
      (P.toPerfectPairing y) (P.coroot x_1)) (congrFun rfl)

/-- This is SGA3 XXI Lemma 1.2.1 (10), key for proving nondegeneracy and positivity. -/
lemma rootForm_self_smul_coroot (P : RootPairing ι R M N) (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
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
  simp only [rootForm_apply_apply, LinearMap.coe_comp, comp_apply, Polarization_apply,
    root_coroot_eq_pairing, map_sum, LinearMapClass.map_smul, Finset.sum_neg_distrib, ← smul_assoc]
  rw [Finset.sum_smul, add_neg_eq_zero.mpr rfl]
  exact sub_eq_zero_of_eq rfl

lemma flip_rootForm_self_smul_root (P : RootPairing ι R M N) (i : ι) :
    (P.flip.RootForm (P.coroot i) (P.coroot i)) • P.root i =
      2 • P.flip.Polarization (P.coroot i) :=
  rootForm_self_smul_coroot (P.flip) i

lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ isSumSq_sum_mul_self Finset.univ _

lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp

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


lemma four_smul_flip_polarization_polarization (P : RootPairing ι R M N) (i : ι) :
    4 • P.flip.Polarization (P.Polarization (P.root i)) =
    (P.RootForm (P.root i) (P.root i)) •
      (P.flip.RootForm (P.coroot i) (P.coroot i)) • P.root i := by
  rw [show 4 = 2 • 2 by rfl, smul_assoc, ← map_nsmul, ← rootForm_self_coroot, map_smul,
    flip_rootForm_self_root, smul_comm]
-/

end CommRing

section LinearOrderedCommRing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

--use IsSumSq.nonneg ?
theorem rootForm_self_non_neg (x : M) : 0 ≤ P.RootForm x x :=
  IsSumSq.nonneg (P.rootForm_self_sum_of_squares x)

theorem rootForm_self_zero_iff (x : M) :
    P.RootForm x x = 0 ↔ ∀ i, P.toPerfectPairing x (P.coroot i) = 0 := by
  simp only [rootForm_apply_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert sum_mul_self_eq_zero_iff Finset.univ fun i => (P.toPerfectPairing x) (P.coroot i)
  constructor
  · intro x _
    exact x
  · rename_i i
    intro x
    refine x ?_
    exact Finset.mem_univ i

lemma rootForm_root_self_pos (j : ι) :
    0 < P.RootForm (P.root j) (P.root j) := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    rootForm_apply_apply, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  exact ⟨Finset.mem_univ j, (by simp)⟩

lemma rootForm_rootPositive : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply

lemma prod_rootForm_root_self_pos :
    0 < ∏ i, P.RootForm (P.root i) (P.root i) :=
  Finset.prod_pos fun i _ => rootForm_root_self_pos P i

lemma prod_rootForm_smul_coroot_in_range (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈ LinearMap.range P.Polarization := by
  have hdvd : P.RootForm (P.root i) (P.root i) ∣ ∏ a : ι, P.RootForm (P.root a) (P.root a) := by
    refine Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a)) (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • P.root i
  simp

lemma rank_polarization_eq_rank_span_coroot :
    LinearMap.rank P.Polarization = Module.rank R (span R (range P.coroot)) := by
  refine eq_of_le_of_le (rank_le_of_submodule (LinearMap.range P.Polarization)
    (span R (range ⇑P.coroot)) P.range_polarization_le_span_coroot) ?_
  letI : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine rank_le_of_injective_smul (span R (range P.coroot)) (LinearMap.range P.Polarization)
    (injective_smul_pos_of_reflective P.prod_rootForm_root_self_pos) ?_
  intro x hx
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range P.Polarization) c
    (fun c _ ↦ prod_rootForm_smul_coroot_in_range P c)

-- injectivity from lemma: reflexive modules over a domain have no torsion

/-!
lemma rank_eq_zero_iff :
    Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by

theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by

lemma coxeter_weight_leq_4 (i j : ι) : coxeterWeight i j ≤ 4 := by
  sorry

-/

end LinearOrderedCommRing

end RootPairing
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
 * `RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## References:
 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:
 * `polarization_self_sum_of_squares` : The inner product of any weight vector is a sum of squares.
 * `rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
   to reflections.
 * `rootForm_self_smul_coroot`: The inner product of a root with itself times the
   corresponding coroot is equal to two times Polarization applied to the root.

## TODO (possibly in other files)
 * Positivity and nondegeneracy
 * Weyl-invariance
 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.
-/

open Function
open Module hiding reflection

noncomputable section

variable {ι R M N : Type*}

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

lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ (i : ι), P.coroot' i x * P.coroot' i y := by
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

lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ isSumSq_sum_mul_self Finset.univ _

lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]

end CommRing

end RootPairing
