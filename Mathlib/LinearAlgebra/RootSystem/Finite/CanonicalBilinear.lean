/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.LinearAlgebra.RootSystem.RootPositive

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
 * `RootPairing.Polarization`: A distinguished linear map from the weight space to the coweight
   space.
 * `RootPairing.RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## Main results:
 * `RootPairing.rootForm_self_sum_of_squares` : The inner product of any
   weight vector is a sum of squares.
 * `RootPairing.rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
   to reflections.
 * `RootPairing.rootForm_self_smul_coroot`: The inner product of a root with itself
   times the corresponding coroot is equal to two times Polarization applied to the root.
 * `RootPairing.exists_ge_zero_eq_rootForm`: `RootForm` is positive semidefinite.

## References:
 * [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
 * [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

-/

open Set Function
open Module hiding reflection
open Submodule (span)

noncomputable section

variable {ι R M N : Type*}

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

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Fintype

instance [Finite ι] : Module.Finite R P.rootSpan := .span_of_finite R <| finite_range P.root

instance [Finite ι] : Module.Finite R P.corootSpan := .span_of_finite R <| finite_range P.coroot

variable [Fintype ι]

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
    ∑ i, P.coroot' i x * P.coroot' i y := by
  simp [RootForm]

lemma corootForm_apply_apply (x y : N) : P.CorootForm x y =
    ∑ i, P.root' i x * P.root' i y := by
  simp [CorootForm]

lemma toPerfectPairing_apply_apply_Polarization (x y : M) :
    P.toPerfectPairing y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]

lemma toPerfectPairing_apply_CoPolarization (x : N) :
    P.toPerfectPairing (P.CoPolarization x) = P.CorootForm x := by
  ext y
  exact P.flip.toPerfectPairing_apply_apply_Polarization x y

lemma flip_comp_polarization_eq_rootForm :
    P.flip.toLin ∘ₗ P.Polarization = P.RootForm := by
  ext; simp [rootForm_apply_apply, RootPairing.flip]

lemma self_comp_coPolarization_eq_corootForm :
    P.toLin ∘ₗ P.CoPolarization = P.CorootForm := by
  ext; simp [corootForm_apply_apply]

lemma polarization_apply_eq_zero_iff (m : M) :
    P.Polarization m = 0 ↔ P.RootForm m = 0 := by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  change P.toDualRight (P.Polarization m) = 0 at h
  simp only [EmbeddingLike.map_eq_zero_iff] at h
  exact h

lemma coPolarization_apply_eq_zero_iff (n : N) :
    P.CoPolarization n = 0 ↔ P.CorootForm n = 0 :=
  P.flip.polarization_apply_eq_zero_iff n

lemma ker_polarization_eq_ker_rootForm :
    LinearMap.ker P.Polarization = LinearMap.ker P.RootForm := by
  ext; simp only [LinearMap.mem_ker, P.polarization_apply_eq_zero_iff]

lemma ker_copolarization_eq_ker_corootForm :
    LinearMap.ker P.CoPolarization = LinearMap.ker P.CorootForm :=
  P.flip.ker_polarization_eq_ker_rootForm

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

lemma four_nsmul_coPolarization_compl_polarization_apply_root (i : ι) :
    (4 • P.CoPolarization ∘ₗ P.Polarization) (P.root i) =
    (P.RootForm (P.root i) (P.root i) * P.CorootForm (P.coroot i) (P.coroot i)) • P.root i := by
  rw [LinearMap.smul_apply, LinearMap.comp_apply, show 4 = 2 * 2 from rfl, mul_smul, ← map_nsmul,
    ← rootForm_self_smul_coroot, map_smul, smul_comm, ← corootForm_self_smul_root, smul_smul]

lemma four_smul_rootForm_sq_eq_coxeterWeight_smul (i j : ι) :
    4 • (P.RootForm (P.root i) (P.root j)) ^ 2 = P.coxeterWeight i j •
      (P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j)) := by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toPerfectPairing (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toPerfectPairing_apply_apply_Polarization, LinearMap.map_smul_of_tower, ← smul_assoc,
      Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.root j) =
      P.toPerfectPairing (P.root i) (2 • P.Polarization (P.root j)) := by
    rw [show (P.RootForm (P.root i)) (P.root j) = (P.RootForm (P.root j)) (P.root i) by
      apply rootForm_symmetric, ← toPerfectPairing_apply_apply_Polarization,
      LinearMap.map_smul_of_tower]
  rw [sq, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul, hij, ← rootForm_self_smul_coroot,
    smul_mul_assoc 2, ← mul_smul_comm, hji, ← rootForm_self_smul_coroot, map_smul, ← pairing,
    map_smul, ← pairing, smul_eq_mul, smul_eq_mul, smul_eq_mul, coxeterWeight]
  ring

lemma rootForm_mul_pairing (i j : ι) : P.RootForm (P.root i) (P.root i) * P.pairing j i =
    P.RootForm (P.root j) (P.root j) * P.pairing i j := by
  rw [pairing, root', ← smul_eq_mul, ← map_smul, rootForm_self_smul_coroot, map_nsmul,
    toPerfectPairing_apply_apply_Polarization, pairing, root', ← smul_eq_mul,
    ← map_smul _ ((P.RootForm (P.root j)) (P.root j)), rootForm_self_smul_coroot, map_nsmul,
    toPerfectPairing_apply_apply_Polarization]
  simp [RootForm, mul_comm]

lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _

lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]

theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict P.rootSpan) ≤ P.corootSpan := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, LinearMap.domRestrict_apply, Polarization_apply]
  refine (mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)
  simp

theorem corootSpan_dualAnnihilator_le_ker_rootForm :
    P.corootSpan.dualAnnihilator.map P.toDualLeft.symm ≤ LinearMap.ker P.RootForm := by
  rw [← SetLike.coe_subset_coe, coe_corootSpan_dualAnnihilator_map]
  intro x hx
  simp only [coroot', PerfectPairing.flip_apply_apply, mem_setOf_eq] at hx
  ext y
  simp [rootForm_apply_apply, hx]

theorem rootSpan_dualAnnihilator_le_ker_rootForm :
    P.rootSpan.dualAnnihilator.map P.toDualRight.symm ≤ LinearMap.ker P.CorootForm :=
  P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

lemma prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈
      LinearMap.range (P.Polarization.domRestrict (P.rootSpan)) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨(c • 2 • P.root i), by aesop⟩
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

end Fintype

section IsValuedInOrdered

variable (S : Type*) [LinearOrderedCommRing S] [Algebra S R] [FaithfulSMul S R]
  [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] [Fintype ι] {i j : ι}

 [Module S N] [IsScalarTower S R N]

/-- Polarization restricted to `S`-span of roots. -/
def PolarizationIn : span S (range P.root) →ₗ[S] N :=
  ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in
lemma PolarizationIn_apply (x : span S (range P.root)) :
    P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i := by
  simp [PolarizationIn]

lemma PolarizationIn_eq (x : span S (range P.root)) :
    P.PolarizationIn S x = P.Polarization x := by
  simp only [PolarizationIn, LinearMap.coeFn_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply, PerfectPairing.flip_apply_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [algebra_compatible_smul R ((P.coroot'In S i) x) (P.coroot i), algebraMap_coroot'In_apply,
    PerfectPairing.flip_apply_apply]

/-- Polarization restricted to `S`-span of roots. -/
def CoPolarizationIn : span S (range P.coroot) →ₗ[S] M :=
  ∑ i, LinearMap.toSpanSingleton S M (P.root i) ∘ₗ P.root'In S i

omit [IsScalarTower S R M] in
lemma CoPolarizationIn_apply (x : span S (range P.coroot)) :
    P.CoPolarizationIn S x = ∑ i, P.root'In S i x • P.root i := by
  simp [CoPolarizationIn]

lemma CoPolarizationIn_eq (x : span S (range P.coroot)) :
    P.CoPolarizationIn S x = P.CoPolarization x := by
  simp [CoPolarizationIn]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [algebra_compatible_smul R ((P.root'In S i) x) (P.root i), algebraMap_root'In_apply]

/-- The bilinear form of a finite root pairing taking values in a linearly-ordered ring, as a
root-positive form. -/
def posRootForm : P.RootPositiveForm S where
  form := P.RootForm
  symm := P.rootForm_symmetric
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
  exists_eq i j := ⟨∑ k, P.pairingIn S i k * P.pairingIn S j k, by simp [rootForm_apply_apply]⟩
  exists_pos_eq i := by
    refine ⟨∑ k, P.pairingIn S i k ^ 2, ?_, by simp [sq, rootForm_apply_apply]⟩
    exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _) ⟨i, by simp⟩

omit [Module S N] [IsScalarTower S R N] in
lemma algebraMap_posRootForm_posForm (x y : span S (range P.root)) :
    (algebraMap S R) ((P.posRootForm S).posForm x y) = P.RootForm x y := by
  rw [RootPositiveForm.algebraMap_posForm]
  exact rfl

omit [Module S N] [IsScalarTower S R N] in
theorem exists_ge_zero_eq_rootForm (x : M) (hx : x ∈ span S (range P.root)) :
    ∃ s ≥ 0, algebraMap S R s = P.RootForm x x := by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSMul.algebraMap_injective S R
  simp only [posRootForm, RootPositiveForm.algebraMap_posForm, map_sum, map_mul]
  simp [← Algebra.linearMap_apply, hs, rootForm_apply_apply]

omit [Module S N] [IsScalarTower S R N] in
lemma posRootForm_posForm_apply_apply (x y : P.rootSpanIn S) : (P.posRootForm S).posForm x y =
    ∑ i, P.coroot'In S i x * P.coroot'In S i y := by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]

omit [Module S N] [IsScalarTower S R N] in
lemma zero_le_posForm (x : span S (range P.root)) :
    0 ≤ (P.posRootForm S).posForm x x := by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
    FaithfulSMul.algebraMap_injective S R <| (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

lemma toPerfectPairing_apply_PolarizationIn (x y : span S (range P.root)) :
    P.toPerfectPairing y (P.PolarizationIn S x) =
      (algebraMap S R) ((P.posRootForm S).posForm x y) := by
  rw [PolarizationIn_eq, algebraMap_posRootForm_posForm]
  exact toPerfectPairing_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in
lemma range_polarizationIn_le_span_coroot :
    LinearMap.range (P.PolarizationIn S) ≤ span S (range P.coroot) := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (mem_span_range_iff_exists_fun S).mpr (Exists.intro (fun i ↦ (P.coroot'In S i) y) hy)

/-- A version of SGA3 XXI Lemma 1.2.1 (10), adapted to change of rings. -/
lemma posRootForm_posForm_self_smul_coroot (i : ι) :
    ((P.posRootForm S).posForm (P.rootSpanMem S i)) (P.rootSpanMem S i) • P.coroot i =
      2 • P.PolarizationIn S (P.rootSpanMem S i) := by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflection_perm i)
          (fun j ↦ P.pairingIn S i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j))
          (fun j ↦ P.pairingIn S i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [PolarizationIn_apply]
  simp only [coroot'In_rootSpanMem_eq_pairingIn, pairingIn_reflection_perm,
    pairingIn_reflection_perm_self_left, ← reflection_perm_coroot, neg_smul, Finset.sum_neg_distrib,
    smul_sub, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add]
  simp only [posRootForm_posForm_apply_apply, coroot'In_rootSpanMem_eq_pairingIn,
    root_coroot_eq_pairing, ← P.algebraMap_pairingIn S, Finset.sum_neg_distrib, add_neg_cancel,
    IsScalarTower.algebraMap_smul, ← mul_smul]
  rw [Finset.sum_smul, sub_eq_zero]

lemma prod_posRootForm_posForm_smul_coroot_mem_range_PolarizationIn (i : ι) :
    (∏ j : ι, ((P.posRootForm S).posForm (P.rootSpanMem S j)) (P.rootSpanMem S j)) • P.coroot i ∈
      LinearMap.range (P.PolarizationIn S) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j ↦ ((P.posRootForm S).posForm (P.rootSpanMem S j)) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, posRootForm_posForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul, two_smul, two_smul, map_add]

omit [Fintype ι] [Module S N] [IsScalarTower S R N] in
lemma zero_lt_pairingIn_iff' [Finite ι] :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i :=
  let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j

end IsValuedInOrdered

end RootPairing
