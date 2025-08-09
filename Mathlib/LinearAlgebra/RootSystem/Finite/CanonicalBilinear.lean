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

namespace RootPairing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Fintype

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
  P.flip.Polarization

@[simp]
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.root' i x • P.root i :=
  P.flip.Polarization_apply x

lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization :=
  rfl

/-- An invariant inner product on the weight space. -/
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (P.coroot' i).smulRight (P.coroot' i)

/-- An invariant inner product on the coweight space. -/
def CorootForm : LinearMap.BilinForm R N :=
  P.flip.RootForm

lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ i, P.coroot' i x * P.coroot' i y := by
  simp [RootForm]

lemma corootForm_apply_apply (x y : N) : P.CorootForm x y =
    ∑ i, P.root' i x * P.root' i y :=
  P.flip.rootForm_apply_apply x y

lemma toPerfectPairing_apply_apply_Polarization (x y : M) :
    P.toPerfectPairing y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]

lemma toPerfectPairing_apply_CoPolarization (x : N) :
    P.toPerfectPairing (P.CoPolarization x) = P.CorootForm x := by
  ext y
  exact P.flip.toPerfectPairing_apply_apply_Polarization x y

lemma flip_comp_polarization_eq_rootForm :
    P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm := by
  ext; simp [rootForm_apply_apply, RootPairing.flip]

lemma self_comp_coPolarization_eq_corootForm :
    P.toLinearMap ∘ₗ P.CoPolarization = P.CorootForm :=
  P.flip.flip_comp_polarization_eq_rootForm

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
  simp [LinearMap.isSymm_def, mul_comm, rootForm_apply_apply]

@[simp]
lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflectionPerm i)
    (fun j ↦ (P.coroot' (P.reflectionPerm i j) x) * (P.coroot' (P.reflectionPerm i j) y))
    (fun j ↦ P.coroot' j x * P.coroot' j y) (congrFun rfl)

lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _

lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]

theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) ≤ P.corootSpan R := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, LinearMap.domRestrict_apply, Polarization_apply]
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)
  simp

theorem corootSpan_dualAnnihilator_le_ker_rootForm :
    (P.corootSpan R).dualAnnihilator.map P.toDualLeft.symm ≤ LinearMap.ker P.RootForm := by
  rw [P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  intro x hx
  ext y
  simp only [coroot', Submodule.mem_iInf, LinearMap.mem_ker, PerfectPairing.flip_apply_apply] at hx
  simp [rootForm_apply_apply, hx]

theorem rootSpan_dualAnnihilator_le_ker_rootForm :
    (P.rootSpan R).dualAnnihilator.map P.toDualRight.symm ≤ LinearMap.ker P.CorootForm :=
  P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

end Fintype

section IsValuedIn

variable (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [Module S N] [IsScalarTower S R N] [P.IsValuedIn S] [Fintype ι] {i j : ι}

/-- Polarization restricted to `S`-span of roots. -/
def PolarizationIn : P.rootSpan S →ₗ[S] N :=
  ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in
lemma PolarizationIn_apply (x : P.rootSpan S) :
    P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i := by
  simp [PolarizationIn]

lemma PolarizationIn_eq (x : P.rootSpan S) :
    P.PolarizationIn S x = P.Polarization x := by
  simp only [PolarizationIn, LinearMap.coeFn_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply, PerfectPairing.flip_apply_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [algebra_compatible_smul R (P.coroot'In S i x) (P.coroot i), algebraMap_coroot'In_apply,
    PerfectPairing.flip_apply_apply]

lemma range_polarizationIn :
    Submodule.map P.Polarization (P.rootSpan R) = LinearMap.range (P.PolarizationIn R) := by
  ext x
  simp [PolarizationIn_eq]

/-- Polarization restricted to `S`-span of roots. -/
def CoPolarizationIn : P.corootSpan S →ₗ[S] M :=
  P.flip.PolarizationIn S

omit [IsScalarTower S R M] in
lemma CoPolarizationIn_apply (x : P.corootSpan S) :
    P.CoPolarizationIn S x = ∑ i, P.root'In S i x • P.root i :=
  P.flip.PolarizationIn_apply S x

lemma CoPolarizationIn_eq (x : P.corootSpan S) :
    P.CoPolarizationIn S x = P.CoPolarization x :=
  P.flip.PolarizationIn_eq S x

/-- A canonical bilinear form on the span of roots in a finite root pairing, taking values in a
commutative ring, where the root-coroot pairing takes values in that ring. -/
def RootFormIn : LinearMap.BilinForm S (P.rootSpan S) :=
  ∑ i, (P.coroot'In S i).smulRight (P.coroot'In S i)

omit [Module S N] [IsScalarTower S R N] in
@[simp]
lemma algebraMap_rootFormIn (x y : P.rootSpan S) :
    (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y := by
  simp [RootFormIn, rootForm_apply_apply]

lemma toPerfectPairing_apply_PolarizationIn (x y : P.rootSpan S) :
    P.toPerfectPairing y (P.PolarizationIn S x) =
      (algebraMap S R) (P.RootFormIn S x y) := by
  rw [PolarizationIn_eq, algebraMap_rootFormIn]
  exact toPerfectPairing_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in
lemma range_polarizationIn_le_span_coroot :
    LinearMap.range (P.PolarizationIn S) ≤ P.corootSpan S := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (Submodule.mem_span_range_iff_exists_fun S).mpr
    (Exists.intro (fun i ↦ (P.coroot'In S i) y) hy)

/-- A version of SGA3 XXI Lemma 1.2.1 (10), adapted to change of rings. -/
lemma rootFormIn_self_smul_coroot (i : ι) :
    P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i) • P.coroot i =
      2 • P.PolarizationIn S (P.rootSpanMem S i) := by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflectionPerm i)
          (fun j ↦ P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j))
          (fun j ↦ P.pairingIn S i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [PolarizationIn_apply]
  simp only [coroot'In_rootSpanMem_eq_pairingIn, pairingIn_reflectionPerm,
    pairingIn_reflectionPerm_self_left, ← reflectionPerm_coroot, neg_smul,
    smul_sub, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add, RootFormIn]
  simp only [LinearMap.coeFn_sum, LinearMap.coe_smulRight, Finset.sum_apply,
    coroot'In_rootSpanMem_eq_pairingIn, LinearMap.smul_apply, smul_eq_mul, Finset.sum_smul,
    root_coroot_eq_pairing, Finset.sum_neg_distrib, add_neg_cancel, sub_eq_zero]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← P.algebraMap_pairingIn S, IsScalarTower.algebraMap_smul, ← mul_smul]

lemma prod_rootFormIn_smul_coroot_mem_range_PolarizationIn (i : ι) :
    (∏ j : ι, P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j)) • P.coroot i ∈
      LinearMap.range (P.PolarizationIn S) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j ↦ P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootFormIn_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul, two_smul, two_smul, map_add]

end IsValuedIn

section MoreFintype

variable [Fintype ι]

/-- A version of SGA3 XXI Lemma 1.2.1 (10). -/
lemma rootForm_self_smul_coroot (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have : (algebraMap R R) ((P.RootFormIn R) (P.rootSpanMem R i) (P.rootSpanMem R i)) • P.coroot i =
      2 • P.Polarization (P.root i) := by
    rw [Algebra.algebraMap_self_apply, P.rootFormIn_self_smul_coroot R i, PolarizationIn_eq]
  rw [← this, algebraMap_rootFormIn]

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
      apply (rootForm_symmetric P).eq, ← toPerfectPairing_apply_apply_Polarization,
      LinearMap.map_smul_of_tower]
  rw [sq, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul, hij, ← rootForm_self_smul_coroot,
    smul_mul_assoc 2, ← mul_smul_comm, hji, ← rootForm_self_smul_coroot, map_smul, ← pairing,
    map_smul, ← pairing, smul_eq_mul, smul_eq_mul, smul_eq_mul, coxeterWeight]
  ring

lemma prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈
      LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨c • 2 • P.root i, by aesop⟩
  simp

end MoreFintype

section IsValuedInOrdered

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [P.IsValuedIn S] [Fintype ι] {i j : ι}

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

lemma algebraMap_posRootForm_posForm (x y : span S (range P.root)) :
    (algebraMap S R) ((P.posRootForm S).posForm x y) = P.RootForm x y := by
  rw [RootPositiveForm.algebraMap_posForm]
  simp [posRootForm]

@[simp]
lemma posRootForm_eq :
    (P.posRootForm S).posForm = P.RootFormIn S := by
  ext
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_posRootForm_posForm, algebraMap_rootFormIn]

theorem exists_ge_zero_eq_rootForm (x : M) (hx : x ∈ span S (range P.root)) :
    ∃ s ≥ 0, algebraMap S R s = P.RootForm x x := by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSMul.algebraMap_injective S R
  simp only [posRootForm, RootPositiveForm.algebraMap_posForm, map_sum, map_mul]
  simp [hs, rootForm_apply_apply]

lemma posRootForm_posForm_apply_apply (x y : P.rootSpan S) : (P.posRootForm S).posForm x y =
    ∑ i, P.coroot'In S i x * P.coroot'In S i y := by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]

lemma zero_le_posForm (x : span S (range P.root)) :
    0 ≤ (P.posRootForm S).posForm x x := by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
    FaithfulSMul.algebraMap_injective S R <| (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

omit [Fintype ι]
variable [Finite ι]

lemma zero_lt_pairingIn_iff' :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i :=
  let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j

lemma pairingIn_lt_zero_iff :
    P.pairingIn S i j < 0 ↔ P.pairingIn S j i < 0 := by
  simpa using P.zero_lt_pairingIn_iff' S (i := i) (j := P.reflectionPerm j j)

lemma pairingIn_le_zero_iff [NeZero (2 : R)] [NoZeroSMulDivisors R M] :
    P.pairingIn S i j ≤ 0 ↔ P.pairingIn S j i ≤ 0 := by
  rcases eq_or_ne (P.pairingIn S i j) 0 with hij | hij <;>
  rcases eq_or_ne (P.pairingIn S j i) 0 with hji | hji
  · rw [hij, hji]
  · rw [hij, P.pairingIn_eq_zero_iff.mp hij]
  · rw [hji, P.pairingIn_eq_zero_iff.mp hji]
  · rw [le_iff_eq_or_lt, le_iff_eq_or_lt, or_iff_right hij, or_iff_right hji]
    exact P.pairingIn_lt_zero_iff S

end IsValuedInOrdered

end RootPairing
