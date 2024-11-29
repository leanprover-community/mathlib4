/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# Nondegeneracy of the polarization on a finite root pairing

We show that if the base ring of a finite root pairing is linearly ordered, then the canonical
bilinear form is root-positive and positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4.  Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`.  Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main results:
 * `RootPairing.rootForm_rootPositive`: `RootForm` is root-positive.
 * `RootPairing.polarization_domRestrict_injective`: The polarization restricted to the span of
   roots is injective.
 * `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.

## References:
 * [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 4--6*][bourbaki1968]
 * [M. Demazure, *SGA III, Expos\'{e} XXI, Don\'{e}es Radicielles*][demazure1970]

## Todo
 * Weyl-invariance of `RootForm` and `CorootForm`
 * Faithfulness of Weyl group perm action, and finiteness of Weyl group, over ordered rings.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.
-/

noncomputable section

open Set Function
open Module hiding reflection
open Submodule (span)

namespace RootPairing

variable {ι R M N : Type*}

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

instance rootForm_rootPositive : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply

instance : Module.Finite R P.rootSpan := Finite.span_of_finite R <| finite_range P.root

instance : Module.Finite R P.corootSpan := Finite.span_of_finite R <| finite_range P.coroot

@[simp]
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R (P.rootSpan.map P.Polarization) = finrank R P.corootSpan := by
  rw [← LinearMap.range_domRestrict]
  apply (Submodule.finrank_mono P.range_polarization_domRestrict_le_span_coroot).antisymm
  have : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine LinearMap.finrank_le_of_isSMulRegular P.corootSpan
    (LinearMap.range (P.Polarization.domRestrict P.rootSpan))
    (smul_right_injective N (Ne.symm (ne_of_lt P.prod_rootForm_root_self_pos)))
    fun _ hx => ?_
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range (P.Polarization.domRestrict P.rootSpan)) c
    (fun c _ ↦ prod_rootForm_smul_coroot_mem_range_domRestrict P c)

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq`. -/
private lemma finrank_corootSpan_le :
    finrank R P.corootSpan ≤ finrank R P.rootSpan := by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization P.rootSpan

lemma finrank_corootSpan_eq :
    finrank R P.corootSpan = finrank R P.rootSpan :=
  le_antisymm P.finrank_corootSpan_le P.flip.finrank_corootSpan_le

lemma disjoint_rootSpan_ker_polarization :
    Disjoint P.rootSpan (LinearMap.ker P.Polarization) := by
  have : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
  refine Submodule.disjoint_ker_of_finrank_eq (L := P.rootSpan) P.Polarization ?_
  rw [finrank_rootSpan_map_polarization_eq_finrank_corootSpan, finrank_corootSpan_eq]

lemma mem_ker_polarization_of_rootForm_self_eq_zero {x : M} (hx : P.RootForm x x = 0) :
    x ∈ LinearMap.ker P.Polarization := by
  rw [LinearMap.mem_ker, Polarization_apply]
  rw [rootForm_self_zero_iff] at hx
  exact Fintype.sum_eq_zero _ fun i ↦ by simp [hx i]

lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x ∈ P.rootSpan) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  rw [← Submodule.mem_bot (R := R), ← P.disjoint_rootSpan_ker_polarization.eq_bot]
  exact ⟨hx, P.mem_ker_polarization_of_rootForm_self_eq_zero hx'⟩

lemma _root_.RootSystem.rootForm_anisotropic (P : RootSystem ι R M N) :
    P.RootForm.toQuadraticMap.Anisotropic :=
  fun x ↦ P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero <| by
    simpa only [rootSpan, P.span_eq_top] using Submodule.mem_top

lemma rootForm_pos_of_nonzero {x : M} (hx : x ∈ P.rootSpan) (h : x ≠ 0) :
    0 < P.RootForm x x := by
  apply (P.rootForm_self_non_neg x).lt_of_ne
  contrapose! h
  exact eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero P hx h.symm

lemma rootForm_restrict_nondegenerate :
    (P.RootForm.restrict P.rootSpan).Nondegenerate :=
  LinearMap.IsRefl.nondegenerate_of_separatingLeft (LinearMap.IsSymm.isRefl fun x y => by
    simp [rootForm_apply_apply, mul_comm]) fun x h => SetLike.coe_eq_coe.mp
    (P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero (Submodule.coe_mem x) (h x))

lemma four_smul_rootForm_mul_rootForm (i j : ι) :
    4 • P.RootForm (P.root i) (P.root j) * P.RootForm (P.root j) (P.root i) =
    P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j) * P.coxeterWeight i j := by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toPerfectPairing (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← Polarization_apply_apply, LinearMap.map_smul_of_tower, ← smul_assoc, Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root j)) (P.root i) =
      P.toPerfectPairing (P.root i) (2 • P.Polarization (P.root j)) := by
    rw [← Polarization_apply_apply, LinearMap.map_smul_of_tower]
  rw [hij, ← rootForm_self_smul_coroot, smul_mul_assoc 2, ← mul_smul_comm, hji,
    ← rootForm_self_smul_coroot, map_smul, ← pairing, map_smul, ← pairing, smul_eq_mul, smul_eq_mul,
    coxeterWeight]
  ring

/-- SGA3 XXI Prop. 2.3.1 -/
lemma coxeterWeight_le_4 (i j : ι) : P.coxeterWeight i j ≤ 4 := by
  by_contra h
  rw [not_le] at h
  have h1 : (P.RootForm (P.root i)) (P.root i) * (P.RootForm (P.root j)) (P.root j) * 4 <
      4 • (P.RootForm (P.root i)) (P.root j) * (P.RootForm (P.root j)) (P.root i) := by
    rw [P.four_smul_rootForm_mul_rootForm i j]
    exact (mul_lt_mul_left (Left.mul_pos (rootForm_root_self_pos P i)
      (rootForm_root_self_pos P j))).mpr h
  have h2 : (P.RootForm (P.root i)) (P.root i) * (P.RootForm (P.root j)) (P.root j) <
      (P.RootForm (P.root i)) (P.root j) * (P.RootForm (P.root j)) (P.root i) := by
    rw [nsmul_eq_mul, mul_comm, mul_assoc] at h1
    exact (mul_lt_mul_left (by simp)).mp h1
  have h3 := LinearMap.BilinForm.inner_mul_inner_le P.RootForm P.rootForm_self_non_neg
    (rootForm_root_self_pos P i) (P.root j)
  linarith

lemma coxeterWeight123 (i j : ι) (hP : P.IsCrystallographic) (hO : ¬ P.IsOrthogonal i j)
    (h : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j = 1 ∨ P.coxeterWeight i j = 2 ∨ P.coxeterWeight i j = 3 := by
  obtain ⟨ij, hij⟩ := P.isCrystallographic_iff.mp hP i j
  obtain ⟨ji, hji⟩ := P.isCrystallographic_iff.mp hP j i
  have hn0 : P.coxeterWeight i j ≠ 0 := by
    by_contra hc
    apply hO ((P.coxeterWeight_zero_iff_isOrthogonal P.RootForm i j).mp hc)
  have ht : P.coxeterWeight i j = ij * ji := Eq.symm (Mathlib.Tactic.Ring.mul_congr hij hji rfl)
  have hn4 : P.coxeterWeight i j ≠ 4 := by
    by_contra hc
    have : Module.IsReflexive R M := P.toPerfectPairing.reflexive_left
    have : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
    have := P.infinite_of_linearly_independent_coxeterWeight_four i j h hc --needs NoZeroSMul ℤ M
    simp_all only [not_or, ← isEmpty_fintype, isEmpty_iff]
  have : ∃ (n : ℕ), P.coxeterWeight i j = n := by -- this should be easier
    have : (0 : ℤ) ≤ ij * ji := by
      have hn := P.coxeterWeight_non_neg P.RootForm i j
      rwa [ht, ← Int.cast_mul, ← Int.cast_zero, Int.cast_le] at hn
    rw [ht, ← Int.cast_mul]
    lift (ij * ji) to ℕ with k
    · exact this
    · use k
      norm_cast
  obtain ⟨n, hcn⟩ := this
  have h4 := P.coxeterWeight_le_4 i j
  simp only [hcn] at *
  norm_cast at *
  omega

end RootPairing
