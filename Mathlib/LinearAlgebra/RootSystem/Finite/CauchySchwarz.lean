/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# The Cauchy-Schwarz inequality for modules

Put this in `Mathlib.LinearAlgebra.BilinearForm.Properties`

## Main results:

 * Cauchy-Schwarz

-/

noncomputable section

open Set Function
open AddSubgroup (zmultiples)

variable {ι R M N : Type*}

namespace LinearMap

namespace BilinForm

lemma CS_aux [CommRing R] [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M) (x y : M) :
    B ((B x y) • x - (B x x) • y) ((B x y) • x - (B x x) • y) =
      (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
  simp only [LinearMap.map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_sub]
  ring

lemma zero_le_inner_self_mul [LinearOrderedCommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hs : ∀ x, 0 ≤ B x x) (x y : M) :
    0 ≤ (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
  rw [← CS_aux B x y]
  exact hs ((B x) y • x - (B x) x • y)

lemma inner_mul_inner_self_le [LinearOrderedCommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (x y : M) :
    (B x y) * (B y x) ≤ (B x x) * (B y y) := by
  by_cases hx : x = 0
  · simp [hx]
  · refine sub_nonneg.mp <| nonneg_of_mul_nonneg_right
      (zero_le_inner_self_mul B (fun z => ?_) x y) (hp x hx)
    by_cases h0 : z = 0
    · simp [h0]
    · exact le_of_lt <| hp z h0

lemma not_LinearIndependent_of_inner_mul_eq [LinearOrderedCommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M) (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (x y : M) (he : (B x y) * (B y x) = (B x x) * (B y y)) :
    ¬ LinearIndependent R ![x, y] := by
  have hl : B ((B x y) • x - (B x x) • y) ((B x y) • x - (B x x) • y) = 0 :=
    (CS_aux B x y).symm ▸ (mul_eq_zero_of_right ((B x) x) (sub_eq_zero_of_eq he.symm))
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
    exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm hl
  by_contra hL
  by_cases hx : x = 0
  · have := LinearIndependent.ne_zero 0 hL
    simp_all
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg, ← neg_smul, add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2

lemma inner_mul_lt_inner_self [LinearOrderedCommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hp : ∀ x, x ≠ 0 → 0 < B x x) (x y : M)
    (hxy : LinearIndependent R ![x, y]) :
    (B x y) * (B y x) < (B x x) * (B y y) := by
  refine lt_of_le_of_ne (inner_mul_inner_self_le B hp x y) ?_
  by_contra h
  apply (not_LinearIndependent_of_inner_mul_eq B hp x y h) hxy

end BilinForm

end LinearMap

namespace RootPairing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

lemma four_inner_mul (i j : ι) :
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
    rw [P.four_inner_mul i j]
    exact (mul_lt_mul_left (Left.mul_pos (rootForm_root_self_pos P i)
      (rootForm_root_self_pos P j))).mpr h
  have h2 : (P.RootForm (P.root i)) (P.root i) * (P.RootForm (P.root j)) (P.root j) <
      (P.RootForm (P.root i)) (P.root j) * (P.RootForm (P.root j)) (P.root i) := by
    rw [nsmul_eq_mul, mul_comm, mul_assoc] at h1
    exact (mul_lt_mul_left (by simp)).mp h1
  have h3 := nonneg_of_mul_nonneg_right (LinearMap.BilinForm.zero_le_inner_self_mul P.RootForm
      P.rootForm_self_non_neg (P.root i) (P.root j)) (rootForm_root_self_pos P i)
  linarith

lemma coxeterWeight_Icc (i j : ι) (hP : P.IsCrystallographic) (hO : ¬ P.IsOrthogonal i j)
    (h : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j = 1 ∨ P.coxeterWeight i j = 2 ∨ P.coxeterWeight i j = 3 := by
  have h4 := P.coxeterWeight_le_4 i j
  have hn := P.coxeterWeight_non_neg P.RootForm i j
  have hC := P.isCrystallographic_iff.mp hP
  obtain ⟨ij, hij⟩ := hC i j
  obtain ⟨ji, hji⟩ := hC j i
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
  have : ∃ (n : ℕ), P.coxeterWeight i j = n := by
    have : (0 : ℤ) ≤ ij * ji := by
      rw [ht, ← Int.cast_mul, ← Int.cast_zero, Int.cast_le] at hn
      exact hn
    rw [ht, ← Int.cast_mul]
    lift (ij * ji) to ℕ with k
    · exact this
    · use k
      norm_cast
  obtain ⟨n, hcn⟩ := this
  simp only [hcn] at *
  norm_cast at *
  omega

end RootPairing
