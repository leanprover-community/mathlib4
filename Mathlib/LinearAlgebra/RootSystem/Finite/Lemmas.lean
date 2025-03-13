/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.NumberTheory.Divisors

/-!
# Structural lemmas about finite crystallographic root pairings

In this file we gather basic lemmas necessary for the classification of finite crystallographic
root pairings.

## Main results:

 * `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`: the Coxeter weights of a finite
   crystallographic root pairing belong to the set `{0, 1, 2, 3, 4}`.
 * `RootPairing.root_sub_root_mem_of_pairingIn_pos`: if `α ≠ β` are both roots of a finite
   crystallographic root pairing, and the pairing of `α` with `β` is positive, then `α - β` is also
   a root.
 * `RootPairing.root_add_root_mem_of_pairingIn_neg`: if `α ≠ -β` are both roots of a finite
   crystallographic root pairing, and the pairing of `α` with `β` is negative, then `α + β` is also
   a root.

-/

noncomputable section

open Function Set
open Submodule (span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable (P : RootPairing ι R M N) [Finite ι]

local notation "Φ" => range P.root
local notation "α" => P.root

/-- SGA3 XXI Prop. 2.3.1 -/
lemma coxeterWeightIn_le_four (S : Type*) [LinearOrderedCommRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] (i j : ι) :
    P.coxeterWeightIn S i j ≤ 4 := by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).posForm ri ri
  set lj := (P.posRootForm S).posForm rj rj
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
  replace hsi' : si = li := algebraMap_injective S R <| by simpa [li] using hsi'
  replace hsj' : sj = lj := algebraMap_injective S R <| by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 ≤ 4 * (li * lj) := by
    rw [mul_le_mul_left four_pos]
    refine (P.posRootForm S).posForm.apply_sq_le_of_symm ?_ (P.posRootForm S).isSymm_posForm ri rj
    intro x
    obtain ⟨s, hs, hs'⟩ := P.exists_ge_zero_eq_rootForm S x x.property
    change _ = (P.posRootForm S).form x x at hs'
    rw [(P.posRootForm S).algebraMap_apply_eq_form_iff] at hs'
    rwa [← hs']
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_right (by positivity)] at cs

variable [CharZero R] [P.IsCrystallographic] (i j : ι)

lemma coxeterWeightIn_mem_set_of_isCrystallographic :
    P.coxeterWeightIn ℤ i j ∈ ({0, 1, 2, 3, 4} : Set ℤ) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : ∃ n : ℕ, P.coxeterWeightIn ℤ i j = n := by
    have : 0 ≤ P.coxeterWeightIn ℤ i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm ℤ) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [← P.algebraMap_coxeterWeightIn ℤ, hn]⟩
  have : P.coxeterWeightIn ℤ i j ≤ 4 := P.coxeterWeightIn_le_four ℤ i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  omega

variable [NoZeroDivisors R]

lemma pairingIn_pairingIn_mem_set_of_isCrystallographic :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  have : Fintype ι := Fintype.ofFinite ι
  simpa [← P.algebraMap_pairingIn ℤ] using pairing_zero_iff (P.posRootForm ℤ) i j

lemma pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced
    [P.IsReduced] [NoZeroSMulDivisors R M] :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (P.root i) (-P.root j) with h₂ | h₂; · aesop
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn ℤ i j * P.pairingIn ℤ j i ≠ 4 := P.coxeterWeightIn_ne_four ℤ h₁ h₂
  aesop

lemma coxeterWeightIn_eq_zero_iff :
    P.coxeterWeightIn ℤ i j = 0 ↔ P.pairingIn ℤ i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [coxeterWeightIn, h, zero_mul]⟩
  have : Fintype ι := Fintype.ofFinite ι
  rwa [← (algebraMap_injective ℤ R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    P.coxeterWeight_zero_iff_isOrthogonal (P.posRootForm ℤ), IsOrthogonal,
    P.pairing_zero_iff (P.posRootForm ℤ) j i, and_self, ← P.algebraMap_pairingIn ℤ,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

variable [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N]
variable {i j}

lemma root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn ℤ i j) (h' : i ≠ j) :
    α i - α j ∈ Φ := by
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn ℤ i j = 1 ∨ P.pairingIn ℤ j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        exact ⟨P.reflection_perm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        rw [← neg_mem_range_root_iff, neg_sub]
        exact ⟨P.reflection_perm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn ℤ i j ∈ ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P ℤ).mp hli
      have aux₃ : P.coxeterWeightIn ℤ i j ≠ 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      aesop
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    omega
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hli
      aesop
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff ℤ i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff ℤ j i).mp hij, two_smul]

lemma root_add_root_mem_of_pairingIn_neg (h : P.pairingIn ℤ i j < 0) (h' : α i ≠ - α j) :
    α i + α j ∈ Φ := by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn ℤ i (-j) := by simpa
  replace h' : i ≠ -j := by contrapose! h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

section RootForm

omit [Finite ι] [NoZeroSMulDivisors R N]
variable [Fintype ι] [P.IsReduced] [P.IsIrreducible]

-- TODO Prove for any invariant form (valued in appropriate scalars) rather than just `RootForm`

-- I think best to break this lemma in three:
-- First part which assumes `P.pairingIn ℤ i j ≠ 0` (but not irreducible) and second which
-- has assumptions as shown. With third part doing the Weyl group argument.
open LinearMap MulAction in
lemma foo (i j : ι) :
    P.RootForm (P.root i) (P.root i) = P.RootForm (P.root j) (P.root j) ∨
    P.RootForm (P.root i) (P.root i) = 2 * P.RootForm (P.root j) (P.root j) ∨
    P.RootForm (P.root i) (P.root i) = 3 * P.RootForm (P.root j) (P.root j) ∨
    P.RootForm (P.root j) (P.root j) = 2 * P.RootForm (P.root i) (P.root i) ∨
    P.RootForm (P.root j) (P.root j) = 3 * P.RootForm (P.root i) (P.root i) := by
  obtain ⟨j', h₁, h₂⟩ : ∃ j',
      P.RootForm (P.root j') (P.root j') = P.RootForm (P.root j) (P.root j) ∧
      P.RootForm (P.root i) (P.root j') ≠ 0 := by
    -- TODO Probably break this out into its own lemma
    have := P.span_orbit_eq_top j
    contrapose! this
    replace this : span R (orbit P.weylGroup (P.root j)) ≤ ker (P.RootForm (P.root i)) := by
      refine Submodule.span_le.mpr fun v hv ↦ ?_
      obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
      rw [P.weylGroup_apply_root]
      simp only [MonoidHom.restrict_apply, Equiv.indexHom_apply]
      specialize this (P.weylGroupToPerm g j)
      simp only [MonoidHom.restrict_apply, Equiv.indexHom_apply] at this
      apply this
      suffices P.root ((g : P.Aut).indexEquiv j) = g • P.root j by simp [this]
      exact (RootPairing.Equiv.smul_root P j g).symm
    intro contra
    replace this : P.RootForm (P.root i) (P.root i) = 0 := by
      suffices P.RootForm (P.root i) = 0 by simp [this]
      simpa [contra] using this
    exact IsAnisotropic.rootForm_root_ne_zero i this
  replace h₂ : P.pairingIn ℤ i j' ≠ 0 := by
    contrapose! h₂
    replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn ℤ, h₂, map_zero]
    exact (P.apply_root_root_zero_iff (P.posRootForm ℤ) i j').mpr h₂
  have h₃ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced i j'
  -- have h₄ := P.qux i j'
  have h₄ : P.pairingIn ℤ j' i * P.RootForm (P.root i) (P.root i) =
            P.pairingIn ℤ i j' * P.RootForm (P.root j') (P.root j') := by
    change (algebraMap ℤ R (P.pairingIn ℤ j' i)) * _ = (algebraMap ℤ R (P.pairingIn ℤ i j')) * _
    simpa only [algebraMap_pairingIn] using pairing_mul_eq_pairing_mul_swap' P i j'
  aesop

instance : CancelMonoidWithZero R := by constructor -- Grr

-- Also worth having version of this which makes statement about just two values of
-- `P.pairing` with no mention of root form.
open Submodule in
/-- A reduced irreducible finite crystallographic root system has roots of at most two different
lengths. -/
lemma bar [Nonempty ι] : ∃ i j, ∀ k,
    P.RootForm (P.root k) (P.root k) = P.RootForm (P.root i) (P.root i) ∨
    P.RootForm (P.root k) (P.root k) = P.RootForm (P.root j) (P.root j) := by
  obtain ⟨i⟩ := inferInstanceAs (Nonempty ι)
  by_cases h : (∀ j, P.RootForm (P.root j) (P.root j) = P.RootForm (P.root i) (P.root i))
  · refine ⟨i, i, fun j ↦ by simp [h j]⟩
  · push_neg at h
    obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k ↦ ?_⟩
    by_contra! hk
    obtain ⟨hki_ne, hkj_ne⟩ := hk
    have hij := (P.foo i j).resolve_left hji_ne.symm
    have hik := (P.foo i k).resolve_left hki_ne.symm
    have hjk := (P.foo j k).resolve_left hkj_ne.symm
    -- Sigh: blob of boilerplate to break through to `omega`
    -- Probably the right thing here is for this lemma and the one above to work with
    -- a new `lengthIn` function that is `ℤ`-valued.
    let r (p : ι) : span ℤ (range P.root) := ⟨P.root p, subset_span (mem_range_self p)⟩
    let l (p : ι) : ℤ := (P.posRootForm ℤ).posForm (r p) (r p)
    have aux₀ (p : ι) : _ = P.RootForm (P.root p) (P.root p) :=
      (P.posRootForm ℤ).algebraMap_posForm (x := r p) (y := r p)
    have aux₁ (z : ℤ) (n : ℕ) [n.AtLeastTwo] :
        ofNat(n) * algebraMap ℤ R z = algebraMap ℤ R (n * z) := by simp; left; rfl
    have aux₂ : l j ≠ l i ∧ l k ≠ l i ∧ l k ≠ l j := by
      simp only [← (FaithfulSMul.algebraMap_injective ℤ R).ne_iff,
        RootPositiveForm.algebraMap_posForm, posRootForm, r, l]
      tauto
    simp only [← aux₀, aux₁, (FaithfulSMul.algebraMap_injective ℤ R).eq_iff] at hij hik hjk
    simp only [l] at aux₂
    omega

end RootForm

namespace Base

variable {P}
variable (b : P.Base) (i j k : ι) (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support)
include b hij hi hj

variable {i j} in
lemma pairingIn_le_zero_of_ne :
    P.pairingIn ℤ i j ≤ 0 := by
  by_contra! h
  exact b.sub_nmem_range_root hi hj <| P.root_sub_root_mem_of_pairingIn_pos h hij

/-- This is Lemma 2.5 (a) from [Geck](Geck2017). -/
lemma root_sub_root_mem_of_mem_of_mem (hk : α k + α i - α j ∈ Φ)
    (hkj : k ≠ j) (hk' : α k + α i ∈ Φ) :
    α k - α j ∈ Φ := by
  rcases lt_or_le 0 (P.pairingIn ℤ j k) with hm | hm
  · rw [← neg_mem_range_root_iff, neg_sub]
    exact P.root_sub_root_mem_of_pairingIn_pos hm hkj.symm
  obtain ⟨l, hl⟩ := hk
  have hli : l ≠ i := by
    rintro rfl
    rw [add_comm, add_sub_assoc, left_eq_add, sub_eq_zero, P.root.injective.eq_iff] at hl
    exact hkj hl
  suffices 0 < P.pairingIn ℤ l i by
    convert P.root_sub_root_mem_of_pairingIn_pos this hli using 1
    rw [hl]
    module
  have hkl : l ≠ k := by rintro rfl; exact hij <| by simpa [add_sub_assoc, sub_eq_zero] using hl
  replace hkl : P.pairingIn ℤ l k ≤ 0 := by
    suffices α l - α k ∉ Φ by contrapose! this; exact P.root_sub_root_mem_of_pairingIn_pos this hkl
    replace hl : α l - α k = α i - α j := by rw [hl]; module
    rw [hl]
    exact b.sub_nmem_range_root hi hj
  have hki : P.pairingIn ℤ i k ≤ -2 := by
    suffices P.pairingIn ℤ l k = 2 + P.pairingIn ℤ i k - P.pairingIn ℤ j k by linarith
    apply algebraMap_injective ℤ R
    simp only [algebraMap_pairingIn, map_sub, map_add, map_ofNat]
    simpa using (P.coroot' k : M →ₗ[R] R).congr_arg hl
  replace hki : P.pairingIn ℤ k i = -1 := by
    replace hk' : α i ≠ - α k := by
      rw [← sub_ne_zero, sub_neg_eq_add, add_comm]
      intro contra
      rw [contra] at hk'
      exact P.ne_zero _ hk'.choose_spec
    have aux (h : P.pairingIn ℤ i k = -2) : ¬P.pairingIn ℤ k i = -2 := by
      contrapose! hk'; exact (P.pairingIn_neg_two_neg_two_iff ℤ i k).mp ⟨h, hk'⟩
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i k
    aesop
  replace hki : P.pairing k i = -1 := by rw [← P.algebraMap_pairingIn ℤ, hki]; simp
  have : P.pairingIn ℤ l i = 1 - P.pairingIn ℤ j i := by
    apply algebraMap_injective ℤ R
    simp only [algebraMap_pairingIn, map_sub, map_one, algebraMap_pairingIn]
    convert (P.coroot' i : M →ₗ[R] R).congr_arg hl using 1
    simp only [PerfectPairing.flip_apply_apply, map_sub, map_add, LinearMap.sub_apply,
      LinearMap.add_apply, root_coroot_eq_pairing, hki, pairing_same]
    ring
  replace hij := pairingIn_le_zero_of_ne b hij.symm hj hi
  omega

/-- This is Lemma 2.5 (b) from [Geck](Geck2017). -/
lemma root_add_root_mem_of_mem_of_mem (hk : α k + α i - α j ∈ Φ)
    (hkj : α k ≠ - α i) (hk' : α k - α j ∈ Φ) :
    α k + α i ∈ Φ := by
  let _i := P.indexNeg
  replace hk : α (-k) + α j - α i ∈ Φ := by
    rw [← neg_mem_range_root_iff]
    convert hk using 1
    simp only [indexNeg_neg, root_reflection_perm, reflection_apply_self]
    module
  rw [← neg_mem_range_root_iff]
  convert b.root_sub_root_mem_of_mem_of_mem j i (-k) hij.symm hj hi hk (by aesop)
    (by convert P.neg_mem_range_root_iff.mpr hk' using 1; simp [neg_add_eq_sub]) using 1
  simp only [indexNeg_neg, root_reflection_perm, reflection_apply_self]
  module

end Base

end RootPairing
