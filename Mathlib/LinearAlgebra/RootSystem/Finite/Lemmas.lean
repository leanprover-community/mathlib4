/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Irreducible

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

#adaptation_note /-- 2025-08-10 add back `import Mathlib.Algebra.Ring.Torsion` after
  https://github.com/leanprover/lean4/issues/9825 is fixed -/

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
lemma coxeterWeightIn_le_four (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] (i j : ι) :
    P.coxeterWeightIn S i j ≤ 4 := by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
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
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn ℤ i j ≤ 4 := P.coxeterWeightIn_le_four ℤ i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  omega

variable [IsDomain R]

lemma pairingIn_pairingIn_mem_set_of_isCrystallographic :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn ℤ] using P.pairing_eq_zero_iff' (i := i) (j := j)

lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  have := P.reflexive_left
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · aesop
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn ℤ i j * P.pairingIn ℤ j i ≠ 4 := P.coxeterWeightIn_ne_four ℤ h₁ h₂
  aesop -- #24551 (this should be faster)

lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced]
    (hij : α i ≠ α j) (hij' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1)} : Set (ℤ × ℤ)) := by
  have := P.reflexive_left
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  aesop

variable {P} in
lemma RootPositiveForm.rootLength_le_of_pairingIn_eq (B : P.RootPositiveForm ℤ) {i j : ι}
    (hij : P.pairingIn ℤ i j = -1 ∨ P.pairingIn ℤ i j = 1) :
    B.rootLength i ≤ B.rootLength j := by
  have h : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (ℤ × ℤ)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- #24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1, hij'.2] at h' <;> omega

variable {P} in
lemma RootPositiveForm.rootLength_lt_of_pairingIn_notMem
    (B : P.RootPositiveForm ℤ) {i j : ι}
    (hne : α i ≠ α j) (hne' : α i ≠ -α j)
    (hij : P.pairingIn ℤ i j ∉ ({-1, 0, 1} : Set ℤ)) :
    B.rootLength j < B.rootLength i := by
  have hij' : P.pairingIn ℤ i j = -3 ∨ P.pairingIn ℤ i j = -2 ∨ P.pairingIn ℤ i j = 2 ∨
      P.pairingIn ℤ i j = 3 ∨ P.pairingIn ℤ i j = -4 ∨ P.pairingIn ℤ i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- #24551 (this should be faster)
  have aux₁ : P.pairingIn ℤ j i = -1 ∨ P.pairingIn ℤ j i = 1 := by
    have _i := P.reflexive_left
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- #24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji, hij'] at aux₂ <;> omega

@[deprecated (since := "2025-05-23")]
alias RootPositiveForm.rootLength_lt_of_pairingIn_nmem :=
  RootPositiveForm.rootLength_lt_of_pairingIn_notMem

variable {i j} in
lemma pairingIn_pairingIn_mem_set_of_length_eq {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j)) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  replace len_eq : P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
    simp only [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- #24551 (this should be faster)

variable {i j} in
lemma pairingIn_pairingIn_mem_set_of_length_eq_of_ne {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j))
    (ne : i ≠ j) (ne' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(0, 0), (1, 1), (-1, -1)} : Set (ℤ × ℤ)) := by
  have := P.reflexive_left
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  aesop

omit [Finite ι] in
lemma coxeterWeightIn_eq_zero_iff :
    P.coxeterWeightIn ℤ i j = 0 ↔ P.pairingIn ℤ i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective ℤ R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn ℤ,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

variable {i j}

lemma root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn ℤ i j) (h' : i ≠ j) :
    α i - α j ∈ Φ := by
  have := P.reflexive_left
  have := P.reflexive_right
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn ℤ i j = 1 ∨ P.pairingIn ℤ j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        rw [← neg_mem_range_root_iff, neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
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
      aesop -- #24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff ℤ i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff ℤ j i).mp hij, two_smul]

/-- If two roots make an obtuse angle then their sum is a root (provided it is not zero).

See `RootPairing.pairingIn_le_zero_of_root_add_mem` for a partial converse. -/
lemma root_add_root_mem_of_pairingIn_neg (h : P.pairingIn ℤ i j < 0) (h' : α i ≠ -α j) :
    α i + α j ∈ Φ := by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn ℤ i (-j) := by simpa
  replace h' : i ≠ -j := by contrapose! h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

omit [Finite ι] in
lemma root_mem_submodule_iff_of_add_mem_invtSubmodule
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N] {P : RootPairing ι K M N}
    (q : P.invtRootSubmodule)
    (hij : P.root i + P.root j ∈ range P.root) :
    P.root i ∈ (q : Submodule K M) ↔ P.root j ∈ (q : Submodule K M) := by
  obtain ⟨q, hq⟩ := q
  rw [mem_invtRootSubmodule_iff] at hq
  suffices ∀ i j, P.root i + P.root j ∈ range P.root → P.root i ∈ q → P.root j ∈ q by
    have aux := this j i (by rwa [add_comm]); tauto
  rintro i j ⟨k, hk⟩ hi
  rcases eq_or_ne (P.pairing i j) 0 with hij₀ | hij₀
  · have hik : P.pairing i k ≠ 0 := by
      rw [ne_eq, P.pairing_eq_zero_iff, ← root_coroot_eq_pairing, hk]
      simpa [P.pairing_eq_zero_iff.mp hij₀] using two_ne_zero
    suffices P.root k ∈ q from (q.add_mem_iff_right hi).mp <| hk ▸ this
    replace hq : P.root i - P.pairing i k • P.root k ∈ q := by
      simpa [reflection_apply_root] using hq k hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hik] at hq
  · replace hq : P.root i - P.pairing i j • P.root j ∈ q := by
      simpa [reflection_apply_root] using hq j hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hij₀] at hq

namespace InvariantForm

variable [P.IsReduced] (B : P.InvariantForm)
variable {P}

lemma apply_eq_or_aux (i j : ι) (h : P.pairingIn ℤ i j ≠ 0) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  have := P.reflexive_left
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have h₂ : algebraMap ℤ R (P.pairingIn ℤ j i) * B.form (α i) (α i) =
            algebraMap ℤ R (P.pairingIn ℤ i j) * B.form (α j) (α j) := by
    simpa only [algebraMap_pairingIn] using B.pairing_mul_eq_pairing_mul_swap i j
  aesop -- #24551 (this should be faster)

variable [P.IsIrreducible]

/-- Relative of lengths of roots in a reduced irreducible finite crystallographic root pairing are
very constrained. -/
lemma apply_eq_or (i j : ι) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn ℤ i j' ≠ 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose! h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn ℤ, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

#adaptation_note /-- 2025-08-10 delete this after
  https://github.com/leanprover/lean4/issues/9825 is fixed -/
theorem exists_apply_eq_or_aux {x y z : R}
    (hij : x = 2 * y ∨ x = 3 * y ∨ y = 2 * x ∨ y = 3 * x)
    (hik : x = 2 * z ∨ x = 3 * z ∨ z = 2 * x ∨ z = 3 * x)
    (hjk : y = 2 * z ∨ y = 3 * z ∨ z = 2 * y ∨ z = 3 * y) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  /- The below proof (due to Mario Carneiro, Johan Commelin, Bhavik Mehta, Jingting Wang) should
     not really be necessary: we should have a tactic to crush this. -/
  suffices y = 0 ∨ z = 0 by apply this.elim <;> rintro rfl <;> simp_all
  let S : Finset (ℕ × ℕ) := {(1, 2), (1, 3), (2, 1), (3, 1)}
  obtain ⟨⟨ab, hab, hxy⟩, ⟨cd, hcd, hxz⟩, ⟨ef, hef, hyz⟩⟩ :
    (∃ ab ∈ S, ab.1 * x = ab.2 * y) ∧
    (∃ cd ∈ S, cd.1 * x = cd.2 * z) ∧
    (∃ ef ∈ S, ef.1 * y = ef.2 * z) := by
    simp_all only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, Nat.cast_one, one_mul,
      Nat.cast_ofNat, eq_comm, exists_eq_left, and_self, S]
  have : (ab.1 * cd.2 * ef.1 : R) ≠ ab.2 * cd.1 * ef.2 := by norm_cast; clear! R; decide +revert
  have : (ab.1 * cd.2 * ef.1 - ab.2 * cd.1 * ef.2) * (y * z) = 0 := by
    linear_combination z * cd.1 * ef.2 * hxy - ab.1 * ef.1 * y * hxz + ab.1 * x * cd.1 * hyz
  simp_all only [ne_eq, mul_eq_zero, sub_eq_zero, false_or, S]

/-- A reduced irreducible finite crystallographic root system has roots of at most two different
lengths. -/
lemma exists_apply_eq_or [Nonempty ι] : ∃ i j, ∀ k,
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  obtain ⟨i⟩ := inferInstanceAs (Nonempty ι)
  by_cases h : (∀ j, B.form (α j) (α j) = B.form (α i) (α i))
  · refine ⟨i, i, fun j ↦ by simp [h j]⟩
  · push_neg at h
    obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k ↦ ?_⟩
    by_contra! hk
    obtain ⟨hki_ne, hkj_ne⟩ := hk
    have hij := (B.apply_eq_or i j).resolve_left hji_ne.symm
    have hik := (B.apply_eq_or i k).resolve_left hki_ne.symm
    have hjk := (B.apply_eq_or j k).resolve_left hkj_ne.symm
    #adaptation_note /-- 2025-08-10 replace the following with grind after
  https://github.com/leanprover/lean4/issues/9825 is fixed -/
    have := exists_apply_eq_or_aux hij hik hjk
    aesop

lemma apply_eq_or_of_apply_ne
    (h : B.form (α i) (α i) ≠ B.form (α j) (α j)) (k : ι) :
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

end InvariantForm

lemma forall_pairing_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (∀ i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 2 * P.pairing j i ∨
            P.pairing j i = 2 * P.pairing i j) ∨
    (∀ i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 3 * P.pairing j i ∨
            P.pairing j i = 3 * P.pairing i j) := by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  by_cases h : ∀ i j, B.form (α i) (α i) = B.form (α j) (α j)
  · refine Or.inl fun i j ↦ Or.inl ?_
    have := B.pairing_mul_eq_pairing_mul_swap j i
    rwa [h i j, mul_left_inj' (B.ne_zero j)] at this
  push_neg at h
  obtain ⟨i, j, hij⟩ := h
  have key := B.apply_eq_or_of_apply_ne hij
  set li := B.form (α i) (α i)
  set lj := B.form (α j) (α j)
  have : (li = 2 * lj ∨ lj = 2 * li) ∨ (li = 3 * lj ∨ lj = 3 * li) := by
    have := B.apply_eq_or i j; tauto
  rcases this with this | this
  · refine Or.inl fun k₁ k₂ ↦ ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- #24551 (this should be faster)
  · refine Or.inr fun k₁ k₂ ↦ ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- #24551 (this should be faster)

lemma forall_pairingIn_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 2 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 2 * P.pairingIn ℤ i j) ∨
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 3 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 3 * P.pairingIn ℤ i j) := by
  simpa only [← P.algebraMap_pairingIn ℤ, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap ℤ R)] using P.forall_pairing_eq_swap_or

end RootPairing
