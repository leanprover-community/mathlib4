/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Criterion for bases of finite root systems

Given a finite crystallographic root pairing $P$, sufficient conditions for a subset of linearly
independent roots $r_i$, $i ∈ s$ to be a base for $P$ are:
 1. $⟨c_j, r_i⟩ ≤ 0$ for all $i ≠ j$, where $c_j$ is the coroot corresponding to the root $r_j$.
 2. Every root belongs to the $ℤ$-span of the $r_i$, $i ∈ s$.
 3. Every coroot belongs to the $ℤ$-span of the $c_i$, $i ∈ s$.

This file provides a proof of this result as the definition: `RootPairing.Base.mk''`.

-/

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open FaithfulSMul (algebraMap_injective)
open Set

namespace RootPairing

-- TODO Rewrite the absurd Claude proof below into something suitable for Mathlib.

section Fintype

variable [Fintype ι] [CharZero R] (P : RootPairing ι R M N) [P.IsCrystallographic]

/-- The defining relation between the canonical positive form and the pairing. -/
private lemma two_mul_posForm_eq (i j : ι) :
    2 * (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j)
      = P.pairingIn ℤ i j * (P.posRootForm ℤ).rootLength j := by
  apply algebraMap_injective ℤ R
  rw [map_mul, map_mul, map_ofNat, RootPositiveForm.algebraMap_posForm, algebraMap_pairingIn,
    RootPositiveForm.algebraMap_rootLength]
  exact (P.posRootForm ℤ).toInvariantForm.two_mul_apply_root_root i j

private lemma posForm_nonpos_of_pairingIn_nonpos {i j : ι} (h : P.pairingIn ℤ i j ≤ 0) :
    (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤ 0 := by
  have h₁ := P.two_mul_posForm_eq i j
  have h₂ := (P.posRootForm ℤ).rootLength_pos j
  nlinarith

private lemma pairingIn_neg_of_posForm_neg {i j : ι}
    (h : (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) < 0) :
    P.pairingIn ℤ i j < 0 := by
  have h₁ := P.two_mul_posForm_eq i j
  have h₂ := (P.posRootForm ℤ).rootLength_pos j
  nlinarith

end Fintype

variable [Finite ι] [CharZero R] [IsDomain R] (P : RootPairing ι R M N) [P.IsCrystallographic]
  (s : Finset ι)

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] in
private lemma sum_smul_root_mem_closure {c : s → ℤ} (hc : 0 ≤ c) :
    ∑ k, c k • P.root k ∈ AddSubmonoid.closure (P.root '' s) := by
  refine AddSubmonoid.sum_mem _ fun k _ ↦ ?_
  rw [show c k • P.root (k : ι) = (c k).toNat • P.root (k : ι) by
    rw [← natCast_zsmul, Int.toNat_of_nonneg (hc k)]]
  exact nsmul_mem (AddSubmonoid.subset_closure (Set.mem_image_of_mem _ k.2)) _

/-- If `k ≠ l` are indices of simple roots then `αₖ - αₗ` is not a root. -/
private lemma root_sub_root_notMem_range
    (h₀' : LinearIndepOn R P.coroot s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    (hcs : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s))
    {k l : ι} (hk : k ∈ s) (hl : l ∈ s) (hkl : k ≠ l) :
    P.root k - P.root l ∉ range P.root := by
  classical
  have _i : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rintro ⟨m, hm⟩
  -- Since `⟨αₗ, αₖ⟩ ≤ 0`, we have `⟨αₖ - αₗ, αₖ⟩ ≥ 2` and so `⟨αₖ, αₖ - αₗ⟩ = 1`
  have hu : P.pairingIn ℤ m k = 2 - P.pairingIn ℤ l k := by
    apply algebraMap_injective ℤ R
    rw [map_sub, algebraMap_pairingIn, algebraMap_pairingIn, map_ofNat,
      ← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing, hm, map_sub, LinearMap.sub_apply,
      P.root_coroot_eq_pairing, P.pairing_same]
  have hu2 : 2 ≤ P.pairingIn ℤ m k := by have := h₁ hl hk (Ne.symm hkl); omega
  have hmk : m ≠ k := by
    rintro rfl
    rw [eq_comm, sub_eq_self] at hm
    exact P.ne_zero l hm
  have hv : P.pairingIn ℤ k m = 1 := by
    have h4 := P.pairingIn_pairingIn_mem_set_of_isCrystallographic m k
    have h2 : ¬ (P.pairingIn ℤ m k = 2 ∧ P.pairingIn ℤ k m = 2) := fun h ↦
      hmk <| (P.pairingIn_two_two_iff ℤ m k).mp h
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h4
    omega
  -- Hence the reflection in `αₖ - αₗ` swaps `αₖ` and `αₗ` and so `αₖ∨ - αₗ∨ = ⟨αₖ - αₗ, αₖ⟩ • m∨`
  have hrefl : P.reflectionPerm m k = l := by
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_root, ← P.algebraMap_pairingIn ℤ, hv, hm]
    simp
  have hcoroot : P.coroot k - P.coroot l = P.pairingIn ℤ m k • P.coroot m := by
    have h := P.coroot_reflectionPerm m k
    rw [hrefl, P.coreflection_apply_coroot, ← P.algebraMap_pairingIn ℤ] at h
    rw [h]
    simp [Int.cast_smul_eq_zsmul]
  -- This is absurd since `⟨αₖ - αₗ, αₖ⟩ ≥ 2` yet the coefficient of `αₖ∨` must be one
  obtain ⟨e, he⟩ : ∃ e : s → ℤ, ∑ j, e j • P.coroot j = P.coroot m := by
    rw [Set.image_eq_range] at hcs
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hcs m)
  have huniq : ∀ c c' : s → ℤ, ∑ j, c j • P.coroot j = ∑ j, c' j • P.coroot j → c = c' :=
    fun c c' h ↦ funext fun j ↦
      Fintype.linearIndependent_iffₛ.mp (h₀'.linearIndependent.restrict_scalars' ℤ) c c' h j
  have key : (Pi.single (⟨k, hk⟩ : s) 1 - Pi.single (⟨l, hl⟩ : s) 1 : s → ℤ)
      = P.pairingIn ℤ m k • e := by
    refine huniq _ _ ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
      Fintype.sum_single_smul, one_smul, mul_smul, ← Finset.smul_sum, he]
    exact hcoroot
  have hk' := congrFun key ⟨k, hk⟩
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by simpa using hkl), Pi.smul_apply,
    smul_eq_mul] at hk'
  have : P.pairingIn ℤ m k = 1 := Int.eq_one_of_dvd_one (by omega) ⟨e ⟨k, hk⟩, by omega⟩
  omega

/-- If a root is a combination of the roots indexed by `s`, at least one of whose coefficients is
negative, then it makes a strictly obtuse angle with one of the roots indexed by `s` whose
coefficient is negative.

This is where positive-definiteness of the canonical form is used. -/
private lemma exists_pairingIn_neg
    (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    {i : ι} {c : s → ℤ} (hc : P.root i = ∑ k, c k • P.root k)
    {p : s} (hp : c p < 0) :
    ∃ l, c l < 0 ∧ P.pairingIn ℤ i l < 0 := by
  classical
  have _i : Fintype ι := Fintype.ofFinite ι
  set B := P.posRootForm ℤ
  set v : s → P.rootSpan ℤ := fun k ↦ P.rootSpanMem ℤ k with hv
  -- Write `c` as the sum `y + x` of its non-negative and non-positive parts
  obtain ⟨x, hx⟩ : ∃ x : s → ℤ, ∀ k, x k = min (c k) 0 := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : s → ℤ, ∀ k, y k = max (c k) 0 := ⟨_, fun _ ↦ rfl⟩
  set X : P.rootSpan ℤ := ∑ k, x k • v k with hX
  set Y : P.rootSpan ℤ := ∑ k, y k • v k with hY
  have hXne : X ≠ 0 := by
    intro contra
    have h : ∑ k, x k • P.root (k : ι) = 0 := by
      have := congrArg (Submodule.subtype (P.rootSpan ℤ)) contra
      simpa [hX, hv] using this
    have := Fintype.linearIndependent_iff.mp (h₀.linearIndependent.restrict_scalars' ℤ) x h p
    rw [hx] at this
    omega
  have hYX : P.rootSpanMem ℤ i = Y + X := by
    have h : P.rootSpanMem ℤ i = ∑ k, c k • v k := by apply Subtype.ext; simpa [hv] using hc
    rw [h, hY, hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← add_smul, hx, hy, max_add_min, add_zero]
  -- The non-positive part pairs non-negatively with the non-negative part, hence positively
  -- with the root itself
  have h1 : 0 < B.posForm X X := P.posRootForm_posForm_pos_of_ne_zero ℤ hXne
  have h2 : 0 ≤ B.posForm Y X := by
    rw [hY, hX]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun l _ ↦ ?_
    rcases eq_or_ne k l with rfl | hkl
    · have h : x k * y k = 0 := by
        rw [hx, hy]
        rcases le_or_gt (c k) 0 with h | h
        · simp [max_eq_right h]
        · simp [min_eq_right h.le]
      rw [← mul_assoc, h, zero_mul]
    · have hxk : x k ≤ 0 := by rw [hx]; omega
      have hyl : 0 ≤ y l := by rw [hy]; omega
      have hF : B.posForm (v l) (v k) ≤ 0 :=
        P.posForm_nonpos_of_pairingIn_nonpos <| h₁ l.2 k.2 (by simpa using hkl.symm)
      exact mul_nonneg_of_nonpos_of_nonpos hxk (by nlinarith)
  have h3 : 0 < ∑ l, x l * B.posForm (P.rootSpanMem ℤ i) (v l) := by
    have h4 : B.posForm (P.rootSpanMem ℤ i) X = ∑ l, x l * B.posForm (P.rootSpanMem ℤ i) (v l) := by
      rw [hX]
      simp [map_sum]
    rw [← h4, hYX, map_add, LinearMap.add_apply]
    linarith
  -- Thus one of the terms in the sum is positive, which yields the required index
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, 0 < x l * B.posForm (P.rootSpanMem ℤ i) (v l) := by
    by_contra contra
    push Not at contra
    exact absurd h3 (not_lt.mpr <| Finset.sum_nonpos fun l hl ↦ contra l hl)
  have hxl : x l < 0 := by
    have : x l ≤ 0 := by rw [hx]; omega
    rcases mul_pos_iff.mp hl with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  refine ⟨l, by rw [hx] at hxl; omega, P.pairingIn_neg_of_posForm_neg ?_⟩
  nlinarith [hl, hxl]

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] in
private lemma sum_natAbs_succ_eq (c d : s → ℤ) (k : s)
    (h : ∀ j, j ≠ k → d j = c j) (h' : (d k).natAbs + 1 = (c k).natAbs) :
    ∑ j, (d j).natAbs + 1 = ∑ j, (c j).natAbs := by
  classical
  have h₁ : ∑ j ∈ Finset.univ.erase k, (d j).natAbs = ∑ j ∈ Finset.univ.erase k, (c j).natAbs :=
    Finset.sum_congr rfl fun j hj ↦ by rw [h j (Finset.ne_of_mem_erase hj)]
  have h₂ := Finset.add_sum_erase Finset.univ (fun j ↦ (d j).natAbs) (Finset.mem_univ k)
  have h₃ := Finset.add_sum_erase Finset.univ (fun j ↦ (c j).natAbs) (Finset.mem_univ k)
  omega

/-- The key step: every root is a non-negative or non-positive combination of the roots indexed
by `s`. The proof is by induction on the sum of the absolute values of the coefficients. -/
private lemma nonneg_or_nonpos
    (h₀ : LinearIndepOn R P.root s)
    (h₀' : LinearIndepOn R P.coroot s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    (hcs : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s))
    (n : ℕ) :
    ∀ (i : ι) (c : s → ℤ), ∑ k, (c k).natAbs ≤ n → P.root i = ∑ k, c k • P.root k →
      0 ≤ c ∨ c ≤ 0 := by
  classical
  have huniq : ∀ c c' : s → ℤ, ∑ k, c k • P.root k = ∑ k, c' k • P.root k → c = c' :=
    fun c c' h ↦ funext fun j ↦
      Fintype.linearIndependent_iffₛ.mp (h₀.linearIndependent.restrict_scalars' ℤ) c c' h j
  have hsingle : ∀ (c : s → ℤ) (k : s) (m : ℤ),
      ∑ j : s, ((c + Pi.single k m : s → ℤ) j) • P.root j
        = (∑ j, c j • P.root j) + m • P.root k := by
    intro c k m
    simp_rw [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib, Fintype.sum_single_smul]
  induction n with
  | zero =>
    intro i c hn _
    refine Or.inl fun k ↦ ?_
    have := Finset.single_le_sum (f := fun k ↦ (c k).natAbs) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ k)
    simp only [Pi.zero_apply]
    omega
  | succ n ih =>
    intro i c hn hc
    by_contra contra
    rw [not_or] at contra
    obtain ⟨hnn, hnp⟩ := contra
    obtain ⟨p, hp⟩ : ∃ p, c p < 0 := by
      simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at hnn; exact hnn
    obtain ⟨q, hq⟩ : ∃ q, 0 < c q := by
      simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at hnp; exact hnp
    -- A simple root with negative coefficient making an obtuse angle with `αᵢ`
    obtain ⟨l, hcl, hil⟩ := P.exists_pairingIn_neg s h₀ h₁ hc hp
    -- A simple root with positive coefficient making an acute angle with `αᵢ`
    obtain ⟨k, hck, hik⟩ : ∃ k, 0 < c k ∧ 0 < P.pairingIn ℤ i k := by
      have hc' : P.root (P.reflectionPerm i i) = ∑ j, (-c) j • P.root j := by
        rw [P.root_reflectionPerm, P.reflection_apply_self, hc]
        simp [← Finset.sum_neg_distrib]
      obtain ⟨k, hk₁, hk₂⟩ := P.exists_pairingIn_neg s h₀ h₁ hc' (p := q) (by simpa using hq)
      rw [P.pairingIn_reflectionPerm_self_left] at hk₂
      exact ⟨k, by simpa using hk₁, by simpa using hk₂⟩
    have hkl : k ≠ l := fun h ↦ by rw [h] at hck; omega
    have hkl' : (k : ι) ≠ (l : ι) := fun h ↦ hkl (Subtype.ext h)
    -- Subtracting `αₖ` we obtain a root with smaller coefficients, necessarily non-positive
    have hck₁ : c k = 1 ∧ ∀ j, j ≠ k → c j ≤ 0 := by
      have hik' : i ≠ (k : ι) := by
        rintro rfl
        have : c = Pi.single k 1 :=
          huniq _ _ (by rw [← hc, Fintype.sum_single_smul, one_smul])
        rw [this, Pi.single_eq_of_ne (Ne.symm hkl)] at hcl
        omega
      obtain ⟨i₀, hi₀⟩ := P.root_sub_root_mem_of_pairingIn_pos hik hik'
      have hci₀ : P.root i₀ = ∑ j : s, ((c + Pi.single k (-1) : s → ℤ) j) • P.root j := by
        rw [hsingle, ← hc, hi₀]
        module
      have hn₀ : ∑ j : s, ((c + Pi.single k (-1) : s → ℤ) j).natAbs ≤ n := by
        have haux : ∀ j, j ≠ k → (c + Pi.single k (-1) : s → ℤ) j = c j :=
          fun j hj ↦ by simp [Pi.single_eq_of_ne hj]
        have haux' : ((c + Pi.single k (-1) : s → ℤ) k).natAbs + 1 = (c k).natAbs := by
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        have := sum_natAbs_succ_eq s c (c + Pi.single k (-1)) k haux haux'
        omega
      rcases ih i₀ _ hn₀ hci₀ with h | h
      · have := Pi.le_def.mp h l
        rw [Pi.zero_apply, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hkl)] at this
        omega
      · refine ⟨?_, fun j hj ↦ ?_⟩
        · have := Pi.le_def.mp h k
          rw [Pi.zero_apply, Pi.add_apply, Pi.single_eq_same] at this
          omega
        · have := Pi.le_def.mp h j
          rw [Pi.zero_apply, Pi.add_apply, Pi.single_eq_of_ne hj] at this
          omega
    -- Adding `αₗ` we obtain a root with smaller coefficients, necessarily non-negative
    have hcl₁ : c l = -1 ∧ ∀ j, j ≠ l → 0 ≤ c j := by
      have hil' : P.root i ≠ -P.root l := by
        intro contra
        have : c = -Pi.single l 1 := by
          refine huniq _ _ ?_
          rw [← hc, contra]
          simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, Fintype.sum_single_smul,
            one_smul]
        rw [this] at hck
        simp only [Pi.neg_apply, Pi.single_eq_of_ne hkl] at hck
        omega
      obtain ⟨i₁, hi₁⟩ := P.root_add_root_mem_of_pairingIn_neg hil hil'
      have hci₁ : P.root i₁ = ∑ j : s, ((c + Pi.single l 1 : s → ℤ) j) • P.root j := by
        rw [hsingle, ← hc, hi₁]
        module
      have hn₁ : ∑ j : s, ((c + Pi.single l 1 : s → ℤ) j).natAbs ≤ n := by
        have haux : ∀ j, j ≠ l → (c + Pi.single l 1 : s → ℤ) j = c j :=
          fun j hj ↦ by simp [Pi.single_eq_of_ne hj]
        have haux' : ((c + Pi.single l 1 : s → ℤ) l).natAbs + 1 = (c l).natAbs := by
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        have := sum_natAbs_succ_eq s c (c + Pi.single l 1) l haux haux'
        omega
      rcases ih i₁ _ hn₁ hci₁ with h | h
      · refine ⟨?_, fun j hj ↦ ?_⟩
        · have := Pi.le_def.mp h l
          rw [Pi.zero_apply, Pi.add_apply, Pi.single_eq_same] at this
          omega
        · have := Pi.le_def.mp h j
          rw [Pi.zero_apply, Pi.add_apply, Pi.single_eq_of_ne hj] at this
          omega
      · have := Pi.le_def.mp h k
        rw [Pi.add_apply, Pi.zero_apply, Pi.single_eq_of_ne hkl] at this
        omega
    -- Hence `αᵢ = αₖ - αₗ` which is absurd
    have hceq : c = Pi.single k 1 - Pi.single l 1 := by
      funext j
      rcases eq_or_ne j k with rfl | hjk
      · rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl, hck₁.1, sub_zero]
      rcases eq_or_ne j l with rfl | hjl
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hjk, Pi.single_eq_same, hcl₁.1, zero_sub]
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl, sub_zero]
        have := hck₁.2 j hjk
        have := hcl₁.2 j hjl
        omega
    refine P.root_sub_root_notMem_range s h₀' h₁ hcs k.2 l.2 hkl' ⟨i, ?_⟩
    rw [hc, hceq]
    simp_rw [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib, Fintype.sum_single_smul, Fintype.sum_single_smul, one_smul,
      one_smul]

variable (s : Finset ι)
  (h₀ : LinearIndepOn R P.root s)
  (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
  (h₂ : ∀ i, P.root i ∈ Submodule.span ℤ (P.root '' s))
  (h₃ : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s))
include h₀ h₁ h₂ h₃

lemma bar (i : ι) :
     P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
    -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
  have _i : Fintype ι := Fintype.ofFinite ι
  have h₀' : LinearIndepOn R P.coroot s := by rwa [P.linearIndepOn_coroot_iff]
  obtain ⟨c, hc⟩ : ∃ c : s → ℤ, P.root i = ∑ k, c k • P.root k := by
    have h := h₂ i
    rw [Set.image_eq_range] at h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨c, hc.symm⟩
  rcases P.nonneg_or_nonpos s h₀ h₀' h₁ h₃ _ i c le_rfl hc with h | h
  · exact Or.inl (hc ▸ sum_smul_root_mem_closure P s h)
  · refine Or.inr ?_
    have h' : -P.root i = ∑ k, (-c) k • P.root k := by
      rw [hc]
      simp [← Finset.sum_neg_distrib]
    rw [h']
    exact sum_smul_root_mem_closure P s (by simpa using h)

/-- A alternate condition for a subset of linearly independent (co)roots to form a base.

This is useful when constructing a root pairing from a realisation of a Cartan matrix. -/
public def Base.mk'' :
    P.Base where
  support := s
  linearIndepOn_root := h₀
  linearIndepOn_coroot := by
    have : Fintype ι := Fintype.ofFinite ι
    rwa [P.linearIndepOn_coroot_iff]
  root_mem_or_neg_mem := P.bar s h₀ h₁ h₂ h₃
  coroot_mem_or_neg_mem i := by
    replace h₀ : LinearIndepOn R P.coroot s := by
      have : Fintype ι := Fintype.ofFinite ι
      rwa [P.linearIndepOn_coroot_iff]
    exact P.flip.bar s h₀ (fun j hj k hk hjk ↦ h₁ hk hj hjk.symm) h₃ h₂ i

@[simp] lemma Base.mk''_support :
    (Base.mk'' P s h₀ h₁ h₂ h₃).support = s := by
  rfl

end RootPairing
