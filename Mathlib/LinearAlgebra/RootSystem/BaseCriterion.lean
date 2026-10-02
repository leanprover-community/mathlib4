/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

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

open Set Submodule

namespace RootPairing

variable [Finite ι] [CharZero R] [IsDomain R] (P : RootPairing ι R M N) [P.IsCrystallographic]

private lemma exists_coroot_sub_coroot_eq_zsmul {k l m : ι}
    (hm : P.root m = P.root k - P.root l) (hlk : P.pairingIn ℤ l k ≤ 0) :
    ∃ n : ℤ, 2 ≤ n ∧ P.coroot k - P.coroot l = n • P.coroot m := by
  have hmk : P.pairingIn ℤ m k = 2 - P.pairingIn ℤ l k := by
    rw [← P.pairingIn_same ℤ k, pairingIn_eq_add_of_root_eq_add (eq_sub_iff_add_eq.mp hm).symm]
    abel
  have hkm : P.pairingIn ℤ k m = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have hne : m ≠ k := by rintro rfl; exact P.ne_zero l <| by rwa [eq_comm, sub_eq_self] at hm
    have h := P.pairingIn_pairingIn_mem_set_of_isCrystallographic m k
    have := (P.pairingIn_two_two_iff ℤ m k).not.mpr hne
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h
    omega
  have hl : P.reflectionPerm m k = l := P.root.injective <| by
    simp [root_reflectionPerm, reflection_apply_root, ← P.algebraMap_pairingIn ℤ, hkm, hm]
  refine ⟨P.pairingIn ℤ m k, by lia, ?_⟩
  rw [← hl, coroot_reflectionPerm, coreflection_apply_coroot, ← P.algebraMap_pairingIn ℤ]
  simp [Int.cast_smul_eq_zsmul]

variable {s : Finset ι}

private lemma root_sub_root_notMem_range (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    (h₃ : ∀ i, P.coroot i ∈ span ℤ (P.coroot '' s)) {k l : s} (hkl : k ≠ l) :
    P.root k - P.root l ∉ range P.root := by
  classical
  have := Fintype.ofFinite ι
  rintro ⟨m, hm⟩
  obtain ⟨n, hn, hn'⟩ :=
    P.exists_coroot_sub_coroot_eq_zsmul hm (h₁ l.2 k.2 (by simpa using hkl.symm))
  obtain ⟨c, hc⟩ : P.coroot m ∈ LinearMap.range
      (Fintype.linearCombination ℤ fun k : s ↦ P.coroot k) := by
    simpa [image_eq_range] using h₃ m
  have hL : Function.Injective (Fintype.linearCombination ℤ fun k : s ↦ P.coroot k) :=
    ((P.linearIndepOn_coroot_iff s).mpr h₀).linearIndependent.restrict_scalars' ℤ
    |>.fintypeLinearCombination_injective
  have : Pi.single k 1 - Pi.single l 1 = n • c := hL <| by rw [map_sub, map_smul, hc, ← hn']; simp
  have : 1 = n * c k := by simpa [hkl] using congr_fun this k
  have := Int.eq_one_of_mul_eq_one_right (by lia) this.symm
  lia

private lemma _root_.LinearMap.BilinForm.exists_pos_and_pos_apply_sum_smul
    {S V κ : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [AddCommGroup V]
    [Module S V] [Fintype κ] {B : LinearMap.BilinForm S V} (hB : ∀ x ≠ 0, 0 < B x x)
    {v : κ → V} (hv : LinearIndependent S v) (hv' : Pairwise fun k l ↦ B (v k) (v l) ≤ 0)
    {c : κ → S} (hc : ¬ c ≤ 0) :
    ∃ k, 0 < c k ∧ 0 < B (∑ l, c l • v l) (v k) := by
  set x := ∑ k, c k • v k
  let X := ∑ k, (c k)⁺ • v k
  let Y := ∑ k, (c k)⁻ • v k
  have hXY : x = X - Y := by
    simp only [x, X, Y, ← Finset.sum_sub_distrib, ← sub_smul, posPart_sub_negPart]
  have hX : X ≠ 0 := fun hX ↦
    hc fun k ↦ posPart_eq_zero.mp <| Fintype.linearIndependent_iff.mp hv _ hX k
  have hYX : B Y X ≤ 0 := by
    simp only [X, Y, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_nonpos fun k _ ↦ Finset.sum_nonpos fun l _ ↦ ?_
    rcases eq_or_ne k l with rfl | hkl
    · rcases le_total (c k) 0 with h | h <;> simp [h]
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) <|
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (hv' hkl.symm)
  have : 0 < B x X := by
    rw [hXY, map_sub, LinearMap.sub_apply, sub_pos]
    exact hYX.trans_lt (hB X hX)
  simp only [X, map_sum, map_smul, smul_eq_mul] at this
  obtain ⟨k, -, hk⟩ := Finset.exists_lt_of_sum_lt (f := fun _ ↦ (0 : S)) (by simpa using this)
  have hk' := pos_of_mul_pos_right hk (posPart_nonneg (c k))
  exact ⟨k, posPart_pos_iff.mp (pos_of_mul_pos_left hk hk'.le), hk'⟩

private lemma exists_pos_pairingIn (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0) {i : ι} {c : s → ℤ}
    (hc : Fintype.linearCombination ℤ (fun k : s ↦ P.root k) c = P.root i) (hc₀ : ¬ c ≤ 0) :
    ∃ k, 0 < c k ∧ 0 < P.pairingIn ℤ i k := by
  have := Fintype.ofFinite ι
  let B := P.posRootForm ℤ
  have hi : ∑ k, c k • P.rootSpanMem ℤ k = P.rootSpanMem ℤ i := by
    ext; simp only [← hc, Fintype.linearCombination_apply, coe_sum, coe_smul_of_tower]
  obtain ⟨k, hk, hik⟩ := B.posForm.exists_pos_and_pos_apply_sum_smul
    (v := fun k : s ↦ P.rootSpanMem ℤ k) (fun _ ↦ P.posRootForm_posForm_pos_of_ne_zero ℤ)
    (.of_comp (P.rootSpan ℤ).subtype (h₀.linearIndependent.restrict_scalars' ℤ))
    (fun k l hkl ↦ (B.posForm_apply_root_root_le_zero_iff k l).mpr <| h₁ k.2 l.2 (by simpa))
    hc₀
  rw [hi] at hik
  exact ⟨k, hk, (B.zero_lt_apply_root_root_iff i k).mp hik⟩

private lemma exists_le_single [DecidableEq ι] (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0) {c : s → ℤ}
    (hc : Fintype.linearCombination ℤ (fun k : s ↦ P.root k) c ∈ range P.root)
    (hc₀ : ¬ 0 ≤ c) (hc₁ : ¬ c ≤ 0)
    (ih : ∀ d : s → ℤ, ∑ k, (d k).natAbs < ∑ k, (c k).natAbs →
      Fintype.linearCombination ℤ (fun k : s ↦ P.root k) d ∈ range P.root → 0 ≤ d ∨ d ≤ 0) :
    ∃ k, 0 < c k ∧ c ≤ Pi.single k 1 := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨k, hk, hik⟩ := P.exists_pos_pairingIn h₀ h₁ hi.symm hc₁
  obtain ⟨l, hl⟩ : ∃ l, c l < 0 := by simpa [Pi.le_def] using hc₀
  refine ⟨k, hk, ?_⟩
  have hik' : i ≠ k := by
    rintro rfl
    have : c = Pi.single k 1 :=
      (h₀.linearIndependent.restrict_scalars' ℤ).fintypeLinearCombination_injective (by simp [← hi])
    exact hc₀ (this ▸ Pi.single_nonneg.mpr zero_le_one)
  have hd : ∑ j, ((c - Pi.single k 1 : s → ℤ) j).natAbs < ∑ j, (c j).natAbs := by
    refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨k, Finset.mem_univ _, by simp; lia⟩
    rcases eq_or_ne j k with rfl | hj
    · simp; lia
    · simp [hj]
  obtain ⟨j, hj⟩ := P.root_sub_root_mem_of_pairingIn_pos hik hik'
  rcases ih _ hd ⟨j, by simp [hj, hi]⟩ with h | h
  · have := h l
    simp [show l ≠ k by lia] at this
    lia
  · exact sub_nonpos.mp h

private lemma nonneg_or_nonpos (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    (h₃ : ∀ i, P.coroot i ∈ span ℤ (P.coroot '' s)) (c : s → ℤ)
    (hc : Fintype.linearCombination ℤ (fun k : s ↦ P.root k) c ∈ range P.root) :
    0 ≤ c ∨ c ≤ 0 := by
  classical
  have ih (d : s → ℤ) (hd : ∑ k, (d k).natAbs < ∑ k, (c k).natAbs)
      (hd' : Fintype.linearCombination ℤ (fun k : s ↦ P.root k) d ∈ range P.root) :=
    nonneg_or_nonpos h₀ h₁ h₃ d hd'
  by_contra! hc'
  obtain ⟨k, hk, hk'⟩ := P.exists_le_single h₀ h₁ hc hc'.1 hc'.2 ih
  obtain ⟨l, hl, hl'⟩ := P.exists_le_single h₀ h₁ (c := -c)
    (by rwa [map_neg, neg_mem_range_root_iff]) (by simpa using hc'.2) (by simpa using hc'.1)
    (by simpa using ih)
  rw [Pi.neg_apply, neg_pos] at hl
  have hkl : k ≠ l := by lia
  have : c = Pi.single k 1 - Pi.single l 1 := by
    ext j
    have hj := hk' j
    have hj' := hl' j
    rcases eq_or_ne j k with rfl | hjk
    · simp [hkl] at hj ⊢; lia
    rcases eq_or_ne j l with rfl | hjl
    · simp [hjk] at hj' ⊢; lia
    · simp [hjk, hjl] at hj hj' ⊢; lia
  exact P.root_sub_root_notMem_range h₀ h₁ h₃ hkl <| by aesop
termination_by ∑ k, (c k).natAbs

private lemma root_mem_or_neg_mem_closure (h₀ : LinearIndepOn R P.root s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    (h₂ : ∀ i, P.root i ∈ span ℤ (P.root '' s))
    (h₃ : ∀ i, P.coroot i ∈ span ℤ (P.coroot '' s)) (i : ι) :
     P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
    -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
  have aux {c : s → ℤ} (hc : 0 ≤ c) : Fintype.linearCombination ℤ (fun k : s ↦ P.root k) c ∈
      AddSubmonoid.closure (P.root '' s) := by
    rw [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid,
      Fintype.mem_span_image_iff_exists_fun]
    refine ⟨fun k ↦ (c k).toNat, Finset.sum_congr rfl fun k _ ↦ ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg (hc k)]
  obtain ⟨c, hc⟩ : P.root i ∈ LinearMap.range (Fintype.linearCombination ℤ _) := by
    simpa [image_eq_range] using h₂ i
  rcases P.nonneg_or_nonpos h₀ h₁ h₃ c ⟨i, hc.symm⟩ with h | h
  · exact .inl (hc ▸ aux h)
  · exact .inr (by simpa [← hc] using aux (neg_nonneg.mpr h))

variable (s) (h₀ : LinearIndepOn R P.root s)
  (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
  (h₂ : ∀ i, P.root i ∈ Submodule.span ℤ (P.root '' s))
  (h₃ : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s))
include h₀ h₁ h₂ h₃

/-- An alternate condition for a subset of linearly independent (co)roots to form a base.

This is useful when constructing a root pairing from a realisation of a Cartan matrix. -/
public def Base.mk'' :
    P.Base where
  support := s
  linearIndepOn_root := h₀
  linearIndepOn_coroot := by
    have : Fintype ι := Fintype.ofFinite ι
    rwa [P.linearIndepOn_coroot_iff]
  root_mem_or_neg_mem := P.root_mem_or_neg_mem_closure h₀ h₁ h₂ h₃
  coroot_mem_or_neg_mem := by
    have : Fintype ι := Fintype.ofFinite ι
    exact P.flip.root_mem_or_neg_mem_closure ((P.linearIndepOn_coroot_iff s).mpr h₀)
      (fun j hj k hk hjk ↦ h₁ hk hj hjk.symm) h₃ h₂

@[simp] lemma Base.mk''_support :
    (Base.mk'' P s h₀ h₁ h₂ h₃).support = s := by
  rfl

end RootPairing
