/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Bases for root pairings / systems

This file contains a theory of bases for root pairings / systems.

## Implementation details

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature (e.g., it follows from [serre1965](Ch. V, §8, Proposition 7) that
`RootSystem.Base` is equivalent to both [serre1965](Ch. V, §8, Definition 5) and
[bourbaki1968](Ch. VI, §1.5) for reduced pairings). However for non-reduced root pairings, it is
more restrictive because it includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base in the sense of `RootSystem.Base`.

It is also worth remembering that it is only for reduced root systems that one has the simply
transitive action of the Weyl group on the set of bases, and that the Weyl group of a non-reduced
root system is the same as that of the reduced root system obtained by passing to the indivisible
roots.

For infinite root systems, `RootSystem.Base` is usually not the right notion: linear independence
is too strong.

## Main definitions / results:
* `RootSystem.Base`: a base of a root pairing.
* `RootSystem.Base.IsPos`: the predicate that a (co)root is positive relative to a base.
* `RootSystem.Base.IsPos.IsPos.induction_on`: an induction principle for positive roots.

## TODO

* Develop a theory of base / separation / positive roots for infinite systems which specialises to
  the concept here for finite systems.

-/

noncomputable section

open Function Set Submodule
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A base of a root pairing.

For reduced root pairings this definition is equivalent to the usual definition appearing in the
informal literature but not for non-reduced root pairings it is more restrictive. See the module
doc string for further remarks. -/
structure Base (P : RootPairing ι R M N) where
  /-- The indices of the simple roots / coroots. -/
  support : Finset ι
  linearIndepOn_root : LinearIndepOn R P.root support
  linearIndepOn_coroot : LinearIndepOn R P.coroot support
  root_mem_or_neg_mem (i : ι) : P.root i ∈ AddSubmonoid.closure (P.root '' support) ∨
                              - P.root i ∈ AddSubmonoid.closure (P.root '' support)
  coroot_mem_or_neg_mem (i : ι) : P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support) ∨
                                - P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support)

namespace Base

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

/-- Interchanging roots and coroots, one still has a base of a root pairing. -/
@[simps] protected def flip :
    P.flip.Base where
  support := b.support
  linearIndepOn_root := b.linearIndepOn_coroot
  linearIndepOn_coroot := b.linearIndepOn_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

include b in
lemma root_ne_neg_of_ne [Nontrivial R] {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j) :
    P.root i ≠ - P.root j := by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  aesop

lemma linearIndependent_pair_of_ne {i j : b.support} (hij : i ≠ j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have : ({(j : ι), (i : ι)} : Set ι) ⊆ b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by aesop)]
  simpa [image_pair] using LinearIndepOn.id_image <| b.linearIndepOn_root.mono this

lemma root_mem_span_int (i : ι) :
    P.root i ∈ span ℤ (P.root '' b.support) := by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoid_closure, mem_toAddSubmonoid] at this
  rw [← span_span_of_tower (R := ℕ)]
  rcases this with hi | hi
  · exact subset_span hi
  · rw [← neg_mem_iff]
    exact subset_span hi

lemma coroot_mem_span_int (i : ι) :
    P.coroot i ∈ span ℤ (P.coroot '' b.support) :=
  b.flip.root_mem_span_int i

@[simp]
lemma span_int_root_support :
    span ℤ (P.root '' b.support) = span ℤ (range P.root) := by
  refine le_antisymm (span_mono <| image_subset_range _ _) (span_le.mpr ?_)
  rintro - ⟨i, rfl⟩
  exact b.root_mem_span_int i

@[simp]
lemma span_int_coroot_support :
    span ℤ (P.coroot '' b.support) = span ℤ (range P.coroot) :=
  b.flip.span_int_root_support

@[simp]
lemma span_root_support :
    span R (P.root '' b.support) = P.rootSpan R := by
  rw [← span_span_of_tower (R := ℤ), span_int_root_support, span_span_of_tower]

@[simp]
lemma span_coroot_support :
    span R (P.coroot '' b.support) = P.corootSpan R :=
  b.flip.span_root_support

open Finsupp in
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem_aux [Finite ι]
    [NoZeroSMulDivisors ℤ M] [NoZeroSMulDivisors ℤ N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    ∃ z : ℤ, z * t = 1 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ := ht
  obtain ⟨f, hf⟩ : ∃ f : b.support → ℤ, P.coroot i = ∑ i, (t * f i) • P.coroot i := by
    have : P.coroot j ∈ span ℤ (P.coroot '' b.support) := b.coroot_mem_span_int j
    rw [image_eq_range, mem_span_range_iff_exists_fun] at this
    refine this.imp fun f hf ↦ ?_
    simp only [Finset.coe_sort_coe] at hf
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf,
      coroot_eq_smul_coroot_iff.mpr hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x ↦ (f x : R))) := by
    rw [map_smul, linearCombination_eq_fintype_linearCombination_apply,
      Fintype.linearCombination_apply, hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support →₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support ↦ P.coroot k) := b.linearIndepOn_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

lemma eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι] [CharZero R]
    [NoZeroSMulDivisors ℤ M] [NoZeroSMulDivisors ℤ N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    t = 1 ∨ t = - 1 := by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  obtain ⟨s, hs⟩ := IsUnit.exists_left_inv <| isUnit_of_mul_eq_one_right _ t hz
  replace ht : s • P.coroot i ∈ range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hs, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h s ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t _ s, mul_comm t s, hs] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = - 1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto

lemma pos_or_neg_of_sum_smul_root_mem [CharZero R] [Fintype ι] (f : ι → ℤ)
    (hf : ∑ j, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    0 ≤ f ∨ f ≤ 0 := by
  suffices ∀ (f : ι → ℤ)
      (hf : ∑ j, f j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support ⊆ b.support), 0 ≤ f by
    obtain ⟨k, hk⟩ := hf
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀
    · right; simpa using this (-f) (by convert hk'; simp) (by simpa only [support_neg'])
  intro f hf hf₀
  let f' : b.support → ℤ := fun i ↦ f i
  replace hf : ∑ j, f' j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j, f j • P.root j by rwa [this]
    rw [← Fintype.sum_subset (s := b.support) (by aesop), ← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoid_closure, mem_toAddSubmonoid,
    Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' ℤ) (Int.ofNat ∘ c) f' (by simpa) i
  intro i
  by_cases hi : i ∈ b.support
  · change 0 ≤ f' ⟨i, hi⟩
    simp [← hc]
  · replace hi : i ∉ f.support := by contrapose! hi; exact hf₀ hi
    aesop

lemma sub_notMem_range_root [CharZero R] [Finite ι]
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.root i - P.root j ∉ range P.root := by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k ↦ P.ne_zero k
  classical
  have _i : Fintype ι := Fintype.ofFinite ι
  let f : ι → ℤ := fun k ↦ if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k, f k • P.root k = P.root i - P.root j := by
    rw [← Fintype.sum_subset (s := {i, j}) (by aesop), Finset.sum_insert (by aesop),
      Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using pos j
  · simpa [hij, f] using neg i

@[deprecated (since := "2025-05-24")] alias sub_nmem_range_root := sub_notMem_range_root

lemma sub_notMem_range_coroot [CharZero R] [Finite ι]
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.coroot i - P.coroot j ∉ range P.coroot :=
  b.flip.sub_notMem_range_root hi hj

@[deprecated (since := "2025-05-24")] alias sub_nmem_range_coroot := sub_notMem_range_coroot

lemma pairingIn_le_zero_of_ne [CharZero R] [IsDomain R] [P.IsCrystallographic] [Finite ι]
    {i j} (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.pairingIn ℤ i j ≤ 0 := by
  by_contra! h
  exact b.sub_notMem_range_root hi hj <| P.root_sub_root_mem_of_pairingIn_pos h hij

lemma pos_of_sum_smul_sub_mem_range_root
    [Nontrivial M] [NoZeroSMulDivisors ℤ M] [Fintype ι] [P.IsReduced]
    {i : ι} (hi : i ∈ b.support) {f : ι → ℕ}
    (hf₀ : f.support ⊆ b.support)
    (h₁ : ∑ j, f j • P.root j ∈ range P.root)
    (h₂ : ∑ j, f j • P.root j - P.root i ∈ range P.root) :
    0 < f i := by
  have _i : CharZero R := CharZero.of_noZeroSMulDivisors R M
  classical
  let g (j : ι) : ℤ := f j -  if j = i then 1 else 0
  suffices 0 ≤ g by simpa [g] using this i
  have hg₀ : g.support ⊆ b.support := fun j hj ↦ by
    rcases eq_or_ne j i with rfl | hij; · assumption
    exact hf₀ <| by simpa [hij, g] using hj
  have hg₁ : ∑ j, g j • P.root j = ∑ j, f j • P.root j - P.root i := by simp [g, sub_smul]
  suffices ¬ g ≤ 0 by have := b.pos_or_neg_of_sum_smul_root_mem g (by rwa [hg₁]) hg₀; tauto
  intro contra
  replace contra (j : ι) (hj : j ≠ i) : f j = 0 := by simpa [g, hj] using contra j
  replace contra : ∑ j, f j • P.root j = f i • P.root i :=
    Finset.sum_eq_single_of_mem _ (by aesop) (by aesop)
  suffices f i = 1 by simp [this ▸ contra, P.ne_zero] at h₂
  by_contra hfi
  rw [contra] at h₁
  have aux : f i ≠ 0 := fun hi₀ ↦ by simp [hi₀, P.ne_zero] at h₁
  replace hfi : (f i).AtLeastTwo := ⟨by omega⟩
  exact P.nsmul_notMem_range_root h₁
variable {b}
variable [CharZero R] [IsDomain R] [P.IsCrystallographic] [Finite ι] {i j : b.support}

@[simp] lemma chainBotCoeff_eq_zero :
    P.chainBotCoeff i j = 0 :=
  chainBotCoeff_eq_zero_iff.mpr <| Or.inr <| b.sub_notMem_range_root j.property i.property

lemma chainTopCoeff_eq_of_ne (hij : i ≠ j) :
    P.chainTopCoeff i j = -P.pairingIn ℤ j i := by
  rw [← chainTopCoeff_sub_chainBotCoeff (b.linearIndependent_pair_of_ne hij)]
  simp

end RootPairing

section RootSystem

variable {P : RootSystem ι R M N} (b : P.Base)

/-- A base of a root system yields a basis of the root space. -/
def toWeightBasis :
    Basis b.support R M :=
  Basis.mk b.linearIndepOn_root <| by
    change ⊤ ≤ span R (range <| P.root ∘ ((↑) : b.support → ι))
    simp [range_comp]

@[simp] lemma toWeightBasis_apply (i : b.support) :
    b.toWeightBasis i = P.root i := by
  simp [toWeightBasis]

@[simp] lemma toWeightBasis_repr_root (i : b.support) :
    b.toWeightBasis.repr (P.root i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

/-- A base of a root system yields a basis of the coroot space. -/
def toCoweightBasis :
    Basis b.support R N :=
  Base.toWeightBasis (P := P.flip) b.flip

@[simp] lemma toCoweightBasis_apply (i : b.support) :
    b.toCoweightBasis i = P.coroot i :=
  b.flip.toWeightBasis_apply (P := P.flip) i

@[simp] lemma toCoweightBasis_repr_coroot (i : b.support) :
    b.toCoweightBasis.repr (P.coroot i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

include b
variable [Fintype ι]

lemma exists_root_eq_sum_nat_or_neg (i : ι) :
    ∃ f : ι → ℕ, P.root i = ∑ j, f j • P.root j ∨ P.root i = - ∑ j, f j • P.root j := by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices ∀ m ∈ AddSubmonoid.closure (P.root '' b.support), ∃ f : ι → ℕ, m = ∑ j, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf⟩ := this _ hi
      exact ⟨f, Or.inl hf⟩
    · obtain ⟨f, hf⟩ := this _ hi
      exact ⟨f, Or.inr hf⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  · intro _ _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by simp [hf, hg, add_smul, Finset.sum_add_distrib]⟩

lemma exists_root_eq_sum_int (i : ι) :
    ∃ f : ι → ℤ, (0 ≤ f ∨ f ≤ 0) ∧ P.root i = ∑ j, f j • P.root j := by
  obtain ⟨f, hf | hf⟩ := b.exists_root_eq_sum_nat_or_neg i
  · exact ⟨  Nat.cast ∘ f, Or.inl fun _ ↦ by simp, by simp [hf]⟩
  · exact ⟨- Nat.cast ∘ f, Or.inr fun _ ↦ by simp, by simp [hf]⟩

lemma exists_coroot_eq_sum_int (i : ι) :
    ∃ f : ι → ℤ, (0 ≤ f ∨ f ≤ 0) ∧ P.coroot i = ∑ j, f j • P.coroot j :=
  b.flip.exists_root_eq_sum_int i (P := P.flip)

end RootSystem

section PositiveRoots

variable {P : RootPairing ι R M N} (b : P.Base) [Fintype ι]

/-- The predicate that a (co)root is positive with respect to a base. -/
def IsPos (i : ι) : Prop :=
  ∃ f : ι → ℕ, f.support ⊆ b.support ∧ P.root i = ∑ j, f j • P.root j

variable {b}

lemma IsPos.add {i j k : ι}
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i + P.root j) :
    b.IsPos k := by
  classical
  obtain ⟨f, hf, hf'⟩ := hi
  refine ⟨f + Pi.single j 1, ?_, ?_⟩
  · apply (Function.support_add (f := f) (g := Pi.single j 1)).trans
    simp [insert_subset_iff, hj, hf]
  · simp_rw [hk, Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf']
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun x _ h ↦ by simp [h]),
      Pi.single_eq_same, one_smul]

lemma IsPos.sub [P.IsReduced] [Nontrivial M] [NoZeroSMulDivisors ℤ M] {i j k : ι}
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i - P.root j) :
    b.IsPos k := by
  classical
  obtain ⟨f, hf, hf'⟩ := hi
  let f' := f - Pi.single j 1
  suffices f = f' + Pi.single j 1 by
    refine ⟨f', fun l hl ↦ ?_, ?_⟩
    · rcases eq_or_ne j l with rfl | hlj; · assumption
      apply hf
      simpa [f', hlj] using hl
    · simp_rw [hk, hf', this, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_sub_assoc,
        add_eq_left]
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun x _ h ↦ by simp [h]),
        Pi.single_eq_same, one_smul, sub_self]
  ext l
  rcases eq_or_ne j l with rfl | hl
  · suffices 0 < f j by simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, f']; omega
    apply b.pos_of_sum_smul_sub_mem_range_root hj hf (hf' ▸ mem_range_self i)
    rw [← hf', ← hk]
    exact mem_range_self k
  · simp [hl, f']

variable [P.IsCrystallographic]

lemma IsPos.exists_mem_support_pos_pairingIn [CharZero R] {i : ι} (h₀ : b.IsPos i) :
    ∃ j ∈ b.support, 0 < P.pairingIn ℤ i j := by
  simp_rw [P.zero_lt_pairingIn_iff' (S := ℤ) (i := i)]
  by_contra! contra
  suffices P.pairingIn ℤ i i ≤ 0 by aesop
  obtain ⟨f, hf, hf'⟩ := h₀
  have : P.pairingIn ℤ i i = ∑ j, f j • P.pairingIn ℤ j i := algebraMap_injective ℤ R <| by
    simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf', map_sum, map_nsmul,
      LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
      nsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ ↦ ?_
  by_cases hj : j ∈ Function.support f
  · exact Left.nsmul_nonpos (contra j (hf hj)) (f j)
  · aesop

variable [P.IsReduced] [Nontrivial M] [NoZeroSMulDivisors ℤ M] [IsDomain R]

lemma IsPos.induction_on
    {i : ι} (h₀ : b.IsPos i)
    {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j k, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) :
    p i := by
  classical
  have _i : CharZero R := CharZero.of_noZeroSMulDivisors R M
  obtain ⟨f, hf₀, hf⟩ := id h₀
  generalize hN : ∑ j, f j = N
  induction N using Nat.recOn generalizing f i with
  | zero =>
    exfalso
    apply P.ne_zero i
    replace hN : f = 0 := by ext; aesop
    simpa [hN] using hf
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    let f' := f - Pi.single j 1
    have hf'₀ : Function.support f' ⊆ b.support := fun l hl ↦ by
      rcases eq_or_ne j l with rfl | hjl; · assumption
      exact hf₀ <| by simpa [hjl, f'] using hl
    have hff' : f = f' + Pi.single j 1 := by
      ext l
      rcases ne_or_eq j l with hl | rfl; · simp [hl, f']
      suffices 0 < f j by simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, f']; omega
      apply b.pos_of_sum_smul_sub_mem_range_root hj hf₀ (hf ▸ mem_range_self i)
      rw [← hf, ← hk]
      exact mem_range_self k
    have hf' : ∑ k, f' k = n := by simpa [hff', Finset.sum_add_distrib, hj] using hN
    have hfk : P.root k = ∑ j, f' j • P.root j := by
      have aux : ∀ l ∈ Finset.univ, l ≠ j → Pi.single (M := fun _ ↦ M) j (P.root l) l = 0 :=
        fun l _ hl ↦ by simp [hl]
      simp_rw [hk, hf, hff', Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply_smul,
        add_sub_assoc, add_eq_left, sub_eq_zero,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ j) aux, Pi.single_eq_same]
    exact h₂ k j i (by simp [hk]) (ih (h₀.sub hj hk) f' hf'₀ hfk hf') hj

/-- This lemma is included mostly for comparison with the informal literature. Usually
`RootPairing.Base.induction_on_pos` will be more useful. -/
lemma exists_eq_sum_and_forall_sum_mem_of_isPos {i : ι} (hi : b.IsPos i) :
    ∃ n, ∃ f : Fin n → ι,
      range f ⊆ b.support ∧
      P.root i = ∑ m, P.root (f m) ∧
      ∀ m, ∑ m' ≤ m, P.root (f m') ∈ range P.root := by
  apply hi.induction_on (fun j hj ↦ ⟨1, ![j], by simpa⟩)
  intro j k l h₁ ⟨n, f, h₂, h₃, h₄⟩ h₅
  refine ⟨n + 1, Fin.snoc f k, ?_, ?_, fun m ↦ ?_⟩
  · simpa using insert_subset h₅ h₂
  · simp [Fin.sum_univ_castSucc, h₁, h₃]
  · by_cases hm : m < n
    · have : m = (⟨m, hm⟩ : Fin n).castSucc := rfl
      rw [this, Fin.sum_Iic_castSucc]
      simp only [Fin.snoc_castSucc, h₄]
    · replace hm : m = n := by omega
      replace hm : Finset.Iic m = Finset.univ := by ext; simp [hm, Fin.le_def, Fin.is_le]
      simp [hm, Fin.sum_univ_castSucc, ← h₃, ← h₁]

end PositiveRoots

end Base

end RootPairing
