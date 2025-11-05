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
* `RootSystem.Base.induction_add`: an induction principle for predicates on (co)roots which
  respect addition of a simple root.
* `RootSystem.Base.induction_reflect`: an induction principle for predicates on (co)roots which
  respect reflection in a simple root.

## TODO

* Develop a theory of base / separation / positive roots for infinite systems which specialises to
  the concept here for finite systems.

-/

noncomputable section

open Function Set Submodule
open FaithfulSMul (algebraMap_injective)
open Module
open End (invtSubmodule mem_invtSubmodule)

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
                               -P.root i ∈ AddSubmonoid.closure (P.root '' support)
  coroot_mem_or_neg_mem (i : ι) : P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support) ∨
                                 -P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support)

namespace Base

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

lemma support_nonempty [Nonempty ι] [NeZero (2 : R)] : b.support.Nonempty := by
  by_contra! contra
  rw [Finset.not_nonempty_iff_eq_empty] at contra
  inhabit ι
  simpa [P.ne_zero default, contra] using b.root_mem_or_neg_mem default

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
    P.root i ≠ -P.root j := by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  simp_all

lemma linearIndependent_pair_of_ne {i j : b.support} (hij : i ≠ j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have : ({(j : ι), (i : ι)} : Set ι) ⊆ b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by aesop)]
  simpa [image_pair] using LinearIndepOn.id_image <| b.linearIndepOn_root.mono this

lemma root_mem_span_int (i : ι) :
    P.root i ∈ span ℤ (P.root '' b.support) := by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid] at this
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
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    ∃ z : ℤ, z * t = 1 := by
  classical
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

variable [CharZero R]

lemma eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι]
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    t = 1 ∨ t = -1 := by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  obtain ⟨s, hs⟩ := IsUnit.exists_left_inv <| isUnit_of_mul_eq_one_right _ t hz
  replace ht : s • P.coroot i ∈ range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hs, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h s ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t _ s, mul_comm t s, hs] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = -1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto

lemma pos_or_neg_of_sum_smul_root_mem (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    0 < f ∨ f < 0 := by
  suffices ∀ (f : ι → ℤ)
      (hf : ∑ j ∈ b.support, f j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support ⊆ b.support) (hf' : f ≠ 0), 0 < f by
    obtain ⟨k, hk⟩ := hf
    have hf' : f ≠ 0 := by rintro rfl; exact P.ne_zero k <| by simp [hk]
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀ hf'
    · right; simpa using this (-f) (by convert hk'; simp) (by simpa only [support_neg]) (by simpa)
  intro f hf hf₀ hf'
  let f' : b.support → ℤ := fun i ↦ f i
  replace hf : ∑ j, f' j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j ∈ b.support, f j • P.root j by rwa [this]
    rw [← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid,
    Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' ℤ) (Int.ofNat ∘ c) f' (by simpa) i
  have aux : 0 ≤ f := by
    intro i
    by_cases hi : i ∈ b.support
    · change 0 ≤ f' ⟨i, hi⟩
      simp [← hc]
    · replace hi : i ∉ f.support := by contrapose! hi; exact hf₀ hi
      simp_all
  refine Pi.lt_def.mpr ⟨aux, ?_⟩
  by_contra! contra
  replace contra : f = 0 := le_antisymm contra aux
  contradiction

lemma not_nonpos_iff_pos_of_sum_mem_range_root (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    (¬ f ≤ 0) ↔ 0 < f := by
  rw [Pi.lt_def]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, ⟨i, hi⟩⟩ contra ↦ by simp [le_antisymm contra h] at hi⟩
  · rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with h' | h'
    · exact le_of_lt h'
    · exfalso
      exact h (le_of_lt h')
  · contrapose! h; exact h

lemma not_nonneg_iff_neg_of_sum_mem_range_root (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    (¬ 0 ≤ f) ↔ f < 0 := by
  replace hf : ∑ j ∈ b.support, (-f) j • P.root j ∈ range P.root := by
    rw [← neg_mem_range_root_iff]; simpa
  have := b.not_nonpos_iff_pos_of_sum_mem_range_root (-f) hf (by simpa)
  simp_all

lemma sub_notMem_range_root
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.root i - P.root j ∉ range P.root := by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k ↦ P.ne_zero k
  classical
  let f : ι → ℤ := fun k ↦ if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k ∈ b.support, f k • P.root k = P.root i - P.root j := by
    have : {i, j} ⊆ b.support := by aesop (add simp Finset.insert_subset_iff)
    rw [← Finset.sum_subset (s₁ := {i, j}) (s₂ := b.support) (by aesop) (by aesop),
      Finset.sum_insert (by aesop), Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using le_of_lt pos j
  · simpa [hij, f] using le_of_lt neg i

@[deprecated (since := "2025-05-24")] alias sub_nmem_range_root := sub_notMem_range_root

lemma sub_notMem_range_coroot
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.coroot i - P.coroot j ∉ range P.coroot :=
  b.flip.sub_notMem_range_root hi hj

@[deprecated (since := "2025-05-24")] alias sub_nmem_range_coroot := sub_notMem_range_coroot

lemma pairingIn_le_zero_of_ne [IsDomain R] [P.IsCrystallographic] [Finite ι]
    {i j} (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.pairingIn ℤ i j ≤ 0 := by
  by_contra! h
  exact b.sub_notMem_range_root hi hj <| P.root_sub_root_mem_of_pairingIn_pos h hij

variable {b}
variable [IsDomain R] [P.IsCrystallographic] [Finite ι] {i j : b.support}

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

end RootSystem

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

include b

lemma exists_root_eq_sum_nat_or_neg (i : ι) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      (P.root i =   ∑ j ∈ b.support, f j • P.root j ∨
       P.root i = - ∑ j ∈ b.support, f j • P.root j) := by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices ∀ m ∈ AddSubmonoid.closure (P.root '' b.support),
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧ m = ∑ j ∈ b.support, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inl hf'⟩
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inr hf'⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simpa, by aesop (add simp Pi.single_apply)⟩
  · intro _ _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    refine ⟨f + g, ?_, by simp [hf', hg', add_smul, Finset.sum_add_distrib]⟩
    exact (support_add f g).trans <| union_subset_iff.mpr ⟨hf, hg⟩

lemma exists_root_eq_sum_int [CharZero R] (i : ι) :
    ∃ f : ι → ℤ, f.support ⊆ b.support ∧ (0 < f ∨ f < 0) ∧
      P.root i = ∑ j ∈ b.support, f j • P.root j := by
  obtain ⟨f, hf, hf' | hf'⟩ := b.exists_root_eq_sum_nat_or_neg i
  · refine ⟨Nat.cast ∘ f, by simpa, Or.inl <| Pi.lt_def.mpr ⟨fun _ ↦ by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
    exact P.ne_zero i <| by simp [hf', contra]
  · refine ⟨-Nat.cast ∘ f, by simpa, Or.inr <| Pi.lt_def.mpr ⟨fun _ ↦ by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
    exact P.ne_zero i <| by simp [hf', contra]

end RootPairing

section PositiveRoots

variable {P : RootPairing ι R M N} (b : P.Base) [CharZero R]

/-- Given a base `α₁, α₂, …`, the height of a root `∑ zᵢαᵢ` relative to this base is `∑ zᵢ`. -/
def height (i : ι) : ℤ :=
  ∑ j ∈ b.support, (b.exists_root_eq_sum_int i).choose j

variable {b} in
lemma height_eq_sum {i : ι} {f : ι → ℤ} (heq : P.root i = ∑ j ∈ b.support, f j • P.root j) :
    b.height i = ∑ j ∈ b.support, f j := by
  suffices ∀ j ∈ b.support, (b.exists_root_eq_sum_int i).choose j = f j from
    Finset.sum_congr rfl this
  intro j hj
  obtain ⟨-, -, h⟩ := (b.exists_root_eq_sum_int i).choose_spec
  rw [h, b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance),
    b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance)] at heq
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
      (b.linearIndepOn_root.restrict_scalars' ℤ) ((b.exists_root_eq_sum_int i).choose ∘ (↑))
      (f ∘ (↑)) (by simpa) j
  simpa using aux ⟨j, hj⟩

lemma height_ne_zero (i : ι) :
    b.height i ≠ 0 := by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  rw [height_eq_sum hf₂]
  rcases hf₁ with pos | neg
  · refine (Finset.sum_pos' (fun i _ ↦ pos.le i) ?_).ne'
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j ∈ f.support
      · exact le_antisymm (contra j (hf₀ hj)) (pos.le j)
      · simpa using hj
    exact P.ne_zero i <| by simp [hf₂, contra]
  · refine (Finset.sum_neg' (fun i _ ↦ neg.le i) ?_).ne
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j ∈ f.support
      · exact le_antisymm (neg.le j) (contra j (hf₀ hj))
      · simpa using hj
    exact P.ne_zero i <| by simp [hf₂, contra]

lemma height_reflectionPerm_self (i : ι) :
    letI := P.indexNeg
    b.height (-i) = -b.height i := by
  letI := P.indexNeg
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  have hf₃ : P.root (-i) = ∑ j ∈ b.support, (-f) j • P.root j := by simpa
  simp only [height_eq_sum hf₂, height_eq_sum hf₃, Pi.neg_apply, Finset.sum_neg_distrib]

variable {b} in
lemma height_one_of_mem_support {i : ι} (hi : i ∈ b.support) :
    b.height i = 1 := by
  classical
  have : P.root i = ∑ j ∈ b.support, (Pi.single i 1 : ι → ℤ) j • P.root j := by
    rw [Finset.sum_eq_single_of_mem i hi (by simp_all)]; simp
  simpa [height_eq_sum this]

lemma height_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    b.height k = b.height i + b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l ∈ b.support, (f + g) l • P.root l := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, ← Finset.sum_add_distrib,
    Pi.add_apply]

lemma height_sub {i j k : ι} (hk : P.root k = P.root i - P.root j) :
    b.height k = b.height i - b.height j := by
  letI := P.indexNeg
  replace hk : P.root k = P.root i + P.root (-j) := by simpa [← sub_eq_add_neg]
  rw [sub_eq_add_neg, ← b.height_reflectionPerm_self, b.height_add hk]

lemma height_add_zsmul {i j k : ι} {z : ℤ} (hk : P.root k = P.root i + z • P.root j) :
    b.height k = b.height i + z • b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l ∈ b.support, (f + z • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum]

/-- The predicate that a (co)root is positive with respect to a base. -/
def IsPos (i : ι) : Prop := 0 < b.height i

lemma isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height i := Iff.rfl

lemma isPos_iff' {i : ι} : b.IsPos i ↔ 0 ≤ b.height i := by
  rw [isPos_iff]
  have := b.height_ne_zero i
  cutsat

lemma IsPos.or_neg (i : ι) :
    letI := P.indexNeg
    b.IsPos i ∨ b.IsPos (-i) := by
  rw [isPos_iff, isPos_iff, height_reflectionPerm_self]
  have := b.height_ne_zero i
  cutsat

lemma IsPos.neg_iff_not (i : ι) :
    letI := P.indexNeg
    b.IsPos (-i) ↔ ¬ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_reflectionPerm_self]
  have := b.height_ne_zero i
  cutsat

variable {b}

lemma isPos_of_mem_support {i : ι} (h : i ∈ b.support) :
    b.IsPos i := by
  rw [isPos_iff, height_one_of_mem_support h]
  exact Int.one_pos

lemma IsPos.add {i j k : ι}
    (hi : b.IsPos i) (hj : b.IsPos j) (hk : P.root k = P.root i + P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi hj ⊢
  rw [b.height_add hk]
  cutsat

lemma IsPos.sub {i j k : ι}
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i - P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi
  rw [isPos_iff', b.height_sub hk, height_one_of_mem_support hj]
  cutsat

lemma IsPos.exists_mem_support_pos_pairingIn [P.IsCrystallographic] {i : ι} (h₀ : b.IsPos i) :
    ∃ j ∈ b.support, 0 < P.pairingIn ℤ j i := by
  by_contra! contra
  suffices P.pairingIn ℤ i i ≤ 0 by simp_all
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  replace hf₁ : 0 < f := by
    refine hf₁.resolve_right ?_
    rw [isPos_iff, height_eq_sum hf₂] at h₀
    contrapose! h₀
    exact Finset.sum_nonpos fun i _ ↦ h₀.le i
  have : P.pairingIn ℤ i i = ∑ j ∈ b.support, f j • P.pairingIn ℤ j i :=
    algebraMap_injective ℤ R <| by
      simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf₂, map_sum, map_zsmul,
        LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
        zsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ ↦ ?_
  by_cases hj : j ∈ Function.support f
  · exact smul_nonpos_of_nonneg_of_nonpos (hf₁.le j) (contra j (hf₀ hj))
  · simp_all

lemma exists_mem_support_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) :
    ∃ j ∈ b.support, P.pairingIn ℤ j i ≠ 0 := by
  rcases IsPos.or_neg b i with hi | hi
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, hj₀.ne'⟩
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, by aesop⟩

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

lemma IsPos.add_zsmul {i j k : ι} {z : ℤ} (hij : i ≠ j)
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i + z • P.root j) :
    b.IsPos k := by
  replace hij : LinearIndependent R ![P.root j, P.root i] := by
    refine IsReduced.linearIndependent P hij.symm fun contra ↦ ?_
    letI := P.indexNeg
    replace contra : i = -j := by rw [eq_comm, neg_eq_iff_eq_neg]; simpa using contra
    rw [contra, isPos_iff, height_reflectionPerm_self, height_one_of_mem_support hj] at hi
    omega
  induction z generalizing i k with
  | zero => simp_all
  | succ w hw =>
    obtain ⟨l, hl⟩ : P.root i + (w : ℤ) • P.root j ∈ range P.root := by
      replace hk : P.root i + (w + 1) • P.root j ∈ range P.root := ⟨k, by rw [hk]; module⟩
      simp only [natCast_zsmul, root_add_nsmul_mem_range_iff_le_chainTopCoeff hij] at hk ⊢
      cutsat
    replace hk : P.root k = P.root l + P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).add (b.isPos_of_mem_support hj) hk
  | pred w hw =>
    obtain ⟨l, hl⟩ : P.root i + (-w : ℤ) • P.root j ∈ range P.root := by
      replace hk : P.root i - (w + 1) • P.root j ∈ range P.root := ⟨k, by rw [hk]; module⟩
      rw [neg_smul, ← sub_eq_add_neg, natCast_zsmul]
      simp only [root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij] at hk ⊢
      cutsat
    replace hk : P.root k = P.root l - P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).sub hj hk

lemma IsPos.reflectionPerm {i j : ι} (hi : b.IsPos i) (hj : j ∈ b.support) (hij : i ≠ j) :
    b.IsPos (P.reflectionPerm j i) := by
  have : P.root (P.reflectionPerm j i) = P.root i + (-P.pairingIn ℤ i j) • P.root j := by
    rw [root_reflectionPerm, neg_smul, reflection_apply_root' ℤ, sub_eq_add_neg]
  exact hi.add_zsmul hij hj this

omit [P.IsReduced] in
lemma IsPos.induction_on_add
    {i : ι} (h₀ : b.IsPos i)
    {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j k, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) :
    p i := by
  generalize hN : b.height i = N
  induction N using Int.induction_on generalizing i with
  | zero => exact False.elim <| b.height_ne_zero i hN
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    have hkn : b.height k = n := by rw [b.height_sub hk, height_one_of_mem_support hj]; omega
    have hkpos : b.IsPos k := by rw [isPos_iff']; omega
    exact h₂ k j i (by rw [hk]; module) (ih hkpos hkn) hj
  | pred n ih =>
    rw [isPos_iff] at h₀
    cutsat

omit [P.IsReduced] in
/-- This lemma is included mostly for comparison with the informal literature. Usually
`RootPairing.Base.IsPos.induction_on_add` will be more useful. -/
lemma exists_eq_sum_and_forall_sum_mem_of_isPos {i : ι} (hi : b.IsPos i) :
    ∃ n, ∃ f : Fin n → ι,
      range f ⊆ b.support ∧
      P.root i = ∑ m, P.root (f m) ∧
      ∀ m, ∑ m' ≤ m, P.root (f m') ∈ range P.root := by
  apply hi.induction_on_add (fun j hj ↦ ⟨1, ![j], by simpa⟩)
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

omit [P.IsReduced] in
lemma induction_add (i : ι) {p : ι → Prop}
    (h₀ : ∀ i, p i → p (P.reflectionPerm i i))
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j k, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) :
    p i := by
  letI := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_add h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_add h₁ h₂

lemma IsPos.induction_on_reflect
    {i : ι} (h₀ : b.IsPos i)
    {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j, p i → j ∈ b.support → p (P.reflectionPerm j i)) :
    p i := by
  generalize hN : (b.height i).natAbs = N
  induction N using Nat.strongRecOn generalizing i with
  | ind n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    have hk := h₀.reflectionPerm hj hij
    have : (b.height (P.reflectionPerm j i)).natAbs < n := by
      suffices b.height (P.reflectionPerm j i) < b.height i by
        have : (b.height (P.reflectionPerm j i)).natAbs = b.height (P.reflectionPerm j i) :=
          Int.natAbs_of_nonneg <| (isPos_iff' _).mp hk
        cutsat
      have := P.reflection_apply_root' ℤ (i := j) (j := i)
      rw [← root_reflectionPerm, sub_eq_add_neg, ← neg_smul] at this
      rw [b.height_add_zsmul this]
      replace hj : 0 < b.height j := (isPos_iff _).mp <| isPos_of_mem_support hj
      aesop
    simpa using h₂ (P.reflectionPerm j i) j
      (ih (m := (b.height (P.reflectionPerm j i)).natAbs) this hk rfl) hj

lemma induction_reflect (i : ι) {p : ι → Prop}
    (h₀ : ∀ i, p i → p (P.reflectionPerm i i))
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j, p i → j ∈ b.support → p (P.reflectionPerm j i)) :
    p i := by
  letI := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_reflect h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_reflect h₁ h₂

lemma forall_mem_support_invtSubmodule_iff (q : Submodule R M) :
    (∀ i ∈ b.support, q ∈ invtSubmodule (P.reflection i)) ↔
      (∀ i, q ∈ invtSubmodule (P.reflection i)) := by
  refine ⟨fun hq i ↦ ?_, fun hq i _ ↦ hq i⟩
  letI := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction_reflect i (by simp_all) hq ?_
  clear i
  intro i j hi hj
  rw [reflection_reflectionPerm]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (hq j hj) hi) (hq j hj)

end PositiveRoots

end Base

end RootPairing
