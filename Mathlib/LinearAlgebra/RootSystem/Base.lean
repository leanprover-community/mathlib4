/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Bases for root pairings / systems

This file contains a theory of bases for root pairings / systems.

## Implementation details

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature. However for non-reduced root pairings, it is more restrictive because it
includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base.

For infinite root systems, `RootSystem.Base` is usually not the right notion: linear independence
is too strong.

## Main definitions / results:
 * `RootSystem.Base`: a base of a root pairing.

## TODO

 * Develop a theory of base / separation / positive roots for infinite systems which specialises to
   the concept here for finite systems.

-/

noncomputable section

open Function Set Submodule

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A base of a root pairing.

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature. However for non-reduced root pairings, it is more restrictive because it
includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base. -/
structure Base (P : RootPairing ι R M N) where
  /-- The set of roots / coroots belonging to the base. -/
  support : Set ι
  linInd_root : LinearIndependent R fun i : support ↦ P.root i
  linInd_coroot : LinearIndependent R fun i : support ↦ P.coroot i
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
  linInd_root := b.linInd_coroot
  linInd_coroot := b.linInd_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

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
    span R (P.root '' b.support) = P.rootSpan := by
  rw [← span_span_of_tower (R := ℤ), span_int_root_support, span_span_of_tower]

@[simp]
lemma span_coroot_support :
    span R (P.coroot '' b.support) = P.corootSpan :=
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
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf, root_eq_smul_root_iff.mp hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x ↦ (f x : R))) := by
    rw [map_smul, linearCombination_eq_fintype_linearCombination_apply R R,
      Fintype.linearCombination_apply, hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support →₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support ↦ P.coroot k) := b.linInd_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

lemma eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι] [CharZero R]
    [NoZeroSMulDivisors ℤ M] [NoZeroSMulDivisors ℤ N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    t = 1 ∨ t = - 1 := by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  obtain ⟨s, hs⟩ := IsUnit.exists_left_inv <| isUnit_of_mul_eq_one_right _ t hz
  replace ht : s • P.coroot i ∈ range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [root_eq_smul_root_iff.mp hj, smul_smul, hs, one_smul] using mem_range_self j
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

end RootPairing

section RootSystem

variable {P : RootSystem ι R M N} (b : P.Base)

/-- A base of a root system yields a basis of the root space. -/
@[simps!] def toWeightBasis :
    Basis b.support R M :=
  Basis.mk b.linInd_root <| by
    change ⊤ ≤ span R (range <| P.root ∘ ((↑) : b.support → ι))
    rw [top_le_iff, range_comp, Subtype.range_coe_subtype, setOf_mem_eq, b.span_root_support]
    exact P.span_root_eq_top

/-- A base of a root system yields a basis of the coroot space. -/
def toCoweightBasis :
    Basis b.support R N :=
  Base.toWeightBasis (P := P.flip) b.flip

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

end Base

end RootPairing
