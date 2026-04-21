/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!

# Connection between adic properties and topological properties

## Main results
- `IsAdic.isPrecomplete_iff`:
  `IsPrecomplete I R` is equivalent to `CompleteSpace R` in the adic topology.
- `IsAdic.isAdicComplete_iff`:
  `IsAdicComplete I R` is equivalent to `CompleteSpace R` and `T2Space R` in the adic topology.

-/
set_option backward.defeqAttrib.useBackward true

public section

section TopologicalSpace

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R} (hI : IsAdic I)

include hI in
/-- `IsHausdorff I R` is equivalent to being Hausdorff in the adic topology. -/
protected lemma IsAdic.isHausdorff_iff : IsHausdorff I R ↔ T2Space R := by
  rw [I.ringFilterBasis.t2Space_iff_sInter_subset hI.symm, isHausdorff_iff]
  simp +instances [SModEq.zero, Ideal.ringFilterBasis, RingSubgroupsBasis.toRingFilterBasis]

end TopologicalSpace

section UniformSpace

open Topology Uniformity

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  {I : Ideal R} (hI : IsAdic I)

include hI in
/-- `IsPrecomplete I R` is equivalent to being complete in the adic topology. -/
protected lemma IsAdic.isPrecomplete_iff : IsPrecomplete I R ↔ CompleteSpace R := by
  have := hI.hasBasis_nhds_zero.isCountablyGenerated
  have : (𝓤 R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  simp only [isPrecomplete_iff, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  constructor
  · intro H
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    have : ∀ i, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → u n - u m ∈ I ^ i := by
      simpa using hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mp hu
    choose N hN using this
    obtain ⟨L, hL⟩ := H (fun i ↦ u ((Finset.Iic i).sup N))
      fun _ ↦ hN _ _ (Finset.le_sup (by simpa)) _ (Finset.le_sup (by simp))
    use L
    suffices ∀ i, ∃ N, ∀ n, N ≤ n → u n - L ∈ I ^ i by
      simpa [(hI.hasBasis_nhds L).tendsto_right_iff, sub_eq_neg_add]
    refine fun i ↦ ⟨(Finset.Iic i).sup N, fun n hn ↦ ?_⟩
    have := Ideal.add_mem _ (hN i ((Finset.Iic i).sup N) (Finset.le_sup (by simp))
      n (.trans (Finset.le_sup (by simp)) hn)) (hL i)
    rwa [sub_add_sub_cancel] at this
  · intro H f hf
    obtain ⟨L, hL⟩ := CompleteSpace.complete (f := Filter.atTop.map f)
      (hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mpr fun i _ ↦
        ⟨i, fun m hm n hn ↦ by simpa using Ideal.sub_mem _ (hf hm) (hf hn)⟩)
    refine ⟨L, fun i ↦ ?_⟩
    obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → f n - L ∈ I ^ i := by
      simpa [sub_eq_neg_add] using (hI.hasBasis_nhds L).tendsto_right_iff.mp hL i
    simpa using Ideal.add_mem _ (hN (max i N) le_sup_right) (hf (le_max_left i N))

include hI in
/-- `IsAdicComplete I R` is equivalent to being complete and hausdorff in the adic topology. -/
protected lemma IsAdic.isAdicComplete_iff : IsAdicComplete I R ↔ CompleteSpace R ∧ T2Space R := by
  rw [isAdicComplete_iff, hI.isHausdorff_iff, hI.isPrecomplete_iff, and_comm]

end UniformSpace

section congrRingEquiv

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S)

theorem IsPrecomplete.congr_ringEquiv : IsPrecomplete (I.map e) S ↔ IsPrecomplete I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isPrecomplete_iff (by rfl), IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)

theorem IsHausdorff.congr_ringEquiv : IsHausdorff (I.map e) S ↔ IsHausdorff I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isHausdorff_iff rfl, IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ ↦ (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ ↦
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩

theorem IsAdicComplete.congr_ringEquiv : IsAdicComplete (I.map e) S ↔ IsAdicComplete I R := by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

end congrRingEquiv
