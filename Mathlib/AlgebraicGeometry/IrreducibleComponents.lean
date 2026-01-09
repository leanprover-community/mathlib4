/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Lasker

/-!
# Irreducible Components of Noetherian Schemes

-/

@[expose] public section

theorem IsIrreducible.preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} (hC : IsIrreducible C)
    {f : X → Y} (hf : Topology.IsOpenEmbedding f)
    (h : (C ∩ Set.range f).Nonempty) :
    IsIrreducible (f ⁻¹' C) := by
  obtain ⟨-, hx, x, rfl⟩ := h
  exact ⟨⟨x, hx⟩, hC.2.preimage hf⟩

theorem preimage_mem_irreducibleComponents {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} (hC : C ∈ irreducibleComponents Y)
    {f : X → Y} (hf : Topology.IsOpenEmbedding f)
    (h : (C ∩ Set.range f).Nonempty) :
    f ⁻¹' C ∈ irreducibleComponents X := by
  refine ⟨hC.1.preimage hf h, fun S hS hfS ↦ ?_⟩
  replace hC := @hC.2 (closure (f '' S)) ?_ ?_
  · exact Set.image_subset_iff.mp (subset_closure.trans hC)
  · exact IsIrreducible.closure (hS.image f hf.continuous.continuousOn)
  · suffices C ≤ closure (f '' (f ⁻¹' C)) from this.trans (closure_mono (Set.image_mono hfS))
    rw [Set.image_preimage_eq_inter_range]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hf.isOpen_range h

theorem Homeomorph.preimage_mem_irreducibleComponents_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {S : Set Y} :
    f ⁻¹' S ∈ irreducibleComponents X ↔ S ∈ irreducibleComponents Y := by
  have hf y : IsPreirreducible (f ⁻¹' {y}) := by
    rw [← f.image_symm, Set.image_singleton]
    exact isPreirreducible_singleton
  refine ⟨fun h ↦ ?_, preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
    f f.continuous f.isOpenMap hf f.surjective⟩
  rw [← image_preimage f S]
  exact image_mem_irreducibleComponents_of_isPreirreducible_fiber f f.continuous f.isOpenMap
    hf f.surjective h

theorem Homeomorph.image_mem_irreducibleComponents_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {S : Set X} :
    f '' S ∈ irreducibleComponents Y ↔ S ∈ irreducibleComponents X := by
  rw [← f.preimage_symm, f.symm.preimage_mem_irreducibleComponents_iff]

-- Set of radical is just the set of associated primes of R / I
-- For the minimal primes above I, the primary ideal is uniquely determined

namespace AlgebraicGeometry

def tada' (X : Scheme) [IsLocallyNoetherian X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) : AlgebraicGeometry.Scheme.GlueData where
  J := {U : X.affineOpens | (C ∩ U).Nonempty}
  U i := by
    let U : Set X := i
    have hU : IsOpen U := i.1.1.2
    let V : Set U := Subtype.val ⁻¹' C
    have hv : Topology.IsOpenEmbedding (Subtype.val : U → X) :=
      hU.isOpenEmbedding_subtypeVal
    have key : V ∈ irreducibleComponents U := by
      apply preimage_mem_irreducibleComponents hC hv
      simp only [Subtype.range_coe]
      exact i.2
    -- let φ := AlgebraicGeometry.Scheme.isoSpec i
    -- let φ' : i ≃ₜ Spec Γ(i, ⊤) := Scheme.homeoOfIso φ
    let φ := i.1.2.isoSpec
    let φ' : i ≃ₜ Spec Γ(X, i) := Scheme.homeoOfIso φ
    have key' := (AlgebraicGeometry.Scheme.eq_zeroLocus_of_isClosed_of_isAffine i V).mp
      (isClosed_of_mem_irreducibleComponents V key)



    let Z : Set (Spec Γ(X, i)) := φ' '' V
    have hZ : Z ∈ irreducibleComponents (Spec Γ(X, i)) := by
      rwa [φ'.image_mem_irreducibleComponents_iff]
    let p := PrimeSpectrum.vanishingIdeal Z
    have hp : p ∈ minimalPrimes _ := by
      rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
      exact Set.mem_image_of_mem PrimeSpectrum.vanishingIdeal hZ
    have : IsNoetherianRing Γ(X, i) := IsLocallyNoetherian.component_noetherian i.1
    have : IsLasker Γ(X, i) := Ideal.isLasker ↑Γ(X, ↑↑i)


    -- AlgebraicGeometry.Scheme.eq_zeroLocus_of_isClosed_of_isAffine

    -- i is an affine open of X
    -- vanishing ideal is a minimal prime
    -- (see `PrimeSpectrum.vanishingIdeal_irreducibleComponents` and following)
    -- then use theory of minimal primes
    sorry
  V i := by

    sorry
  f i j := by

    sorry
  f_mono i j := sorry
  f_hasPullback i j k := sorry
  f_id i := sorry
  t i j := sorry
  t_id i := sorry
  t' := sorry
  t_fac := sorry
  cocycle := sorry
  f_open := sorry

def tada (X : Scheme) [IsLocallyNoetherian X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) : Scheme where
  carrier := TopCat.of C
  presheaf := sorry
  IsSheaf := sorry
  isLocalRing := sorry
  local_affine := by
    sorry

end AlgebraicGeometry
