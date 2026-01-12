/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
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

/-- This will give a nice scheme structure on an irreducible component. -/
def oneIdealToRuleThemAll {R : Type*} [CommSemiring R] {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    Ideal R := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry

def component' {R : Type*} [CommSemiring R] {p : Ideal R} (hp : p ∈ minimalPrimes R) : Ideal R :=
  have := hp.1.1; Ideal.component ⊥ p

-- better gluing API in our case?
-- in our case, for each of our affine opens, we construct some sort of ring or affine scheme
-- and this construction is somehow nice and functorial

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
    let q := component' hp
    exact Spec (Γ(X, i) ⧸ q)
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

#check Scheme.IdealSheafData.vanishingIdeal
#check Scheme.IdealSheafData.mkOfMemSupportIff

-- extract API (and hopefully the if/then cases on `(C ∩ U).Nonempty` can alse be extracted)

noncomputable def def0
    (X : Scheme) (C : Set X) (hC : IsPreirreducible C) (U : X.affineOpens) :
    Ideal Γ(X, U) :=
  dite (U.2.fromSpec.base.hom ⁻¹' C).Nonempty (h := Classical.dec _)
    (have := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp
      ⟨·, hC.preimage U.2.fromSpec.isOpenEmbedding⟩;
      Ideal.component ⊥ (PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base.hom ⁻¹' C))) (fun _ ↦ ⊤)

  -- change IsOpenImmersion e at he
  -- let D : Set U := Subtype.val ⁻¹' C
  -- let hD : D.IsPreirreducible := IsPreirreducible.preimage

/-- temp for minimal prime -/
noncomputable def def1
    (X : Scheme) (C : Set X) (hC : C ∈ irreducibleComponents X) (U : X.affineOpens) :
    Ideal Γ(X, U) :=
  dite (C ∩ U).Nonempty (h := Classical.dec _) (fun hi ↦
    let ψ := U.2.fromSpec.base.hom
    have he : Topology.IsOpenEmbedding ψ :=
      AlgebraicGeometry.Scheme.Hom.isOpenEmbedding U.2.fromSpec
    let p := PrimeSpectrum.vanishingIdeal (ψ ⁻¹' C)
    have hp : p ∈ minimalPrimes Γ(X, U) := by
      rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
      apply Set.mem_image_of_mem PrimeSpectrum.vanishingIdeal
      exact preimage_mem_irreducibleComponents hC he (U.2.range_fromSpec ▸ hi)
    have : p.IsPrime := hp.1.1
    Ideal.component ⊥ p
  ) (fun _ ↦ ⊤)

noncomputable def tada (X : Scheme) [IsLocallyNoetherian X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) : X.IdealSheafData :=
  Scheme.IdealSheafData.mkOfMemSupportIff
    (fun U ↦ def1 X C hC U)
    (by
      intro i f
      set F := X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op
      set G := F.hom
      simp only
      -- (basically just a lemma about mapping components)
      )
    C
    (by

      sorry)

/-- The scheme structure on an irreducible component (preserving any non-reducedness). -/
noncomputable def tada'' (X : Scheme) [IsLocallyNoetherian X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) : Scheme :=
  (tada X C hC).subscheme

end AlgebraicGeometry
