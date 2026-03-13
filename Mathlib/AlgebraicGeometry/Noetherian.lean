/-
Copyright (c) 2024 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geno Racklin Asher
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Noetherian and Locally Noetherian Schemes

We introduce the concept of (locally) Noetherian schemes,
giving definitions, equivalent conditions, and basic properties.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherian`: A scheme is locally Noetherian
  if the components of the structure sheaf at each affine open are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian`: A scheme is Noetherian if it is locally Noetherian
  and quasi-compact as a topological space.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`: A scheme is locally Noetherian
  if and only if it is covered by affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`: A locally Noetherian scheme is
  quasi-separated.

* `AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover`: A scheme is Noetherian
  if and only if it is covered by finitely many affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian.noetherianSpace`: A Noetherian scheme is
  topologically a Noetherian space.

## References

* [Stacks: Noetherian Schemes](https://stacks.math.columbia.edu/tag/01OU)
* [Robin Hartshorne, *Algebraic Geometry*][Har77]

-/

@[expose] public section

universe u v

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

namespace AlgebraicGeometry

/-- A scheme `X` is locally Noetherian if `𝒪ₓ(U)` is Noetherian for all affine `U`. -/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance

section localizationProps

variable {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤)
  (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s))

include hS hN in
/-- Let `R` be a ring, and `f i` a finite collection of elements of `R` generating the unit ideal.
If the localization of `R` at each `f i` is Noetherian, so is `R`.

We follow the proof given in [Har77], Proposition II.3.2 -/
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : ∀ s : S, minN s ∈ suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : ℕ →o Ideal (Away (M := R) s) :=
      ⟨fun n ↦ Ideal.map (floc s) (I n), fun _ _ h ↦ Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : ∀ s : S, minN s ≤ N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_comap_map_away hS (I N),
      IsLocalization.ideal_eq_iInf_comap_map_away hS (I n),
      iInf_subtype', iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
  exact hSuit s n <| Nat.le_trans (hN s) hn

end localizationProps

variable {X : Scheme}

/-- If a scheme `X` has a cover by affine opens whose sections are Noetherian rings,
then `X` is locally Noetherian. -/
theorem isLocallyNoetherian_of_affine_cover {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤)
    (hS' : ∀ i, IsNoetherianRing Γ(X, S i)) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _

/-- A scheme is locally Noetherian if and only if it is covered by affine opens whose sections
are Noetherian rings.

See [Har77], Proposition II.3.2. -/
theorem isLocallyNoetherian_iff_of_iSup_eq_top {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsLocallyNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) :=
  ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩

/-- A version of `isLocallyNoetherian_iff_of_iSup_eq_top` using `Scheme.OpenCover`. -/
theorem isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
    [∀ i, IsAffine (𝒰.X i)] :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.f i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.f i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.X i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.f i)

-- Also see `LocallyOfFiniteType.isLocallyNoetherian`.
lemma isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X where
  component_noetherian U :=
    have : IsNoetherianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyNoetherian.component_noetherian ⟨_, U.2.image_of_isOpenImmersion f⟩
    isNoetherianRing_of_surjective _ _ _ (f.appIso U).commRingCatIsoToRingEquiv.surjective

instance {U : X.Opens} [IsLocallyNoetherian X] : IsLocallyNoetherian U :=
  isLocallyNoetherian_of_isOpenImmersion U.ι

instance {U : X.OpenCover} (i) [IsLocallyNoetherian X] : IsLocallyNoetherian (U.X i) :=
  isLocallyNoetherian_of_isOpenImmersion (U.f i)

/-- If `𝒰` is an open cover of a scheme `X`, then `X` is locally Noetherian if and only if
`𝒰.X i` are all locally Noetherian. -/
theorem isLocallyNoetherian_iff_openCover (𝒰 : Scheme.OpenCover X) :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.I₀), IsLocallyNoetherian (𝒰.X i) := by
  refine ⟨fun _ ↦ inferInstance, ?_⟩
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (PreZeroHypercover.f _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian topological space. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Spec R) := by
  convert PrimeSpectrum.instNoetherianSpace (R := R)

lemma noetherianSpace_of_isAffine [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] :
    NoetherianSpace X :=
  (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance

lemma noetherianSpace_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] :
    NoetherianSpace U := by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _

instance {R : CommRingCat} [IsNoetherianRing R] : IsLocallyNoetherian (Spec R) :=
  isLocallyNoetherian_of_affine_cover (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top (Spec R)⟩) (by simp)
    fun _ ↦ isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

@[simp]
theorem isLocallyNoetherian_Spec {R : CommRingCat} :
    IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R where
  mp _ :=
    have := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  mpr _ := inferInstance

/-- Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact. -/
@[stacks 01OX]
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsOpenImmersion f] : QuasiCompact f := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  rw [Opens.map_coe, ← Set.preimage_inter_range]
  apply f.isOpenEmbedding.isInducing.isCompact_preimage'
  · apply (noetherianSpace_set_iff _).mp
    · convert noetherianSpace_of_isAffineOpen U hU
      apply IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    · exact Set.inter_subset_left
  · exact Set.inter_subset_right

/-- A locally Noetherian scheme is quasi-separated. -/
@[stacks 01OY]
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply quasiSeparatedSpace_iff_forall_affineOpens.mpr
  intro U V
  have hInd := U.2.fromSpec.isOpenEmbedding.isInducing
  apply (hInd.isCompact_preimage_iff ?_).mp
  · rw [← Set.preimage_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
    apply hInd.isCompact_preimage'
    · apply (noetherianSpace_set_iff _).mp
      · convert noetherianSpace_of_isAffineOpen U.1 U.2
        apply IsLocallyNoetherian.component_noetherian
      · exact Set.inter_subset_left
    · rw [IsAffineOpen.range_fromSpec]
      exact Set.inter_subset_left
  · rw [IsAffineOpen.range_fromSpec]
    exact Set.inter_subset_left

set_option backward.isDefEq.respectTransparency false in
theorem LocallyOfFiniteType.isLocallyNoetherian
    {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X := by
  change id (IsLocallyNoetherian X) -- avoid wlog hypotheses confusing the instance synthesizer
  wlog hY : ∃ R, Y = Spec R
  · exact (isLocallyNoetherian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i ↦
      this (Limits.pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  wlog hX : ∃ S, X = Spec S
  · exact (isLocallyNoetherian_iff_openCover X.affineCover).mpr
      fun i ↦ this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  simp_all [Algebra.FiniteType.isNoetherianRing R]

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd _ _)

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [LocallyOfFiniteType g] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst _ _)

instance (priority := low) {X Y : Scheme} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  refine ⟨fun {U hU V hV} hUV ↦ ?_⟩
  let := (f.appLE U V hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Algebra.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hUV)

lemma LocallyOfFinitePresentation.iff_locallyOfFiniteType {X Y : Scheme} {f : X ⟶ Y}
    [IsLocallyNoetherian Y] : LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- A scheme `X` is Noetherian if it is locally Noetherian and compact. -/
@[mk_iff]
class IsNoetherian (X : Scheme) : Prop extends IsLocallyNoetherian X, CompactSpace X

/-- A scheme is Noetherian if and only if it is covered by finitely many affine opens whose
sections are Noetherian rings. -/
theorem isNoetherian_iff_of_finite_iSup_eq_top {ι} [Finite ι] {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top, ← hS, Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)

/-- A version of `isNoetherian_iff_of_finite_iSup_eq_top` using `Scheme.OpenCover`. -/
theorem isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X}
    [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)] :
    IsNoetherian X ↔ ∀ (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰

/-- A Noetherian scheme has a Noetherian underlying topological space. -/
@[stacks 01OZ]
instance (priority := 100) IsNoetherian.noetherianSpace [IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let 𝒰 := X.affineCover.finiteSubcover
  rw [← 𝒰.iUnion_range]
  suffices ∀ i : 𝒰.I₀, NoetherianSpace (Set.range <| (𝒰.f i)) by
    apply NoetherianSpace.iUnion
  intro i
  have : IsAffine (𝒰.X i) := by
    rw [X.affineCover.finiteSubcover_X]
    apply Scheme.isAffine_affineCover
  let U : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
  convert noetherianSpace_of_isAffineOpen U.1 U.2
  apply IsLocallyNoetherian.component_noetherian

/-- Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact. -/
@[stacks 01P0]
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] : IsNoetherian (Spec R) where

instance {R} [CommRing R] [IsNoetherianRing R] :
    IsNoetherian <| Spec <| .of R := by
  suffices IsNoetherianRing (CommRingCat.of R) by infer_instance
  assumption

instance [IsLocallyNoetherian X] {x : X} : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

/-- `R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme. -/
@[simp]
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R := by
  simp [AlgebraicGeometry.isNoetherian_iff, inferInstanceAs (CompactSpace (Spec R))]

/-- A Noetherian scheme has a finite number of irreducible components. -/
@[stacks 0BA8]
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents

end AlgebraicGeometry
