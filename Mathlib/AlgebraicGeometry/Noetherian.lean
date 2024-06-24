/-
Copyright (c) 2024 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geno Racklin Asher
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.QuasiSeparated

/-!
# Noetherian and Locally Noetherian Schemes

We introduce the concept of (locally) Noetherian schemes,
giving definitions, equivalent conditions, and basic properties.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherian`: A scheme is locally Noetherian
  if the components of the structure sheaf at each affine open are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian`: A scheme is Noetherian if it is locally Noetherian
  and compact as a topological space.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_iff_affine_cover`: A scheme is locally Noetherian
  if and only if it is covered by affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`: A locally Noetherian scheme is
  quasi-separated.

* `AlgebraicGeometry.isNoetherian_iff_finite_affine_cover`: A scheme is Noetherian
  if and only if it is covered by finitely many affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian.noetherianSpace`: A Noetherian scheme is
  topologically a Noetherian space.

## References

* [Stacks: Noetherian Schemes](https://stacks.math.columbia.edu/tag/01OU)
* [Robin Hartshorne, *Algebraic Geometry*][Har77]

-/

universe u

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme `X` is locally Noetherian if `𝒪ₓ(U)` is Noetherian for all affine `U`. -/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing (X.presheaf.obj (op U)) := by infer_instance

section localizationProps

variable {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤)
  (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s))

/-- Let `R` be a ring, and `f i` a finite collection of elements of `R` generating the unit ideal.
If the localization of `R` at each `f i` is noetherian, so is `R`.

We follow the proof given in [Har77], Proposition II.3.2 -/
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply Iff.mp
  apply monotone_stabilizes_iff_noetherian
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : ∀ s : S, minN s ∈ suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : ℕ →o Ideal (Away (M := R) s) :=
      ⟨fun n => Ideal.map (floc s) (I n), by
        intro n m hnm
        dsimp
        apply Ideal.map_mono
        exact I.monotone hnm⟩
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
theorem isLocallyNoetherian_of_affine_cover (S : Set X.affineOpens)
    (hS : (⨆ i : S, i : Opens X) = ⊤)
    (hS' : ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U))) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  have hS : ⋃ i : S, (i : Set X) = Set.univ := by
    rw [← (Opens.coe_iSup _)]
    apply Opens.coe_eq_univ.mpr
    exact hS
  apply of_affine_open_cover (P := _) U S _ _ hS hS'
  · intro U f hN
    let R := X.presheaf.obj (op U)
    let Rf := Localization.Away f
    have hh : IsLocalization _ Rf := isLocalization
    have : IsNoetherianRing Rf := by
      apply @IsLocalization.isNoetherianRing R _ _ Rf _ algebra hh
      assumption
    let Rf' := X.presheaf.obj (op (X.basicOpen f))
    have hAff := IsAffineOpen.isLocalization_basicOpen U.prop f
    have := @IsLocalization.algEquiv R _ _ Rf _ _ hh Rf' _ _ hAff
    apply isNoetherianRing_of_ringEquiv Rf
    exact this.toRingEquiv
  · intro U s _ hN
    let R := X.presheaf.obj (op U)
    have : ∀ f : s, IsNoetherianRing (Away (M := R) f) := by
      intro ⟨f, hf⟩
      have : IsNoetherianRing (X.presheaf.obj (op (X.basicOpen f))) := hN ⟨f, hf⟩
      apply isNoetherianRing_of_ringEquiv (X.presheaf.obj (op (X.basicOpen f)))
      let Rf := Localization.Away f
      have hh : IsLocalization _ Rf := isLocalization
      let Rf' := X.presheaf.obj (op (X.basicOpen f))
      have hAff := IsAffineOpen.isLocalization_basicOpen U.prop f
      have := @IsLocalization.algEquiv R _ _ Rf _ _ hh Rf' _ _ hAff
      exact this.symm.toRingEquiv
    apply isNoetherianRing_of_away
    assumption'

lemma iSup_eq_top_iff_iUnion {S : Set X.affineOpens} :
    (⨆ i : S, i : Opens X) = ⊤ ↔ ⋃ i : S, (i : Set X) = Set.univ := by
  rw [← Opens.coe_iSup]
  exact Iff.symm Opens.coe_eq_univ

/-- A scheme is locally Noetherian if and only if it is covered by affine opens whose sections
are noetherian rings.

See [Har77], Proposition II.3.2. -/
theorem isLocallyNoetherian_iff_affine_cover :
    IsLocallyNoetherian X ↔
    ∃ (S : Set X.affineOpens), (⨆ i : S, i : Opens X) = ⊤ ∧
    ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U)) :=
  ⟨fun h => by
    let S : Set X.affineOpens := Set.univ
    have hS : ⨆ s : S, (s : Opens X) = ⊤ := by
      rw [← iSup_affineOpens_eq_top (X := X)]
      simp only [Opens.iSup_def, Set.iUnion_coe_set,
        Set.mem_univ, Set.iUnion_true, S]
    have hS' : ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U)) :=
      fun U => h.component_noetherian U
    exact ⟨S, hS, hS'⟩,
  fun ⟨S, hS, hS'⟩ => isLocallyNoetherian_of_affine_cover S hS hS'⟩

open CategoryTheory in
/-- A version of `isLocallyNoetherian_iff_affine_cover` using `Scheme.OpenCover`. -/
theorem isLocallyNoetherian_iff_affine_cover' :
    IsLocallyNoetherian X ↔
    ∃ (C : Scheme.OpenCover.{u, u} X), (∀ (i : C.J), IsAffine (C.obj i)) ∧
    ∀ (i : C.J), IsNoetherianRing (Scheme.Γ.obj (op <| C.obj i)) := by
  -- FIXME: This proof is a bit of a mess
  constructor
  · intro h
    obtain ⟨S, hS, hS'⟩ := isLocallyNoetherian_iff_affine_cover.mp h
    use Scheme.openCoverOfSuprEqTop X (fun U : S => U.val) hS
    constructor
    rintro ⟨U, hU⟩
    let U' : S := ⟨U, hU⟩
    rw [Scheme.openCoverOfSuprEqTop_obj]
    exact instIsAffineRestrict U'.val
    rintro ⟨U, hU⟩
    let U' : S := ⟨U, hU⟩
    have := hS' U'
    apply isNoetherianRing_of_ringEquiv (R := X.presheaf.obj (op U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact ((Scheme.restrictFunctorΓ X).app (op U)).symm
  · rintro ⟨C, ⟨hCAff, hCNoeth⟩⟩
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (C.map i), by
      apply rangeIsAffineOpenOfOpenImmersion
    ⟩
    let S : Set X.affineOpens := { fS i | i : C.J }
    apply isLocallyNoetherian_of_affine_cover S
    rw [← Scheme.OpenCover.iSup_opensRange C]
    rw [← iSup_range, ← iSup_image]
    simp only [Scheme.Γ_obj, Subtype.range_coe_subtype, Set.image_univ, Set.mem_range,
      Set.image_id', Set.mem_setOf_eq, iSup_exists, Opens.iSup_mk, Opens.carrier_eq_coe,
      Set.iUnion_iUnion_eq', Scheme.Hom.opensRange_coe, S, fS]
    intro ⟨U, ⟨i, hi⟩⟩
    apply isNoetherianRing_of_ringEquiv (R := Scheme.Γ.obj (op <| C.obj i))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    subst hi
    exact Scheme.openImmersionΓ (C.map i)

/-- A scheme is locally Noetherian if it has an open cover by
locally Noetherian schemes. -/
theorem isLocallyNoetherian_of_openCover (C : Scheme.OpenCover.{u, u} X)
    (hC : ∀ (i : C.J), IsLocallyNoetherian (C.obj i)) :
    IsLocallyNoetherian X := by
  let C' := Scheme.OpenCover.affineRefinement C
  let m := Scheme.OpenCover.fromAffineRefinement C
  apply isLocallyNoetherian_iff_affine_cover'.mpr
  use C'.openCover
  constructor
  · intro i
    rw [Scheme.AffineOpenCover.openCover_obj]
    exact SpecIsAffine _
  · intro i
    let X := (C.obj (m.idx i))
    let U : X.affineOpens := ⟨Scheme.Hom.opensRange (m.app i), by
      convert rangeIsAffineOpenOfOpenImmersion (m.app i)
      exact SpecIsAffine _
    ⟩
    have hNoeth: IsNoetherianRing (X.presheaf.obj (op U)) := by
      apply (hC (m.idx i)).component_noetherian
    apply isNoetherianRing_of_ringEquiv (R := X.presheaf.obj (op U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    symm
    exact Scheme.openImmersionΓ (m.app i)

/-- If `R` is a noetherian ring, `Spec R` is a noetherian topological space. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Scheme.Spec.obj <| op R) := by
  convert PrimeSpectrum.instNoetherianSpace (R := R)

lemma noetherianSpace_of_isAffine [IsAffine X]
    (hX : IsNoetherianRing <| Scheme.Γ.obj (op X)) :
    NoetherianSpace X := by
  let R := Scheme.Γ.obj (op X)
  let SpecR := Scheme.Spec.obj (op R)
  suffices f : SpecR.carrier ≃ₜ X.carrier by
    apply (noetherianSpace_iff_of_homeomorph f).mp
    infer_instance
  apply TopCat.homeoOfIso
  exact CategoryTheory.asIso (Scheme.isoSpec X).symm.hom.val.base

lemma noetherianSpace_of_affineOpen (U : X.affineOpens)
    (hU : IsNoetherianRing (X.presheaf.obj (op U))) :
    NoetherianSpace U := by
  suffices h : IsNoetherianRing (Scheme.Γ.obj { unop := X ∣_ᵤ ↑U }) by
    exact noetherianSpace_of_isAffine h
  apply isNoetherianRing_of_ringEquiv (R := X.presheaf.obj (op U))
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact ((Scheme.restrictFunctorΓ X).app (op U)).symm

/-- Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact.

[Stacks: Lemma 01OX](https://stacks.math.columbia.edu/tag/01OX) -/
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [h : IsOpenImmersion f] : QuasiCompact f := by
  apply (quasiCompact_iff_forall_affine f).mpr
  intro U hU
  rw [← Set.preimage_inter_range]
  apply Inducing.isCompact_preimage'
  constructor
  exact h.base_open.induced
  apply (noetherianSpace_set_iff _).mp
  apply noetherianSpace_of_affineOpen ⟨U, hU⟩
  apply IsLocallyNoetherian.component_noetherian
  exact Set.inter_subset_left
  exact Set.inter_subset_right

/-- A locally Noetherian scheme is quasi-separated.

[Stacks: Lemma 01OY](https://stacks.math.columbia.edu/tag/01OY) -/
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply (quasiSeparatedSpace_iff_affine X).mpr
  intro U V
  let f := U.prop.fromSpec.val.base
  have hInd := (IsAffineOpen.isOpenImmersion_fromSpec U.prop).base_open.induced
  apply Iff.mp
  apply Inducing.isCompact_preimage_iff (f := f)
  constructor
  exact hInd
  rw [IsAffineOpen.fromSpec_range]
  exact Set.inter_subset_left
  rw [← Set.preimage_inter_range, IsAffineOpen.fromSpec_range, Set.inter_comm]
  apply Inducing.isCompact_preimage'
  constructor
  exact hInd
  apply (noetherianSpace_set_iff _).mp
  apply noetherianSpace_of_affineOpen U
  apply IsLocallyNoetherian.component_noetherian
  exact Set.inter_subset_left
  rw [IsAffineOpen.fromSpec_range]
  exact Set.inter_subset_left

/-- A scheme `X` is Noetherian if it is locally Noetherian and compact. -/
@[mk_iff]
class IsNoetherian (X : Scheme) extends IsLocallyNoetherian X, CompactSpace X : Prop

open Classical in
/-- A scheme is Noetherian if and only if it is covered by finitely many affine opens whose
sections are noetherian rings. -/
theorem isNoetherian_iff_finite_affine_cover :
    IsNoetherian X ↔
    ∃ (S : Finset X.affineOpens), (⨆ i : S, i : Opens X) = ⊤ ∧
    ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U)) := by
  constructor
  · intro h
    obtain ⟨S, hS, hS'⟩ := isLocallyNoetherian_iff_affine_cover.mp h.toIsLocallyNoetherian
    obtain ⟨T, hT⟩ := by
      apply IsCompact.elim_finite_subcover h.toCompactSpace.isCompact_univ (fun i : S => i)
      exact fun i => Opens.isOpen i
      exact Set.univ_subset_iff.mpr <| iSup_eq_top_iff_iUnion.mp hS
    use T.image (fun i => i.val)
    constructor
    · apply le_antisymm
      exact Set.subset_univ _
      intro x hx
      have : ⋃ i ∈ T, (i : Set X) = ⋃ i : T, (↑↑↑i) := by
        apply Set.biUnion_eq_iUnion
      rw [this] at hT
      obtain ⟨t, ⟨w, hw⟩, ht'⟩ := hT hx
      use t
      constructor
      simp only [Set.mem_range, Subtype.exists, Finset.mem_image,
        exists_and_right, exists_eq_right, exists_prop]
      use w
      subst hw
      simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_coe_set, Subtype.forall,
        Set.univ_subset_iff, Opens.coe_top, Set.mem_univ, SetLike.mem_coe,
        Subtype.coe_eta, Finset.coe_mem, Subtype.coe_prop, exists_const, Set.iUnion_true]
      exact ht'
    · intro ⟨U, hU⟩
      rw [Finset.mem_image] at hU
      obtain ⟨V, _, rfl⟩ := hU
      apply hS'
  · intro h
    obtain ⟨S, hS, hS'⟩ := h
    have : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover S hS hS'
    suffices CompactSpace X by exact IsNoetherian.mk
    constructor
    have hUniv : ⋃ i : S, (i : Set X) = Set.univ := iSup_eq_top_iff_iUnion.mp hS
    rw [← hUniv]
    apply isCompact_iUnion
    intro U
    apply isCompact_iff_isCompact_univ.mpr
    have := noetherianSpace_of_affineOpen U.val (hS' U)
    refine CompactSpace.isCompact_univ

/-- A version of `isNoetherian_iff_finite_affine_cover` using `Scheme.OpenCover`. -/
theorem isNoetherian_iff_finite_affine_cover' :
    IsNoetherian X ↔
    ∃ (C : Scheme.OpenCover.{u, u} X), Finite C.J ∧ (∀ (i : C.J), IsAffine (C.obj i)) ∧
    ∀ (i : C.J), IsNoetherianRing (Scheme.Γ.obj (op <| C.obj i)) := by
  constructor
  · intro h
    obtain ⟨S, hS, hS'⟩ := isNoetherian_iff_finite_affine_cover.mp h
    use Scheme.openCoverOfSuprEqTop X (fun U : S => U.val) hS
    constructor
    exact Finite.of_fintype { x // x ∈ S }
    constructor
    rintro ⟨U, hU⟩
    let U' : S := ⟨U, hU⟩
    rw [Scheme.openCoverOfSuprEqTop_obj]
    exact instIsAffineRestrict U'.val
    rintro ⟨U, hU⟩
    have := hS' ⟨U, hU⟩
    apply isNoetherianRing_of_ringEquiv (R := X.presheaf.obj (op U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact ((Scheme.restrictFunctorΓ X).app (op U)).symm
  · rintro ⟨C, ⟨hFin, hCAff, hCN⟩⟩
    have : IsLocallyNoetherian X := isLocallyNoetherian_iff_affine_cover'.mpr
      ⟨C, hCAff, hCN⟩
    have H : ∀ j : C.J, CompactSpace (C.obj j) := by
      intro j
      constructor
      have : NoetherianSpace (C.obj j) := noetherianSpace_of_isAffine (hCN j)
      apply NoetherianSpace.isCompact
    have := Scheme.OpenCover.compactSpace C
    exact IsNoetherian.mk


open CategoryTheory in
/-- A Noetherian scheme has a Noetherian underlying topological space.

[Stacks, Lemma 01OZ](https://stacks.math.columbia.edu/tag/01OZ) -/
instance (priority := 100) IsNoetherian.noetherianSpace [h : IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  obtain ⟨t, ht, hN⟩ := isNoetherian_iff_finite_affine_cover.mp h
  have hUniv : ⋃ i : t, (i : Set X) = Set.univ := iSup_eq_top_iff_iUnion.mp ht
  rw [← hUniv]
  suffices ∀ U : t, NoetherianSpace U by
    apply NoetherianSpace.iUnion
  intro U
  apply noetherianSpace_of_affineOpen U.val
  exact hN U

/-- Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact.

[Stacks, Lemma 01P0](https://stacks.math.columbia.edu/tag/01P0) -/
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩

/-- If `R` is a Noetherian ring, `Spec R` is a locally Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsLocallyNoetherian (Scheme.Spec.obj (op R)) := by
  let X := Scheme.Spec.obj (op R)
  apply isLocallyNoetherian_of_affine_cover (S := {⟨⊤, AlgebraicGeometry.topIsAffineOpen X⟩})
  simp only [ciSup_unique, Set.default_coe_singleton]
  rintro ⟨_, rfl⟩
  apply isNoetherianRing_of_ringEquiv R
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact CategoryTheory.asIso (toSpecΓ R)

instance (priority := 100) {R : CommRingCat}
    [h : IsLocallyNoetherian (Scheme.Spec.obj (op R))] : IsNoetherianRing R := by
  let X := Scheme.Spec.obj (op R)
  have := h.component_noetherian ⟨⊤, AlgebraicGeometry.topIsAffineOpen X⟩
  -- suffices R ≅ X.presheaf.obj (op ⊤) by
  apply isNoetherianRing_of_ringEquiv (X.presheaf.obj (op ⊤))
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact (CategoryTheory.asIso (toSpecΓ R)).symm

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsNoetherian (Scheme.Spec.obj (op R)) where


/-- `R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme. -/
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Scheme.Spec.obj (op R)) ↔ IsNoetherianRing R :=
  ⟨fun _ => by infer_instance,
   fun _ => by infer_instance⟩

/-- A Noetherian scheme has a finite number of irreducible components.

[Stacks, Lemma 0BA8](https://stacks.math.columbia.edu/tag/0BA8) -/
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
