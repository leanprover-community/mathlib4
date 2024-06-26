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

universe u v

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme `X` is locally Noetherian if `𝒪ₓ(U)` is Noetherian for all affine `U`. -/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance

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
theorem isLocallyNoetherian_of_affine_cover {S : Set X.affineOpens}
    (hS : (⨆ i ∈ S, i : Opens X) = ⊤)
    (hS' : ∀ U ∈ S, IsNoetherianRing Γ(X, U)) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  rw [iSup_subtype'] at hS
  apply of_affine_open_cover (P := _) (fun i : S => i) hS U _ _ (fun U => hS' U.1 U.2)
  · intro U f hN
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  · intro U s _ hN
    let R := Γ(X, U)
    have : ∀ f : s, IsNoetherianRing (Away (M := R) f) := by
      intro ⟨f, hf⟩
      have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
      apply isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f)
      have := U.prop.isLocalization_basicOpen f
      have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
      exact hEq.symm.toRingEquiv
    apply isNoetherianRing_of_away
    assumption'

lemma iSup_eq_top_iff_iUnion {S : Set X.affineOpens} :
    (⨆ i ∈ S, i : Opens X) = ⊤ ↔ ⋃ i : S, (i : Set X) = Set.univ := by
  rw [iSup_subtype']
  rw [← Opens.coe_iSup]
  exact Iff.symm Opens.coe_eq_univ

/-- A scheme is locally Noetherian if and only if it is covered by affine opens whose sections
are noetherian rings.

See [Har77], Proposition II.3.2. -/
theorem isLocallyNoetherian_iff_of_iSup_eq_top
    {S : Set X.affineOpens} (hS : (⨆ i ∈ S, i : Opens X) = ⊤) :
    IsLocallyNoetherian X ↔ ∀ U ∈ S, IsNoetherianRing Γ(X, U) :=
  ⟨fun _ U _ => IsLocallyNoetherian.component_noetherian U,
   isLocallyNoetherian_of_affine_cover hS⟩

open CategoryTheory in
/-- A version of `isLocallyNoetherian_iff_of_iSup_eq_top` using `Scheme.OpenCover`. -/
theorem isLocallyNoetherian_iff_of_affine_openCover {C : Scheme.OpenCover.{v, u} X}
    (hAff : ∀ (i : C.J), IsAffine (C.obj i)) :
    IsLocallyNoetherian X ↔
    ∀ (i : C.J), IsNoetherianRing (Scheme.Γ.obj (op <| C.obj i)) := by
  -- FIXME: This proof is a bit of a mess
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (C.map i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (Scheme.openImmersionΓ (C.map i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (C.map i), isAffineOpen_opensRange _⟩
    let S : Set X.affineOpens := Set.range fS
    apply isLocallyNoetherian_of_affine_cover (S := S)
    rw [← Scheme.OpenCover.iSup_opensRange C, iSup_range]
    rintro _ ⟨i, rfl⟩
    apply isNoetherianRing_of_ringEquiv (R := Scheme.Γ.obj (op <| C.obj i))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact Scheme.openImmersionΓ (C.map i)


/-- A scheme is locally Noetherian if it has an open cover by
locally Noetherian schemes. -/
theorem isLocallyNoetherian_of_openCover (C : Scheme.OpenCover.{u, u} X)
    (hC : ∀ (i : C.J), IsLocallyNoetherian (C.obj i)) :
    IsLocallyNoetherian X := by
  let C' := Scheme.OpenCover.affineRefinement C
  let m := Scheme.OpenCover.fromAffineRefinement C
  apply Iff.mpr
  apply isLocallyNoetherian_iff_of_affine_openCover (C := C'.openCover)
  · intro i
    rw [Scheme.AffineOpenCover.openCover_obj]
    exact isAffine_Spec _
  · intro i
    let X := (C.obj (m.idx i))
    let U : X.affineOpens := ⟨Scheme.Hom.opensRange (m.app i), by
      convert isAffineOpen_opensRange (m.app i)
      exact isAffine_Spec _
    ⟩
    have hNoeth: IsNoetherianRing Γ(X, U) := by
      apply (hC (m.idx i)).component_noetherian
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    symm
    exact Scheme.openImmersionΓ (m.app i)

/-- If `R` is a noetherian ring, `Spec R` is a noetherian topological space. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Spec R) := by
  convert PrimeSpectrum.instNoetherianSpace (R := R)

lemma noetherianSpace_of_isAffine [IsAffine X]
    (hX : IsNoetherianRing <| Scheme.Γ.obj (op X)) :
    NoetherianSpace X := by
  let R := Scheme.Γ.obj (op X)
  suffices f : (Spec R).carrier ≃ₜ X.carrier by
    apply (noetherianSpace_iff_of_homeomorph f).mp
    infer_instance
  apply TopCat.homeoOfIso
  exact CategoryTheory.asIso (Scheme.isoSpec X).symm.hom.val.base

lemma noetherianSpace_of_affineOpen (U : X.affineOpens)
    (hU : IsNoetherianRing Γ(X, U)) :
    NoetherianSpace U := by
  suffices h : IsNoetherianRing (Scheme.Γ.obj { unop := X ∣_ᵤ ↑U }) by
    exact noetherianSpace_of_isAffine h
  apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact ((Scheme.restrictFunctorΓ X).app (op U)).symm

/-- Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact.

[Stacks: Lemma 01OX](https://stacks.math.columbia.edu/tag/01OX) -/
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [h : IsOpenImmersion f] : QuasiCompact f := by
  apply (quasiCompact_iff_forall_affine f).mpr
  intro U hU
  rw [Opens.map_coe, ← Set.preimage_inter_range]
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
  rw [IsAffineOpen.range_fromSpec]
  exact Set.inter_subset_left
  rw [← Set.preimage_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
  apply Inducing.isCompact_preimage'
  constructor
  exact hInd
  apply (noetherianSpace_set_iff _).mp
  apply noetherianSpace_of_affineOpen U
  apply IsLocallyNoetherian.component_noetherian
  exact Set.inter_subset_left
  rw [IsAffineOpen.range_fromSpec]
  exact Set.inter_subset_left

/-- A scheme `X` is Noetherian if it is locally Noetherian and compact. -/
@[mk_iff]
class IsNoetherian (X : Scheme) extends IsLocallyNoetherian X, CompactSpace X : Prop

open Classical in
/-- A scheme is Noetherian if and only if it is covered by finitely many affine opens whose
sections are noetherian rings. -/
theorem isNoetherian_iff_of_finite_iSup_eq_top {S : Finset X.affineOpens}
    (hS : (⨆ i ∈ S, i : Opens X) = ⊤) :
    IsNoetherian X ↔ ∀ U ∈ S, IsNoetherianRing Γ(X, U) := by
  constructor
  · intro h _ hU
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
    exact hU
  · intro h
    convert IsNoetherian.mk
    exact isLocallyNoetherian_of_affine_cover hS h
    constructor
    have hUniv : ⋃ i : S, (i : Set X) = Set.univ := iSup_eq_top_iff_iUnion.mp hS
    rw [← hUniv]
    apply isCompact_iUnion
    intro U
    apply isCompact_iff_isCompact_univ.mpr
    have := noetherianSpace_of_affineOpen U.val (h U.1 U.2)
    apply CompactSpace.isCompact_univ

/-- A version of `isNoetherian_iff_of_finite_iSup_eq_top` using `Scheme.OpenCover`. -/
theorem isNoetherian_iff_of_finite_affine_openCover {C : Scheme.OpenCover.{v, u} X}
    (hFin: Finite C.J) (hAff : ∀ (i : C.J), IsAffine (C.obj i)) :
    IsNoetherian X ↔ ∀ (i : C.J), IsNoetherianRing (Scheme.Γ.obj (op <| C.obj i)) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover hAff).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert IsNoetherian.mk
    exact (isLocallyNoetherian_iff_of_affine_openCover hAff).mpr hNoeth
    exact Scheme.OpenCover.compactSpace C

open CategoryTheory in
/-- A Noetherian scheme has a Noetherian underlying topological space.

[Stacks, Lemma 01OZ](https://stacks.math.columbia.edu/tag/01OZ) -/
instance (priority := 100) IsNoetherian.noetherianSpace [h : IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let C := X.affineCover.finiteSubcover
  rw [← C.iUnion_range]
  suffices ∀ i : C.J, NoetherianSpace (Set.range <| (C.map i).val.base) by
    apply NoetherianSpace.iUnion
  intro i
  have : IsAffine (C.obj i) := by
    rw [X.affineCover.finiteSubcover_obj]
    apply Scheme.isAffine_affineCover
  let U : X.affineOpens := ⟨Scheme.Hom.opensRange (C.map i), isAffineOpen_opensRange _⟩
  apply noetherianSpace_of_affineOpen U
  apply h.component_noetherian

/-- Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact.

[Stacks, Lemma 01P0](https://stacks.math.columbia.edu/tag/01P0) -/
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩

/-- If `R` is a Noetherian ring, `Spec R` is a locally Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsLocallyNoetherian (Spec R) := by
  apply isLocallyNoetherian_of_affine_cover (
    S := {⟨⊤, AlgebraicGeometry.isAffineOpen_top (Spec R)⟩})
  simp only [Set.mem_singleton_iff, Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_iUnion_eq_left,
    Opens.coe_top, Opens.mk_univ]
  rintro _ rfl
  apply isNoetherianRing_of_ringEquiv R
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact CategoryTheory.asIso (toSpecΓ R)

instance (priority := 100) {R : CommRingCat}
    [h : IsLocallyNoetherian <| Spec R] : IsNoetherianRing R := by
  have := h.component_noetherian ⟨⊤, AlgebraicGeometry.isAffineOpen_top (Spec R)⟩
  apply isNoetherianRing_of_ringEquiv Γ(Spec R, ⊤)
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact (CategoryTheory.asIso (toSpecΓ R)).symm

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsNoetherian (Spec R) where


/-- `R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme. -/
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R :=
  ⟨fun _ => by infer_instance,
   fun _ => by infer_instance⟩

/-- A Noetherian scheme has a finite number of irreducible components.

[Stacks, Lemma 0BA8](https://stacks.math.columbia.edu/tag/0BA8) -/
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
