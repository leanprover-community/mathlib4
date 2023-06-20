/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.open_immersion.Scheme
! leanprover-community/mathlib commit 533f62f4dd62a5aad24a04326e6e787c8f7e98b1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.OpenImmersion.Basic
import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Limits.Shapes.CommSq

/-!
# Open immersions of schemes

-/


noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsOpenImmersion f
#align algebraic_geometry.is_open_immersion AlgebraicGeometry.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpace)
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.1.base : _) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine' ⟨⟨⟨_, h₂.base_open.open_range⟩, h₁⟩, R, ⟨_⟩⟩
    apply LocallyRingedSpace.iso_of_SheafedSpace_iso
    refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
    skip
    apply PresheafedSpace.is_open_immersion.iso_of_range_eq (PresheafedSpace.of_restrict _ _) f.1
    · exact Subtype.range_coe_subtype
    · infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.Scheme AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.open_range {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f.1.base) :=
  H.base_open.open_range
#align algebraic_geometry.is_open_immersion.open_range AlgebraicGeometry.IsOpenImmersion.open_range

section OpenCover

namespace Scheme

-- TODO: provide API to and from a presieve.
/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.
-/
structure OpenCover (X : Scheme.{u}) where
  J : Type v
  obj : ∀ j : J, Scheme
  map : ∀ j : J, obj j ⟶ X
  f : X.carrier → J
  Covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance
#align algebraic_geometry.Scheme.open_cover AlgebraicGeometry.Scheme.OpenCover

attribute [instance] open_cover.is_open

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme) : OpenCover X
    where
  J := X.carrier
  obj x := Spec.obj <| Opposite.op (X.local_affine x).choose_spec.some
  map x :=
    ((X.local_affine x).choose_spec.choose_spec.some.inv ≫ X.toLocallyRingedSpace.of_restrict _ : _)
  f x := x
  IsOpen x :=
    by
    apply (config := { instances := false }) PresheafedSpace.is_open_immersion.comp
    infer_instance
    apply PresheafedSpace.is_open_immersion.of_restrict
  Covers := by
    intro x
    erw [coe_comp]
    rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
    erw [Subtype.range_coe_subtype]
    exact (X.local_affine x).some.2
    rw [← TopCat.epi_iff_surjective]
    change epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forget_to_SheafedSpace.map _))
    infer_instance
#align algebraic_geometry.Scheme.affine_cover AlgebraicGeometry.Scheme.affineCover

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X
    where
  J := Σ i : 𝒰.J, (f i).J
  obj x := (f x.1).obj x.2
  map x := (f x.1).map x.2 ≫ 𝒰.map x.1
  f x := ⟨_, (f _).f (𝒰.Covers x).some⟩
  Covers x := by
    let y := (𝒰.covers x).some
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).choose_spec
    rcases(f (𝒰.f x)).Covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    rw [hz, hy]
#align algebraic_geometry.Scheme.open_cover.bind AlgebraicGeometry.Scheme.OpenCover.bind

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover Y
    where
  J := PUnit.{v + 1}
  obj _ := X
  map _ := f
  f _ := PUnit.unit
  Covers x := by
    rw [set.range_iff_surjective.mpr]; · trivial; rw [← TopCat.epi_iff_surjective]
    infer_instance
#align algebraic_geometry.Scheme.open_cover_of_is_iso AlgebraicGeometry.Scheme.openCoverOfIsIso

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : Scheme} (𝒰 : OpenCover X) (J : Type _) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).Hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J
    obj
    map
    f := fun x => e₁.symm (𝒰.f x)
    Covers := fun x =>
      by
      rw [e₂, Scheme.comp_val_base, coe_comp, Set.range_comp, set.range_iff_surjective.mpr,
        Set.image_univ, e₁.right_inverse_symm]
      · exact 𝒰.covers x
      · rw [← TopCat.epi_iff_surjective]; infer_instance
    IsOpen := fun i => by rw [e₂]; infer_instance }
#align algebraic_geometry.Scheme.open_cover.copy AlgebraicGeometry.Scheme.OpenCover.copy

/-- The pushforward of an open cover along an isomorphism. -/
@[simps J obj map]
def OpenCover.pushforwardIso {X Y : Scheme} (𝒰 : OpenCover X) (f : X ⟶ Y) [IsIso f] : OpenCover Y :=
  ((openCoverOfIsIso f).bind fun _ => 𝒰).copy 𝒰.J _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.J).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm
#align algebraic_geometry.Scheme.open_cover.pushforward_iso AlgebraicGeometry.Scheme.OpenCover.pushforwardIso

/-- Adding an open immersion into an open cover gives another open cover. -/
@[simps]
def OpenCover.add {X : Scheme} (𝒰 : X.OpenCover) {Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f] :
    X.OpenCover where
  J := Option 𝒰.J
  obj i := Option.rec Y 𝒰.obj i
  map i := Option.rec f 𝒰.map i
  f x := some (𝒰.f x)
  Covers := 𝒰.Covers
  IsOpen := by rintro (_ | _) <;> dsimp <;> infer_instance
#align algebraic_geometry.Scheme.open_cover.add AlgebraicGeometry.Scheme.OpenCover.add

-- Related result : `open_cover.pullback_cover`, where we pullback an open cover on `X` along a
-- morphism `W ⟶ X`. This is provided at the end of the file since it needs some more results
-- about open immersion (which in turn needs the open cover API).
attribute [local reducible] CommRingCat.of CommRingCat.ofHom

instance val_base_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_isIso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.Scheme.val_base_isIso

instance basic_open_isOpenImmersion {R : CommRingCat} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) :=
  by
  apply (config := { instances := false }) SheafedSpace.is_open_immersion.of_stalk_iso
  any_goals infer_instance
  any_goals infer_instance
  exact (PrimeSpectrum.localization_away_openEmbedding (Localization.Away f) f : _)
  intro x
  exact Spec_map_localization_is_iso R (Submonoid.powers f) x
#align algebraic_geometry.Scheme.basic_open_is_open_immersion AlgebraicGeometry.Scheme.basic_open_isOpenImmersion

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat) : OpenCover (Spec.obj (Opposite.op R))
    where
  J := R
  obj r := Spec.obj (Opposite.op <| CommRingCat.of <| Localization.Away r)
  map r := Spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f x := 1
  Covers r := by
    rw [set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance
  IsOpen x := AlgebraicGeometry.Scheme.basic_open_isOpenImmersion x
#align algebraic_geometry.Scheme.affine_basis_cover_of_affine AlgebraicGeometry.Scheme.affineBasisCoverOfAffine

/-- We may bind the basic open sets of an open affine cover to form a affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme) : OpenCover X :=
  X.affineCover.bind fun x => affineBasisCoverOfAffine _
#align algebraic_geometry.Scheme.affine_basis_cover AlgebraicGeometry.Scheme.affineBasisCover

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.some _ i.2
#align algebraic_geometry.Scheme.affine_basis_cover_ring AlgebraicGeometry.Scheme.affineBasisCoverRing

theorem affineBasisCover_obj (X : Scheme) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = Spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl
#align algebraic_geometry.Scheme.affine_basis_cover_obj AlgebraicGeometry.Scheme.affineBasisCover_obj

theorem affineBasisCover_map_range (X : Scheme) (x : X.carrier)
    (r : (X.local_affine x).choose_spec.some) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 :=
  by
  erw [coe_comp, Set.range_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)
#align algebraic_geometry.Scheme.affine_basis_cover_map_range AlgebraicGeometry.Scheme.affineBasisCover_map_range

theorem affineBasisCover_is_basis (X : Scheme) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X.carrier |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base} :=
  by
  apply TopologicalSpace.isTopologicalBasis_of_open_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact is_open_immersion.open_range (X.affine_basis_cover.map a)
  · rintro a U haU hU
    rcases X.affine_cover.covers a with ⟨x, e⟩
    let U' := (X.affine_cover.map (X.affine_cover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by rw [← e] at haU ; exact haU
    rcases prime_spectrum.is_basis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affine_cover.map (X.affine_cover.f a)).1.base.continuous_toFun.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine' ⟨_, ⟨⟨_, s⟩, rfl⟩, _, _⟩ <;> erw [affine_basis_cover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU
#align algebraic_geometry.Scheme.affine_basis_cover_is_basis AlgebraicGeometry.Scheme.affineBasisCover_is_basis

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps obj map]
def OpenCover.finiteSubcover {X : Scheme} (𝒰 : OpenCover X) [H : CompactSpace X.carrier] :
    OpenCover X :=
  by
  have :=
    @CompactSpace.elim_nhds_subcover _ H (fun x : X.carrier => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (is_open_immersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)
  let t := this.some
  have h : ∀ x : X.carrier, ∃ y : t, x ∈ Set.range (𝒰.map (𝒰.f y)).1.base :=
    by
    intro x
    have h' : x ∈ (⊤ : Set X.carrier) := trivial
    rw [← Classical.choose_spec this, Set.mem_iUnion] at h' 
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t
      obj := fun x => 𝒰.obj (𝒰.f x.1)
      map := fun x => 𝒰.map (𝒰.f x.1)
      f := fun x => (h x).some
      Covers := fun x => (h x).choose_spec }
#align algebraic_geometry.Scheme.open_cover.finite_subcover AlgebraicGeometry.Scheme.OpenCover.finiteSubcover

instance [H : CompactSpace X.carrier] : Fintype 𝒰.finiteSubcover.J := by
  delta open_cover.finite_subcover; infer_instance

end Scheme

end OpenCover

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace.{u} CommRingCat.{u}} (Y : Scheme.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : Scheme :=
  by
  apply LocallyRingedSpace.is_open_immersion.Scheme (to_LocallyRingedSpace _ f)
  intro x
  obtain ⟨_, ⟨i, rfl⟩, hx, hi⟩ :=
    Y.affine_basis_cover_is_basis.exists_subset_of_mem_open (Set.mem_range_self x)
      H.base_open.open_range
  use Y.affine_basis_cover_ring i
  use LocallyRingedSpace.is_open_immersion.lift (to_LocallyRingedSpace_hom _ f) _ hi
  constructor
  · rw [LocallyRingedSpace.is_open_immersion.lift_range]; exact hx
  · delta LocallyRingedSpace.is_open_immersion.lift; infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toScheme

@[simp]
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toScheme_toLocallyRingedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  toLocallyRingedSpaceHom _ f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom

@[simp]
theorem toSchemeHom_val : (toSchemeHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom_val

instance toSchemeHom_isOpenImmersion : IsOpenImmersion (toSchemeHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom_isOpenImmersionₓ

theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by cases X; cases Y; congr;
  exact H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_eq_of_LocallyRingedSpace_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_eq_of_locallyRingedSpace_eq

theorem scheme_toScheme {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : toScheme Y f.1 = X :=
  by
  apply Scheme_eq_of_LocallyRingedSpace_eq
  exact LocallyRingedSpace_to_LocallyRingedSpace f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_toScheme

end ToScheme

end PresheafedSpace.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps]
def Scheme.restrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) :
    Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.of_restrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
#align algebraic_geometry.Scheme.restrict AlgebraicGeometry.Scheme.restrict

/-- The canonical map from the restriction to the supspace. -/
@[simps]
def Scheme.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.of_restrict h
#align algebraic_geometry.Scheme.of_restrict AlgebraicGeometry.Scheme.ofRestrict

instance IsOpenImmersion.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : IsOpenImmersion (X.of_restrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.of_restrict h) by infer_instance
#align algebraic_geometry.is_open_immersion.of_restrict AlgebraicGeometry.IsOpenImmersion.ofRestrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  @LocallyRingedSpace.IsOpenImmersion.of_isIso _
    (show IsIso ((inducedFunctor _).map g) by infer_instance)
#align algebraic_geometry.is_open_immersion.of_is_iso AlgebraicGeometry.IsOpenImmersion.of_isIso

theorem to_iso {X Y : Scheme} (f : X ⟶ Y) [h : IsOpenImmersion f] [Epi f.1.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ f.1 h _) _
#align algebraic_geometry.is_open_immersion.to_iso AlgebraicGeometry.IsOpenImmersion.to_iso

theorem of_stalk_iso {X Y : Scheme} (f : X ⟶ Y) (hf : OpenEmbedding f.1.base)
    [∀ x, IsIso (PresheafedSpace.stalkMap f.1 x)] : IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.1 hf
#align algebraic_geometry.is_open_immersion.of_stalk_iso AlgebraicGeometry.IsOpenImmersion.of_stalk_iso

theorem iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  ⟨fun H => ⟨H.1, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.of_stalk_iso f h₁ h₂⟩
#align algebraic_geometry.is_open_immersion.iff_stalk_iso AlgebraicGeometry.IsOpenImmersion.iff_stalk_iso

theorem AlgebraicGeometry.isIso_iff_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.1.base :=
  ⟨fun H => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.to_iso f h₁ h₂⟩
#align algebraic_geometry.is_iso_iff_is_open_immersion AlgebraicGeometry.isIso_iff_isOpenImmersion

theorem AlgebraicGeometry.isIso_iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  by
  rw [is_iso_iff_is_open_immersion, is_open_immersion.iff_stalk_iso, and_comm', ← and_assoc']
  refine' and_congr ⟨_, _⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to
      is_iso
        (TopCat.isoOfHomeo
            (Homeomorph.homeomorphOfContinuousOpen
              (Equiv.ofBijective _ ⟨h₂.inj, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
              h₂.is_open_map)).Hom
    · ext; rfl
    · infer_instance
  · intro H; exact ⟨inferInstance, (TopCat.homeoOfIso (as_iso f.1.base)).OpenEmbedding⟩
#align algebraic_geometry.is_iso_iff_stalk_iso AlgebraicGeometry.isIso_iff_stalk_iso

/-- A open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ (Z.restrict H.base_open : _) :=
  ⟨H.isoRestrict.Hom, H.isoRestrict.inv, H.isoRestrict.hom_inv_id, H.isoRestrict.inv_hom_id⟩
#align algebraic_geometry.is_open_immersion.iso_restrict AlgebraicGeometry.IsOpenImmersion.isoRestrict

local notation "forget" => Scheme.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (inducedFunctor _).mono_of_mono_map (show @Mono LocallyRingedSpace _ _ _ f by infer_instance)
#align algebraic_geometry.is_open_immersion.mono AlgebraicGeometry.IsOpenImmersion.mono

instance forget_map_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.IsOpenImmersion.forget_map_isOpenImmersion

instance hasLimit_cospan_forget_of_left :
    HasLimit (cospan f g ⋙ Scheme.forgetToLocallyRingedSpace) :=
  by
  apply has_limit_of_iso (diagramIsoCospan.{u} _).symm
  change has_limit (cospan (forget.map f) (forget.map g))
  infer_instance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left

open CategoryTheory.Limits.WalkingCospan

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left'

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) :=
  by
  apply has_limit_of_iso (diagramIsoCospan.{u} _).symm
  change has_limit (cospan (forget.map g) (forget.map f))
  infer_instance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.snd LocallyRingedSpace _ _ _ _ f g _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.fst LocallyRingedSpace _ _ _ _ g f _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfRight

instance forgetPreservesOfLeft : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit _ _
#align algebraic_geometry.is_open_immersion.forget_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfLeft

instance forgetPreservesOfRight : PreservesLimit (cospan g f) forget :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.is_open_immersion.forget_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfRight

instance hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
#align algebraic_geometry.is_open_immersion.has_pullback_of_left AlgebraicGeometry.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget
#align algebraic_geometry.is_open_immersion.has_pullback_of_right AlgebraicGeometry.IsOpenImmersion.hasPullback_of_right

instance pullback_snd_of_left : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  have := preserves_pullback.iso_hom_snd forget f g
  dsimp only [Scheme.forget_to_LocallyRingedSpace, induced_functor_map] at this 
  rw [← this]
  change LocallyRingedSpace.is_open_immersion _
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.pullback_snd_of_left

instance pullback_fst_of_right : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl]
  change is_open_immersion (_ ≫ f)
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_to_base AlgebraicGeometry.IsOpenImmersion.pullback_to_base

instance forgetToTopPreservesOfLeft : PreservesLimit (cospan f g) Scheme.forgetToTop :=
  by
  apply (config := { instances := false }) limits.comp_preserves_limit
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp [LocallyRingedSpace.forget_to_Top]
  infer_instance
#align algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfLeft

instance forgetToTopPreservesOfRight : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfRight

theorem range_pullback_snd_of_left :
    Set.range (pullback.snd : pullback f g ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.snd : pullback f g ⟶ _).1.base from
      preserves_pullback.iso_hom_snd Scheme.forget_to_Top f g,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _),
    TopCat.pullback_snd_image_fst_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.is_open_immersion.range_pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_snd_of_left

theorem range_pullback_fst_of_right :
    Set.range (pullback.fst : pullback g f ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.fst : pullback g f ⟶ _).1.base from
      preserves_pullback.iso_hom_fst Scheme.forget_to_Top g f,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _),
    TopCat.pullback_fst_image_snd_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.is_open_immersion.range_pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_fst_of_right

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      Set.range f.1.base ∩ Set.range g.1.base :=
  by
  rw [pullback.condition, Scheme.comp_val_base, coe_comp, Set.range_comp,
    range_pullback_snd_of_left, opens.map_obj, opens.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm]
#align algebraic_geometry.is_open_immersion.range_pullback_to_base_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base =
      Set.range g.1.base ∩ Set.range f.1.base :=
  by
  rw [Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_fst_of_right, opens.map_obj,
    opens.coe_mk, Set.image_preimage_eq_inter_range, Set.inter_comm]
#align algebraic_geometry.is_open_immersion.range_pullback_to_base_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  LocallyRingedSpace.IsOpenImmersion.lift f g H'
#align algebraic_geometry.is_open_immersion.lift AlgebraicGeometry.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac f g H'
#align algebraic_geometry.is_open_immersion.lift_fac AlgebraicGeometry.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq f g H' l hl
#align algebraic_geometry.is_open_immersion.lift_uniq AlgebraicGeometry.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range are isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) : X ≅ Y
    where
  Hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id' := by rw [← cancel_mono f]; simp
  inv_hom_id' := by rw [← cancel_mono g]; simp
#align algebraic_geometry.is_open_immersion.iso_of_range_eq AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev AlgebraicGeometry.Scheme.Hom.opensFunctor {X Y : Scheme} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : Opens X.carrier ⥤ Opens Y.carrier :=
  H.openFunctor
#align algebraic_geometry.Scheme.hom.opens_functor AlgebraicGeometry.Scheme.Hom.opensFunctor

/-- The isomorphism `Γ(X, U) ⟶ Γ(Y, f(U))` induced by an open immersion `f : X ⟶ Y`. -/
def AlgebraicGeometry.Scheme.Hom.invApp {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] (U) :
    X.Presheaf.obj (op U) ⟶ Y.Presheaf.obj (op (f.opensFunctor.obj U)) :=
  H.invApp U
#align algebraic_geometry.Scheme.hom.inv_app AlgebraicGeometry.Scheme.Hom.invApp

theorem app_eq_inv_app_app_of_comp_eq_aux {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    (Opens.map f.1.base).obj V = (Opens.map fg.1.base).obj (g.opensFunctor.obj V) :=
  by
  subst H
  rw [Scheme.comp_val_base, opens.map_comp_obj]
  congr 1
  ext1
  exact (Set.preimage_image_eq _ h.base_open.inj).symm
#align algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq_aux AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_invApp_app_of_comp_eq {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    f.1.c.app (op V) =
      g.invApp _ ≫
        fg.1.c.app _ ≫
          Y.Presheaf.map
            (eqToHom <| IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux f g fg H V).op :=
  by
  subst H
  rw [Scheme.comp_val_c_app, category.assoc, Scheme.hom.inv_app,
    PresheafedSpace.is_open_immersion.inv_app_app_assoc, f.val.c.naturality_assoc,
    TopCat.Presheaf.pushforwardObj_map, ← functor.map_comp]
  convert (category.comp_id _).symm
  convert Y.presheaf.map_id _
#align algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq AlgebraicGeometry.IsOpenImmersion.app_eq_invApp_app_of_comp_eq

theorem lift_app {X Y U : Scheme} (f : U ⟶ Y) (g : X ⟶ Y) [h : IsOpenImmersion f] (H)
    (V : Opens U.carrier) :
    (IsOpenImmersion.lift f g H).1.c.app (op V) =
      f.invApp _ ≫
        g.1.c.app _ ≫
          X.Presheaf.map
            (eqToHom <|
                IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux _ _ _
                  (IsOpenImmersion.lift_fac f g H).symm V).op :=
  IsOpenImmersion.app_eq_invApp_app_of_comp_eq _ _ _ _ _
#align algebraic_geometry.is_open_immersion.lift_app AlgebraicGeometry.IsOpenImmersion.lift_app

end IsOpenImmersion

namespace Scheme

theorem image_basicOpen {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X.carrier}
    (r : X.Presheaf.obj (op U)) : f.opensFunctor.obj (X.basicOpen r) = Y.basicOpen (f.invApp U r) :=
  by
  have e := Scheme.preimage_basic_open f (f.inv_app U r)
  rw [Scheme.hom.inv_app, PresheafedSpace.is_open_immersion.inv_app_app_apply,
    Scheme.basic_open_res, inf_eq_right.mpr _] at e 
  rw [← e]
  ext1
  refine' set.image_preimage_eq_inter_range.trans _
  erw [Set.inter_eq_left_iff_subset]
  refine' Set.Subset.trans (Scheme.basic_open_le _ _) (Set.image_subset_range _ _)
  refine' le_trans (Scheme.basic_open_le _ _) (le_of_eq _)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm
#align algebraic_geometry.Scheme.image_basic_open AlgebraicGeometry.Scheme.image_basicOpen

/-- The image of an open immersion as an open set. -/
@[simps]
def Hom.opensRange {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y.carrier :=
  ⟨_, H.base_open.open_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.Scheme.Hom.opensRange

end Scheme

section

variable (X : Scheme)

/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor : Opens X.carrier ⥤ Over X
    where
  obj U := Over.mk (X.of_restrict U.OpenEmbedding)
  map U V i :=
    Over.homMk
      (IsOpenImmersion.lift (X.of_restrict _) (X.of_restrict _)
        (by change Set.range coe ⊆ Set.range coe; simp_rw [Subtype.range_coe]; exact i.le))
      (IsOpenImmersion.lift_fac _ _ _)
  map_id' U := by
    ext1
    dsimp only [over.hom_mk_left, over.id_left]
    rw [← cancel_mono (X.of_restrict U.open_embedding), category.id_comp,
      is_open_immersion.lift_fac]
  map_comp' U V W i j := by
    ext1
    dsimp only [over.hom_mk_left, over.comp_left]
    rw [← cancel_mono (X.of_restrict W.open_embedding), category.assoc]
    iterate 3 rw [is_open_immersion.lift_fac]
#align algebraic_geometry.Scheme.restrict_functor AlgebraicGeometry.Scheme.restrictFunctor

@[reassoc]
theorem Scheme.restrictFunctor_map_ofRestrict {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ X.of_restrict _ = X.of_restrict _ :=
  IsOpenImmersion.lift_fac _ _ _
#align algebraic_geometry.Scheme.restrict_functor_map_of_restrict AlgebraicGeometry.Scheme.restrictFunctor_map_ofRestrict

theorem Scheme.restrictFunctor_map_base {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.1.base = (Opens.toTopCat _).map i :=
  by
  ext a
  exact
    (congr_arg (fun f : X.restrict U.open_embedding ⟶ X => f.1.base a)
        (X.restrict_functor_map_of_restrict i) :
      _)
#align algebraic_geometry.Scheme.restrict_functor_map_base AlgebraicGeometry.Scheme.restrictFunctor_map_base

theorem Scheme.restrictFunctor_map_app_aux {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    U.OpenEmbedding.IsOpenMap.Functor.obj ((Opens.map (X.restrictFunctor.map i).1.val.base).obj W) ≤
      V.OpenEmbedding.IsOpenMap.Functor.obj W :=
  by
  simp only [← SetLike.coe_subset_coe, IsOpenMap.functor_obj_coe, Set.image_subset_iff,
    Scheme.restrict_functor_map_base, opens.map_coe, opens.inclusion_apply]
  rintro _ h
  exact ⟨_, h, rfl⟩
#align algebraic_geometry.Scheme.restrict_functor_map_app_aux AlgebraicGeometry.Scheme.restrictFunctor_map_app_aux

theorem Scheme.restrictFunctor_map_app {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.1.c.app (op W) =
      X.Presheaf.map (homOfLE <| X.restrictFunctor_map_app_aux i W).op :=
  by
  have e₁ :=
    Scheme.congr_app (X.restrict_functor_map_of_restrict i)
      (op <| V.open_embedding.is_open_map.functor.obj W)
  rw [Scheme.comp_val_c_app] at e₁ 
  have e₂ := (X.restrict_functor.map i).1.val.c.naturality (eq_to_hom W.map_functor_eq).op
  rw [← is_iso.eq_inv_comp] at e₂ 
  dsimp at e₁ e₂ ⊢
  rw [e₂, W.adjunction_counit_map_functor, ← is_iso.eq_inv_comp, is_iso.inv_comp_eq, ←
    is_iso.eq_comp_inv] at e₁ 
  simp_rw [eq_to_hom_map (opens.map _), eq_to_hom_map (IsOpenMap.functor _), ← functor.map_inv, ←
    functor.map_comp] at e₁ 
  rw [e₁]
  congr 1
#align algebraic_geometry.Scheme.restrict_functor_map_app AlgebraicGeometry.Scheme.restrictFunctor_map_app

/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps]
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.Presheaf :=
  NatIso.ofComponents
    (fun U => X.Presheaf.mapIso ((eqToIso (unop U).openEmbedding_obj_top).symm.op : _))
    (by
      intro U V i
      dsimp [-Subtype.val_eq_coe, -Scheme.restrict_functor_map_left]
      rw [X.restrict_functor_map_app, ← functor.map_comp, ← functor.map_comp]
      congr 1)
#align algebraic_geometry.Scheme.restrict_functor_Γ AlgebraicGeometry.Scheme.restrictFunctorΓ

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
    (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ≅ Y.restrict U.OpenEmbedding :=
  by
  refine' is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _
  dsimp [opens.inclusion]
  rw [coe_comp, Set.range_comp]
  dsimp
  rw [Subtype.range_coe, Subtype.range_coe]
  refine' @Set.image_preimage_eq _ _ f.1.base U.1 _
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.Scheme.restrict_map_iso AlgebraicGeometry.Scheme.restrictMapIso

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def Scheme.OpenCover.pullbackCover {X : Scheme} (𝒰 : X.OpenCover) {W : Scheme} (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback f (𝒰.map x)
  map x := pullback.fst
  f x := 𝒰.f (f.1.base x)
  Covers x :=
    by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        preserves_pullback.iso_hom_fst Scheme.forget_to_Top f (𝒰.map (𝒰.f (f.1.base x)))]
    rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
    exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance
#align algebraic_geometry.Scheme.open_cover.pullback_cover AlgebraicGeometry.Scheme.OpenCover.pullbackCover

theorem Scheme.OpenCover.iUnion_range {X : Scheme} (𝒰 : X.OpenCover) :
    (⋃ i, Set.range (𝒰.map i).1.base) = Set.univ :=
  by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact ⟨𝒰.f x, 𝒰.covers x⟩
#align algebraic_geometry.Scheme.open_cover.Union_range AlgebraicGeometry.Scheme.OpenCover.iUnion_range

theorem Scheme.OpenCover.iSup_opensRange {X : Scheme} (𝒰 : X.OpenCover) :
    (⨆ i, (𝒰.map i).opensRange) = ⊤ :=
  Opens.ext <| by rw [opens.coe_supr]; exact 𝒰.Union_range
#align algebraic_geometry.Scheme.open_cover.supr_opens_range AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange

theorem Scheme.OpenCover.compactSpace {X : Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.J]
    [H : ∀ i, CompactSpace (𝒰.obj i).carrier] : CompactSpace X.carrier :=
  by
  cases nonempty_fintype 𝒰.J
  rw [← isCompact_univ_iff, ← 𝒰.Union_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ (H i)
      (TopCat.homeoOfIso
        (as_iso
          (is_open_immersion.iso_of_range_eq (𝒰.map i)
                  (X.of_restrict (opens.open_embedding ⟨_, (𝒰.is_open i).base_open.open_range⟩))
                  subtype.range_coe.symm).Hom.1.base))
#align algebraic_geometry.Scheme.open_cover.compact_space AlgebraicGeometry.Scheme.OpenCover.compactSpace

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def Scheme.OpenCover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.OpenCover.{v₁} X)
    (𝒰₂ : Scheme.OpenCover.{v₂} X) : X.OpenCover
    where
  J := 𝒰₁.J × 𝒰₂.J
  obj ij := pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map ij := pullback.fst ≫ 𝒰₁.map ij.1
  f x := ⟨𝒰₁.f x, 𝒰₂.f x⟩
  Covers x := by
    rw [is_open_immersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩
#align algebraic_geometry.Scheme.open_cover.inter AlgebraicGeometry.Scheme.OpenCover.inter

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps J obj map]
def Scheme.openCoverOfSuprEqTop {s : Type _} (X : Scheme) (U : s → Opens X.carrier)
    (hU : (⨆ i, U i) = ⊤) : X.OpenCover where
  J := s
  obj i := X.restrict (U i).OpenEmbedding
  map i := X.of_restrict (U i).OpenEmbedding
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : opens X.carrier) by triv
    (opens.mem_supr.mp this).some
  Covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : opens X.carrier) by triv
    exact (opens.mem_supr.mp this).choose_spec
#align algebraic_geometry.Scheme.open_cover_of_supr_eq_top AlgebraicGeometry.Scheme.openCoverOfSuprEqTop

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    pullback f (Y.of_restrict U.OpenEmbedding) ≅
      X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding :=
  by
  refine' is_open_immersion.iso_of_range_eq pullback.fst (X.of_restrict _) _
  rw [is_open_immersion.range_pullback_fst_of_right]
  dsimp [opens.inclusion]
  rw [Subtype.range_coe, Subtype.range_coe]
  rfl
#align algebraic_geometry.pullback_restrict_iso_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.of_restrict _ := by
  delta pullback_restrict_iso_restrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_inv_fst AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).Hom ≫ X.of_restrict _ = pullback.fst := by
  delta pullback_restrict_iso_restrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_restrict

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ⟶ Y.restrict U.OpenEmbedding :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd
#align algebraic_geometry.morphism_restrict AlgebraicGeometry.morphismRestrict

infixl:80 " ∣_ " => morphismRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme} (f : X ⟶ Y)
    (U : Opens Y.carrier) : (pullbackRestrictIsoRestrict f U).Hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_morphism_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict

@[simp, reassoc]
theorem morphismRestrict_ι {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (f ∣_ U) ≫ Y.of_restrict U.OpenEmbedding = X.of_restrict _ ≫ f :=
  by
  delta morphism_restrict
  rw [category.assoc, pullback.condition.symm, pullback_restrict_iso_restrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_ι AlgebraicGeometry.morphismRestrict_ι

theorem isPullback_morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    IsPullback (f ∣_ U) (X.of_restrict _) (Y.of_restrict _) f :=
  by
  delta morphism_restrict
  nth_rw 1 [← category.id_comp f]
  refine'
    (is_pullback.of_horiz_is_iso ⟨_⟩).paste_horiz
      (is_pullback.of_has_pullback f (Y.of_restrict U.open_embedding)).flip
  rw [pullback_restrict_iso_restrict_inv_fst, category.comp_id]
#align algebraic_geometry.is_pullback_morphism_restrict AlgebraicGeometry.isPullback_morphismRestrict

theorem morphismRestrict_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z.carrier) :
    (f ≫ g) ∣_ U = ((f ∣_ (Opens.map g.val.base).obj U) ≫ g ∣_ U : _) :=
  by
  delta morphism_restrict
  rw [← pullback_right_pullback_fst_iso_inv_snd_snd]
  simp_rw [← category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [category.assoc]
  rw [pullback_restrict_iso_restrict_inv_fst, pullback_right_pullback_fst_iso_inv_snd_fst, ←
    pullback.condition, pullback_restrict_iso_restrict_inv_fst_assoc,
    pullback_restrict_iso_restrict_inv_fst_assoc]
  rfl
  infer_instance
#align algebraic_geometry.morphism_restrict_comp AlgebraicGeometry.morphismRestrict_comp

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens Y.carrier) : IsIso (f ∣_ U) := by
  delta morphism_restrict; infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    @coe U Y.carrier _ ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.val f) x)
    (morphismRestrict_ι f U)
#align algebraic_geometry.morphism_restrict_base_coe AlgebraicGeometry.morphismRestrict_base_coe

theorem morphismRestrict_val_base {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)
#align algebraic_geometry.morphism_restrict_val_base AlgebraicGeometry.morphismRestrict_val_base

theorem image_morphismRestrict_preimage {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier)
    (V : Opens U) :
    ((Opens.map f.val.base).obj U).OpenEmbedding.IsOpenMap.Functor.obj
        ((Opens.map (f ∣_ U).val.base).obj V) =
      (Opens.map f.val.base).obj (U.OpenEmbedding.IsOpenMap.Functor.obj V) :=
  by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ _, rfl⟩
    refine' ⟨⟨_, hx⟩, _, rfl⟩
    convert hx'
    ext1
    exact (morphism_restrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx', rfl : x = _⟩
    refine' ⟨⟨_, hx⟩, (_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    ext1
    exact morphism_restrict_base_coe f U ⟨x, hx⟩
#align algebraic_geometry.image_morphism_restrict_preimage AlgebraicGeometry.image_morphismRestrict_preimage

theorem morphismRestrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.OpenEmbedding.IsOpenMap.Functor.obj V)) ≫
        X.Presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op :=
  by
  have :=
    Scheme.congr_app (morphism_restrict_ι f U) (op (U.open_embedding.is_open_map.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this 
  have e : (opens.map U.inclusion).obj (U.open_embedding.is_open_map.functor.obj V) = V := by ext1;
    exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eq_to_hom e).op).symm.trans _).trans this
  swap; · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _; congr
  rw [← is_iso.eq_comp_inv, ← functor.map_inv, category.assoc] at this 
  rw [this]
  congr 1
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1
#align algebraic_geometry.morphism_restrict_c_app AlgebraicGeometry.morphismRestrict_c_app

theorem Γ_map_morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.Presheaf.map (eqToHom <| U.openEmbedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫
          X.Presheaf.map (eqToHom <| ((Opens.map f.val.base).obj U).openEmbedding_obj_top).op :=
  by
  rw [Scheme.Γ_map_op, morphism_restrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.Γ_map_morphism_restrict AlgebraicGeometry.Γ_map_morphismRestrict

/-- Restricting a morphism onto the the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange {X Y U : Scheme} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd : pullback f g ⟶ _) :=
  by
  let V : opens Y.carrier := g.opens_range
  let e :=
    is_open_immersion.iso_of_range_eq g (Y.of_restrict V.open_embedding) subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f (Y.of_restrict V.open_embedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [category.comp_id, category.id_comp])
      (by rw [category.comp_id, is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac])
  symm
  refine' arrow.iso_mk (as_iso t ≪≫ pullback_restrict_iso_restrict f V) e _
  rw [iso.trans_hom, as_iso_hom, ← iso.comp_inv_eq, ← cancel_mono g, arrow.mk_hom, arrow.mk_hom,
    is_open_immersion.iso_of_range_eq_inv, category.assoc, category.assoc, category.assoc,
    is_open_immersion.lift_fac, ← pullback.condition, morphism_restrict_ι,
    pullback_restrict_iso_restrict_hom_restrict_assoc, pullback.lift_fst_assoc, category.comp_id]
#align algebraic_geometry.morphism_restrict_opens_range AlgebraicGeometry.morphismRestrictOpensRange

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e)
#align algebraic_geometry.morphism_restrict_eq AlgebraicGeometry.morphismRestrictEq

/-- Restricting a morphism twice is isomorpic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.OpenEmbedding.IsOpenMap.Functor.obj V) :=
  by
  have :
    (f ∣_ U ∣_ V) ≫ (iso.refl _).Hom =
      (as_iso <|
            (pullback_restrict_iso_restrict (f ∣_ U) V).inv ≫
              (pullback_symmetry _ _).Hom ≫
                pullback.map _ _ _ _ (𝟙 _)
                    ((pullback_restrict_iso_restrict f U).inv ≫ (pullback_symmetry _ _).Hom) (𝟙 _)
                    ((category.comp_id _).trans (category.id_comp _).symm) (by simpa) ≫
                  (pullback_right_pullback_fst_iso _ _ _).Hom ≫ (pullback_symmetry _ _).Hom).Hom ≫
        pullback.snd :=
    by
    simpa only [category.comp_id, pullback_right_pullback_fst_iso_hom_fst, iso.refl_hom,
      category.assoc, pullback_symmetry_hom_comp_snd, as_iso_hom, pullback.lift_fst,
      pullback_symmetry_hom_comp_fst]
  refine'
    arrow.iso_mk' _ _ _ _ this.symm ≪≫
      (morphism_restrict_opens_range _ _).symm ≪≫ morphism_restrict_eq _ _
  ext1
  dsimp
  rw [coe_comp, Set.range_comp]
  congr
  exact Subtype.range_coe
#align algebraic_geometry.morphism_restrict_restrict AlgebraicGeometry.morphismRestrictRestrict

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction.  -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier)
    (r : Y.Presheaf.obj (op U)) :
    Arrow.mk
        (f ∣_ U ∣_
          (Y.restrict _).basicOpen (Y.Presheaf.map (eqToHom U.openEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) :=
  by
  refine' morphism_restrict_restrict _ _ _ ≪≫ morphism_restrict_eq _ _
  have e := Scheme.preimage_basic_open (Y.of_restrict U.open_embedding) r
  erw [Scheme.of_restrict_val_c_app, opens.adjunction_counit_app_self, eq_to_hom_op] at e 
  rw [← (Y.restrict U.open_embedding).basicOpen_res_eq _ (eq_to_hom U.inclusion_map_eq_top).op, ←
    comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eq_to_hom_op, eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans]
  erw [← e]
  ext1; dsimp [opens.map, opens.inclusion]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, Subtype.range_coe]
  exact Y.basic_open_le r
#align algebraic_geometry.morphism_restrict_restrict_basic_open AlgebraicGeometry.morphismRestrictRestrictBasicOpen

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    Arrow.mk (PresheafedSpace.stalkMap (f ∣_ U).1 x) ≅
      Arrow.mk (PresheafedSpace.stalkMap f.1 x.1) :=
  by
  fapply arrow.iso_mk'
  · refine' Y.restrict_stalk_iso U.open_embedding ((f ∣_ U).1 x) ≪≫ TopCat.Presheaf.stalkCongr _ _
    apply Inseparable.of_eq
    exact morphism_restrict_base_coe f U x
  · exact X.restrict_stalk_iso _ _
  · apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    simp only [TopCat.Presheaf.stalkCongr_hom, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom]
    erw [PresheafedSpace.restrict_stalk_iso_hom_eq_germ_assoc]
    erw [PresheafedSpace.stalk_map_germ_assoc _ _ ⟨_, _⟩]
    rw [TopCat.Presheaf.germ_stalk_specializes'_assoc]
    erw [PresheafedSpace.stalk_map_germ _ _ ⟨_, _⟩]
    erw [PresheafedSpace.restrict_stalk_iso_hom_eq_germ]
    rw [morphism_restrict_c_app, category.assoc, TopCat.Presheaf.germ_res]
    rfl
#align algebraic_geometry.morphism_restrict_stalk_map AlgebraicGeometry.morphismRestrictStalkMap

instance {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by delta morphism_restrict; infer_instance

end MorphismRestrict

end AlgebraicGeometry

