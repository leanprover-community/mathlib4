/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

#align_import algebraic_geometry.open_immersion.Scheme from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Open immersions of schemes

-/

set_option linter.uppercaseLean3 false

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
#align algebraic_geometry.IsOpenImmersion AlgebraicGeometry.IsOpenImmersion

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
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine' SheafedSpace.forgetToPresheafedSpace.preimageIso _
    skip
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    · exact Subtype.range_coe_subtype
    · exact Opens.openEmbedding _ -- Porting note : was `infer_instance`
#align algebraic_geometry.LocallyRingedSpace.IsOpenImmersion.Scheme AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.open_range {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f.1.base) :=
  H.base_open.open_range
#align algebraic_geometry.IsOpenImmersion.open_range AlgebraicGeometry.IsOpenImmersion.open_range

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
  /-- index set of an open cover of a scheme `X` -/
  J : Type v
  /-- the subschemes of an open cover -/
  obj : ∀ _ : J, Scheme
  /-- the embedding of subschemes to `X` -/
  map : ∀ j : J, obj j ⟶ X
  /-- given a point of `x : X`, `f x` is the index of the subscheme which contains `x`  -/
  f : X.carrier → J
  /-- the subschemes covers `X` -/
  Covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  /-- the embedding of subschemes are open immersions -/
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance
#align algebraic_geometry.Scheme.open_cover AlgebraicGeometry.Scheme.OpenCover

attribute [instance] OpenCover.IsOpen

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme) : OpenCover X where
  J := X.carrier
  obj x := Spec.obj <| Opposite.op (X.local_affine x).choose_spec.choose
  map x :=
    ((X.local_affine x).choose_spec.choose_spec.some.inv ≫ X.toLocallyRingedSpace.ofRestrict _ : _)
  f x := x
  IsOpen x := by
    apply (config := { allowSynthFailures := true }) PresheafedSpace.IsOpenImmersion.comp
    apply PresheafedSpace.IsOpenImmersion.ofRestrict
  Covers := by
    intro x
    erw [coe_comp]
    rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
    erw [Subtype.range_coe_subtype]
    exact (X.local_affine x).choose.2
    rw [← TopCat.epi_iff_surjective]
    change Epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forgetToSheafedSpace.map _))
    infer_instance
#align algebraic_geometry.Scheme.affine_cover AlgebraicGeometry.Scheme.affineCover

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps! J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X where
  J := Σ i : 𝒰.J, (f i).J
  obj x := (f x.1).obj x.2
  map x := (f x.1).map x.2 ≫ 𝒰.map x.1
  f x := ⟨_, (f _).f (𝒰.Covers x).choose⟩
  Covers x := by
    let y := (𝒰.Covers x).choose
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.Covers x).choose_spec
    rcases(f (𝒰.f x)).Covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    rw [hz, hy]
  -- Porting note : weirdly, even though no input is needed, `inferInstance` does not work
  -- `PresheafedSpace.IsOpenImmersion.comp` is marked as `instance`
  IsOpen x := PresheafedSpace.IsOpenImmersion.comp _ _
#align algebraic_geometry.Scheme.open_cover.bind AlgebraicGeometry.Scheme.OpenCover.bind

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover Y where
  J := PUnit.{v + 1}
  obj _ := X
  map _ := f
  f _ := PUnit.unit
  Covers x := by
    rw [Set.range_iff_surjective.mpr]
    all_goals try trivial
    rw [← TopCat.epi_iff_surjective]
    infer_instance
#align algebraic_geometry.Scheme.open_cover_of_is_iso AlgebraicGeometry.Scheme.openCoverOfIsIso

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : Scheme} (𝒰 : OpenCover X) (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J, obj, map
    f := fun x => e₁.symm (𝒰.f x)
    Covers := fun x => by
      rw [e₂, Scheme.comp_val_base, coe_comp, Set.range_comp, Set.range_iff_surjective.mpr,
        Set.image_univ, e₁.rightInverse_symm]
      · exact 𝒰.Covers x
      · rw [← TopCat.epi_iff_surjective]; infer_instance
    -- Porting note : weirdly, even though no input is needed, `inferInstance` does not work
    -- `PresheafedSpace.IsOpenImmersion.comp` is marked as `instance`
    IsOpen := fun i => by rw [e₂]; exact PresheafedSpace.IsOpenImmersion.comp _ _ }
#align algebraic_geometry.Scheme.open_cover.copy AlgebraicGeometry.Scheme.OpenCover.copy

-- Porting note : need more hint on universe level
/-- The pushforward of an open cover along an isomorphism. -/
@[simps! J obj map]
def OpenCover.pushforwardIso {X Y : Scheme.{u}} (𝒰 : OpenCover.{v} X) (f : X ⟶ Y) [IsIso f] :
    OpenCover.{v} Y :=
  ((openCoverOfIsIso.{v, u} f).bind fun _ => 𝒰).copy 𝒰.J _ _
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
-- attribute [local reducible] CommRingCat.of CommRingCat.ofHom

instance val_base_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_isIso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.Scheme.val_base_isIso

instance basic_open_isOpenImmersion {R : CommRingCat} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_openEmbedding (Localization.Away f) f : _)
  · intro x
    exact Spec_map_localization_isIso R (Submonoid.powers f) x
#align algebraic_geometry.Scheme.basic_open_IsOpenImmersion AlgebraicGeometry.Scheme.basic_open_isOpenImmersion

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat) : OpenCover (Spec.obj (Opposite.op R)) where
  J := R
  obj r := Spec.obj (Opposite.op <| CommRingCat.of <| Localization.Away r)
  map r := Spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f _ := 1
  Covers r := by
    rw [Set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · -- Porting note : need more hand holding here because Lean knows that
      -- `CommRing.ofHom ...` is iso, but without `ofHom` Lean does not know what to do
      change Epi (Spec.map (CommRingCat.ofHom (algebraMap _ _)).op).1.base
      infer_instance
  IsOpen x := AlgebraicGeometry.Scheme.basic_open_isOpenImmersion x
#align algebraic_geometry.Scheme.affine_basis_cover_of_affine AlgebraicGeometry.Scheme.affineBasisCoverOfAffine

/-- We may bind the basic open sets of an open affine cover to form an affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _
#align algebraic_geometry.Scheme.affine_basis_cover AlgebraicGeometry.Scheme.affineBasisCover

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2
#align algebraic_geometry.Scheme.affine_basis_cover_ring AlgebraicGeometry.Scheme.affineBasisCoverRing

theorem affineBasisCover_obj (X : Scheme) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = Spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl
#align algebraic_geometry.Scheme.affine_basis_cover_obj AlgebraicGeometry.Scheme.affineBasisCover_obj

theorem affineBasisCover_map_range (X : Scheme) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 := by
  erw [coe_comp, Set.range_comp]
  -- Porting note : `congr` fails to see the goal is comparing image of the same function
  refine congr_arg (_ '' ·) ?_
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)
#align algebraic_geometry.Scheme.affine_basis_cover_map_range AlgebraicGeometry.Scheme.affineBasisCover_map_range

theorem affineBasisCover_is_basis (X : Scheme) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base} := by
  apply TopologicalSpace.isTopologicalBasis_of_open_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.open_range (X.affineBasisCover.map a)
  · rintro a U haU hU
    rcases X.affineCover.Covers a with ⟨x, e⟩
    let U' := (X.affineCover.map (X.affineCover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by rw [← e] at haU; exact haU
    rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affineCover.map (X.affineCover.f a)).1.base.continuous_toFun.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine' ⟨_, ⟨⟨_, s⟩, rfl⟩, _, _⟩ <;> erw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU
#align algebraic_geometry.Scheme.affine_basis_cover_is_basis AlgebraicGeometry.Scheme.affineBasisCover_is_basis

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! obj map]
def OpenCover.finiteSubcover {X : Scheme} (𝒰 : OpenCover X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (IsOpenImmersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.Covers x)
  let t := this.choose
  have h : ∀ x : X, ∃ y : t, x ∈ Set.range (𝒰.map (𝒰.f y)).1.base := by
    intro x
    have h' : x ∈ (⊤ : Set X) := trivial
    rw [← Classical.choose_spec this, Set.mem_iUnion] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t
      obj := fun x => 𝒰.obj (𝒰.f x.1)
      map := fun x => 𝒰.map (𝒰.f x.1)
      f := fun x => (h x).choose
      Covers := fun x => (h x).choose_spec }
#align algebraic_geometry.Scheme.open_cover.finite_subcover AlgebraicGeometry.Scheme.OpenCover.finiteSubcover

instance [H : CompactSpace X] : Fintype 𝒰.finiteSubcover.J := by
  delta OpenCover.finiteSubcover; infer_instance

end Scheme

end OpenCover

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace CommRingCat.{u}} (Y : Scheme.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨_, ⟨i, rfl⟩, hx, hi⟩ :=
    Y.affineBasisCover_is_basis.exists_subset_of_mem_open (Set.mem_range_self x)
      H.base_open.open_range
  use Y.affineBasisCoverRing i
  use LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f) _ hi
  constructor
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]; exact hx
  · delta LocallyRingedSpace.IsOpenImmersion.lift; infer_instance
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toScheme

@[simp]
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.to_Scheme_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toScheme_toLocallyRingedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  toLocallyRingedSpaceHom _ f
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.to_Scheme_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom

@[simp]
theorem toSchemeHom_val : (toSchemeHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.to_Scheme_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom_val

instance toSchemeHom_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (toSchemeHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.to_Scheme_hom_IsOpenImmersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.toSchemeHom_isOpenImmersionₓ

theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by
  cases X; cases Y; congr
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.Scheme_eq_of_LocallyRingedSpace_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_eq_of_locallyRingedSpace_eq

theorem scheme_toScheme {X Y : Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    toScheme Y f.1 = X := by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.Scheme_to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_toScheme

end ToScheme

end PresheafedSpace.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps!]
def Scheme.restrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X} (h : OpenEmbedding f) :
    Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
#align algebraic_geometry.Scheme.restrict AlgebraicGeometry.Scheme.restrict

/-- The canonical map from the restriction to the supspace. -/
@[simps!]
def Scheme.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X}
    (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.ofRestrict h
#align algebraic_geometry.Scheme.ofRestrict AlgebraicGeometry.Scheme.ofRestrict

instance IsOpenImmersion.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X}
    (h : OpenEmbedding f) : IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance
#align algebraic_geometry.IsOpenImmersion.ofRestrict AlgebraicGeometry.IsOpenImmersion.ofRestrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  @LocallyRingedSpace.IsOpenImmersion.of_isIso _ _ _
    (show IsIso ((inducedFunctor _).map g) by infer_instance)
#align algebraic_geometry.IsOpenImmersion.of_is_iso AlgebraicGeometry.IsOpenImmersion.of_isIso

theorem to_iso {X Y : Scheme} (f : X ⟶ Y) [h : IsOpenImmersion f] [Epi f.1.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.1 h _) _
#align algebraic_geometry.IsOpenImmersion.to_iso AlgebraicGeometry.IsOpenImmersion.to_iso

theorem of_stalk_iso {X Y : Scheme} (f : X ⟶ Y) (hf : OpenEmbedding f.1.base)
    [∀ x, IsIso (PresheafedSpace.stalkMap f.1 x)] : IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.1 hf
#align algebraic_geometry.IsOpenImmersion.of_stalk_iso AlgebraicGeometry.IsOpenImmersion.of_stalk_iso

theorem iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  ⟨fun H => ⟨H.1, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.of_stalk_iso _ _ f h₁ h₂⟩
#align algebraic_geometry.IsOpenImmersion.iff_stalk_iso AlgebraicGeometry.IsOpenImmersion.iff_stalk_iso

theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.1.base :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.to_iso _ _ f h₁ h₂⟩
#align algebraic_geometry.is_iso_iff_IsOpenImmersion AlgebraicGeometry.isIso_iff_isOpenImmersion

theorem _root_.AlgebraicGeometry.isIso_iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) := by
  rw [isIso_iff_isOpenImmersion, IsOpenImmersion.iff_stalk_iso, and_comm, ← and_assoc]
  refine' and_congr ⟨_, _⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to
      IsIso
        (TopCat.isoOfHomeo
            (Homeomorph.homeomorphOfContinuousOpen
              (Equiv.ofBijective _ ⟨h₂.inj, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
              h₂.isOpenMap)).hom
    infer_instance
  · intro H; exact ⟨inferInstance, (TopCat.homeoOfIso (asIso f.1.base)).openEmbedding⟩
#align algebraic_geometry.is_iso_iff_stalk_iso AlgebraicGeometry.isIso_iff_stalk_iso

/-- An open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ (Z.restrict H.base_open : _) :=
  ⟨(LocallyRingedSpace.IsOpenImmersion.isoRestrict H).hom,
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict H).inv,
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict H).hom_inv_id,
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict H).inv_hom_id⟩
#align algebraic_geometry.IsOpenImmersion.iso_restrict AlgebraicGeometry.IsOpenImmersion.isoRestrict

local notation "forget" => Scheme.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (inducedFunctor _).mono_of_mono_map (show @Mono LocallyRingedSpace _ _ _ f by infer_instance)
#align algebraic_geometry.IsOpenImmersion.mono AlgebraicGeometry.IsOpenImmersion.mono

instance forget_map_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.IsOpenImmersion.forget_map_IsOpenImmersion AlgebraicGeometry.IsOpenImmersion.forget_map_isOpenImmersion

instance hasLimit_cospan_forget_of_left :
    HasLimit (cospan f g ⋙ Scheme.forgetToLocallyRingedSpace) := by
  apply @hasLimitOfIso _ _ _ _ _ _ ?_ (diagramIsoCospan.{u} _).symm
  change HasLimit (cospan ((forget).map f) ((forget).map g))
  infer_instance
#align algebraic_geometry.IsOpenImmersion.has_limit_cospan_forget_of_left AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left

open CategoryTheory.Limits.WalkingCospan

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance
#align algebraic_geometry.IsOpenImmersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left'

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  apply @hasLimitOfIso _ _ _ _ _ _ ?_ (diagramIsoCospan.{u} _).symm
  change HasLimit (cospan ((forget).map g) ((forget).map f))
  infer_instance
#align algebraic_geometry.IsOpenImmersion.has_limit_cospan_forget_of_right AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance
#align algebraic_geometry.IsOpenImmersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.snd LocallyRingedSpace _ _ _ _ f g _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.IsOpenImmersion.forget_creates_pullback_of_left AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.fst LocallyRingedSpace _ _ _ _ g f _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.IsOpenImmersion.forget_creates_pullback_of_right AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfRight

instance forgetPreservesOfLeft : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit _ _
#align algebraic_geometry.IsOpenImmersion.forget_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfLeft

instance forgetPreservesOfRight : PreservesLimit (cospan g f) forget :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.IsOpenImmersion.forget_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfRight

instance hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
#align algebraic_geometry.IsOpenImmersion.has_pullback_of_left AlgebraicGeometry.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget
#align algebraic_geometry.IsOpenImmersion.has_pullback_of_right AlgebraicGeometry.IsOpenImmersion.hasPullback_of_right

instance pullback_snd_of_left : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  rw [← this]
  change LocallyRingedSpace.IsOpenImmersion _
  infer_instance
#align algebraic_geometry.IsOpenImmersion.pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.pullback_snd_of_left

instance pullback_fst_of_right : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  -- Porting note : was just `infer_instance`, it is a bit weird that no explicit class instance is
  -- provided but still class inference fail to find this
  exact LocallyRingedSpace.IsOpenImmersion.comp (H := inferInstance) _
#align algebraic_geometry.IsOpenImmersion.pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  -- Porting note : was just `infer_instance`, it is a bit weird that no explicit class instance is
  -- provided but still class inference fail to find this
  exact LocallyRingedSpace.IsOpenImmersion.comp (H := inferInstance) _
#align algebraic_geometry.IsOpenImmersion.pullback_to_base AlgebraicGeometry.IsOpenImmersion.pullback_to_base

instance forgetToTopPreservesOfLeft : PreservesLimit (cospan f g) Scheme.forgetToTop := by
  delta Scheme.forgetToTop
  apply @Limits.compPreservesLimit (K := cospan f g) (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  apply @preservesLimitOfIsoDiagram (F := _) _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace.forgetToTop]
  infer_instance
#align algebraic_geometry.IsOpenImmersion.forget_to_Top_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfLeft

instance forgetToTopPreservesOfRight : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.IsOpenImmersion.forget_to_Top_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfRight

theorem range_pullback_snd_of_left :
    Set.range (pullback.snd : pullback f g ⟶ Y).1.base =
      ((Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩).1 := by
  rw [←
    show _ = (pullback.snd : pullback f g ⟶ _).1.base from
      PreservesPullback.iso_hom_snd Scheme.forgetToTop f g]
  -- Porting note : was `rw`
  erw [coe_comp]
  rw [Set.range_comp, Set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _)]
  -- Porting note : was `rw`
  erw [TopCat.pullback_snd_image_fst_preimage]
  rw [Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.IsOpenImmersion.range_pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_snd_of_left

theorem range_pullback_fst_of_right :
    Set.range (pullback.fst : pullback g f ⟶ Y).1.base =
      ((Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩).1 := by
  rw [←
    show _ = (pullback.fst : pullback g f ⟶ _).1.base from
      PreservesPullback.iso_hom_fst Scheme.forgetToTop g f]
  -- Porting note : was `rw`
  erw [coe_comp]
  rw [Set.range_comp, Set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _)]
  -- Porting note : was `rw`
  erw [TopCat.pullback_fst_image_snd_preimage]
  rw [Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.IsOpenImmersion.range_pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_fst_of_right

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      Set.range f.1.base ∩ Set.range g.1.base := by
  rw [pullback.condition, Scheme.comp_val_base, coe_comp, Set.range_comp,
    range_pullback_snd_of_left, Opens.carrier_eq_coe,
    Opens.map_obj, Opens.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm]
#align algebraic_geometry.IsOpenImmersion.range_pullback_to_base_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base =
      Set.range g.1.base ∩ Set.range f.1.base := by
  rw [Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_fst_of_right, Opens.map_obj,
    Opens.carrier_eq_coe, Opens.coe_mk, Set.image_preimage_eq_inter_range, Set.inter_comm]
#align algebraic_geometry.IsOpenImmersion.range_pullback_to_base_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  LocallyRingedSpace.IsOpenImmersion.lift f g H'
#align algebraic_geometry.IsOpenImmersion.lift AlgebraicGeometry.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac f g H'
#align algebraic_geometry.IsOpenImmersion.lift_fac AlgebraicGeometry.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq f g H' l hl
#align algebraic_geometry.IsOpenImmersion.lift_uniq AlgebraicGeometry.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range are isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp
#align algebraic_geometry.IsOpenImmersion.iso_of_range_eq AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev _root_.AlgebraicGeometry.Scheme.Hom.opensFunctor {X Y : Scheme} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : Opens X ⥤ Opens Y :=
  H.openFunctor
#align algebraic_geometry.Scheme.hom.opens_functor AlgebraicGeometry.Scheme.Hom.opensFunctor

/-- The isomorphism `Γ(X, U) ⟶ Γ(Y, f(U))` induced by an open immersion `f : X ⟶ Y`. -/
def _root_.AlgebraicGeometry.Scheme.Hom.invApp {X Y : Scheme} (f : X ⟶ Y)
    [H : IsOpenImmersion f] (U) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (f.opensFunctor.obj U)) :=
  H.invApp U
#align algebraic_geometry.Scheme.hom.inv_app AlgebraicGeometry.Scheme.Hom.invApp

theorem app_eq_inv_app_app_of_comp_eq_aux {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U) :
    (Opens.map f.1.base).obj V = (Opens.map fg.1.base).obj (g.opensFunctor.obj V) := by
  subst H
  rw [Scheme.comp_val_base, Opens.map_comp_obj]
  congr 1
  ext1
  exact (Set.preimage_image_eq _ h.base_open.inj).symm
#align algebraic_geometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_invApp_app_of_comp_eq {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U) :
    f.1.c.app (op V) =
      Scheme.Hom.invApp g _ ≫
        fg.1.c.app _ ≫
          Y.presheaf.map
            (eqToHom <| IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux f g fg H V).op := by
  subst H
  rw [Scheme.comp_val_c_app, Category.assoc, Scheme.Hom.invApp,
    PresheafedSpace.IsOpenImmersion.invApp_app_assoc, f.val.c.naturality_assoc,
    TopCat.Presheaf.pushforwardObj_map, ← Functor.map_comp]
  convert (Category.comp_id <| f.1.c.app (op V)).symm
  convert Y.presheaf.map_id _
#align algebraic_geometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq AlgebraicGeometry.IsOpenImmersion.app_eq_invApp_app_of_comp_eq

theorem lift_app {X Y U : Scheme} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
    (V : Opens U) :
    (IsOpenImmersion.lift f g H).1.c.app (op V) =
      Scheme.Hom.invApp f _ ≫
        g.1.c.app _ ≫
          X.presheaf.map
            (eqToHom <|
                IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux _ _ _
                  (IsOpenImmersion.lift_fac f g H).symm V).op :=
  -- Porting note : `(lift_fac ...).symm` was done by unification magic in Lean3.
  IsOpenImmersion.app_eq_invApp_app_of_comp_eq _ _ _ (lift_fac _ _ H).symm _
#align algebraic_geometry.IsOpenImmersion.lift_app AlgebraicGeometry.IsOpenImmersion.lift_app

end IsOpenImmersion

namespace Scheme

theorem image_basicOpen {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X}
    (r : X.presheaf.obj (op U)) :
    f.opensFunctor.obj (X.basicOpen r) = Y.basicOpen (Scheme.Hom.invApp f U r) := by
  have e := Scheme.preimage_basicOpen f (Scheme.Hom.invApp f U r)
  rw [Scheme.Hom.invApp] at e
  -- Porting note : was `rw`
  erw [PresheafedSpace.IsOpenImmersion.invApp_app_apply] at e
  rw [Scheme.basicOpen_res, inf_eq_right.mpr _] at e
  rw [← e]
  ext1
  -- Porting note : this `dsimp` was not necessary
  dsimp [Opens.map]
  refine' Set.image_preimage_eq_inter_range.trans _
  erw [Set.inter_eq_left_iff_subset]
  refine' Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  refine' le_trans (Scheme.basicOpen_le _ _) (le_of_eq _)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm
#align algebraic_geometry.Scheme.image_basic_open AlgebraicGeometry.Scheme.image_basicOpen

/-- The image of an open immersion as an open set. -/
@[simps]
def Hom.opensRange {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y :=
  ⟨_, H.base_open.open_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.Scheme.Hom.opensRange

end Scheme

section

variable (X : Scheme)

-- Porting note : `simps` can't synthesize `obj_left, obj_hom, mapLeft`
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
-- @[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor : Opens X ⥤ Over X where
  obj U := Over.mk (X.ofRestrict U.openEmbedding)
  map {U V} i :=
    Over.homMk
      (IsOpenImmersion.lift (X.ofRestrict _) (X.ofRestrict _) <| by
          dsimp [ofRestrict, LocallyRingedSpace.ofRestrict, Opens.inclusion]
          rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Subtype.range_val, Subtype.range_val]
          exact i.le)
      (IsOpenImmersion.lift_fac _ _ _)
  map_id U := by
    ext1
    dsimp only [Over.homMk_left, Over.id_left]
    rw [← cancel_mono (X.ofRestrict U.openEmbedding), Category.id_comp,
      IsOpenImmersion.lift_fac]
  map_comp {U V W} i j := by
    ext1
    dsimp only [Over.homMk_left, Over.comp_left]
    rw [← cancel_mono (X.ofRestrict W.openEmbedding), Category.assoc]
    iterate 3 rw [IsOpenImmersion.lift_fac]
#align algebraic_geometry.Scheme.restrict_functor AlgebraicGeometry.Scheme.restrictFunctor

@[simp] lemma Scheme.restrictFunctor_obj_left (U : Opens X) :
  (X.restrictFunctor.obj U).left = (X.restrict U.openEmbedding) := rfl

@[simp] lemma Scheme.restrictFunctor_obj_hom (U : Opens X) :
  (X.restrictFunctor.obj U).hom = (X.ofRestrict U.openEmbedding) := rfl

@[simp] lemma Scheme.restrictFunctor_map_left {U V : Opens X} (i : U ⟶ V) :
  ((X.restrictFunctor.map i).left) =
  IsOpenImmersion.lift (X.ofRestrict V.openEmbedding) (X.ofRestrict U.openEmbedding) (by
    dsimp [ofRestrict, LocallyRingedSpace.ofRestrict, Opens.inclusion]
    rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Subtype.range_val, Subtype.range_val]
    exact i.le) := rfl

-- Porting note : the `by ...` used to be automatically done by unification magic
@[reassoc]
theorem Scheme.restrictFunctor_map_ofRestrict {U V : Opens X} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ X.ofRestrict _ = X.ofRestrict _ :=
  IsOpenImmersion.lift_fac _ _ (by
    dsimp [ofRestrict, LocallyRingedSpace.ofRestrict, Opens.inclusion]
    rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Subtype.range_val, Subtype.range_val]
    exact i.le)
#align algebraic_geometry.Scheme.restrict_functor_map_ofRestrict AlgebraicGeometry.Scheme.restrictFunctor_map_ofRestrict

theorem Scheme.restrictFunctor_map_base {U V : Opens X} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.1.base = (Opens.toTopCat _).map i := by
  ext a; refine Subtype.ext ?_ -- Porting note : `ext` did not pick up `Subtype.ext`
  exact (congr_arg (fun f : X.restrict U.openEmbedding ⟶ X => f.1.base a)
        (X.restrictFunctor_map_ofRestrict i))
#align algebraic_geometry.Scheme.restrict_functor_map_base AlgebraicGeometry.Scheme.restrictFunctor_map_base

theorem Scheme.restrictFunctor_map_app_aux {U V : Opens X} (i : U ⟶ V) (W : Opens V) :
    U.openEmbedding.isOpenMap.functor.obj ((Opens.map (X.restrictFunctor.map i).1.val.base).obj W) ≤
      V.openEmbedding.isOpenMap.functor.obj W := by
  simp only [← SetLike.coe_subset_coe, IsOpenMap.functor_obj_coe, Set.image_subset_iff,
    Scheme.restrictFunctor_map_base, Opens.map_coe, Opens.inclusion_apply]
  rintro _ h
  exact ⟨_, h, rfl⟩
#align algebraic_geometry.Scheme.restrict_functor_map_app_aux AlgebraicGeometry.Scheme.restrictFunctor_map_app_aux

theorem Scheme.restrictFunctor_map_app {U V : Opens X} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.1.c.app (op W) =
      X.presheaf.map (homOfLE <| X.restrictFunctor_map_app_aux i W).op := by
  have e₁ :=
    Scheme.congr_app (X.restrictFunctor_map_ofRestrict i)
      (op <| V.openEmbedding.isOpenMap.functor.obj W)
  rw [Scheme.comp_val_c_app] at e₁
  -- Porting note : `Opens.map_functor_eq` need more help
  have e₂ := (X.restrictFunctor.map i).1.val.c.naturality (eqToHom <| W.map_functor_eq (U := V)).op
  rw [← IsIso.eq_inv_comp] at e₂
  dsimp at e₁ e₂ ⊢
  rw [e₂, W.adjunction_counit_map_functor (U := V), ← IsIso.eq_inv_comp, IsIso.inv_comp_eq,
    ← IsIso.eq_comp_inv] at e₁
  simp_rw [eqToHom_map (Opens.map _), eqToHom_map (IsOpenMap.functor _), ← Functor.map_inv,
    ← Functor.map_comp] at e₁
  rw [e₁]
  congr 1
#align algebraic_geometry.Scheme.restrict_functor_map_app AlgebraicGeometry.Scheme.restrictFunctor_map_app

/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps!]
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).openEmbedding_obj_top).symm.op : _))
    (by
      intro U V i
      dsimp [-Scheme.restrictFunctor_map_left]
      rw [X.restrictFunctor_map_app, ← Functor.map_comp, ← Functor.map_comp]
      congr 1)
#align algebraic_geometry.Scheme.restrict_functor_Γ AlgebraicGeometry.Scheme.restrictFunctorΓ

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
    (U : Opens Y) :
    X.restrict ((Opens.map f.1.base).obj U).openEmbedding ≅ Y.restrict U.openEmbedding := by
  apply IsOpenImmersion.isoOfRangeEq (f := X.ofRestrict _ ≫ f)
    (H := PresheafedSpace.IsOpenImmersion.comp (hf := inferInstance) (hg := inferInstance))
    (Y.ofRestrict _) _
  dsimp [Opens.inclusion]
  rw [coe_comp, Set.range_comp, ContinuousMap.coe_mk, ContinuousMap.coe_mk]
  dsimp
  rw [Subtype.range_val, Subtype.range_coe]
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
  Covers x := by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f (𝒰.map (𝒰.f (f.1.base x)))]
    -- Porting note : `rw` to `erw` on this single lemma
    erw [coe_comp]
    rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    obtain ⟨y, h⟩ := 𝒰.Covers (f.1.base x)
    exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance
#align algebraic_geometry.Scheme.open_cover.pullback_cover AlgebraicGeometry.Scheme.OpenCover.pullbackCover

theorem Scheme.OpenCover.iUnion_range {X : Scheme} (𝒰 : X.OpenCover) :
    ⋃ i, Set.range (𝒰.map i).1.base = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact ⟨𝒰.f x, 𝒰.Covers x⟩
#align algebraic_geometry.Scheme.open_cover.Union_range AlgebraicGeometry.Scheme.OpenCover.iUnion_range

theorem Scheme.OpenCover.iSup_opensRange {X : Scheme} (𝒰 : X.OpenCover) :
    ⨆ i, Scheme.Hom.opensRange (𝒰.map i) = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range
#align algebraic_geometry.Scheme.open_cover.supr_opens_range AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange

theorem Scheme.OpenCover.compactSpace {X : Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.J]
    [H : ∀ i, CompactSpace (𝒰.obj i)] : CompactSpace X := by
  cases nonempty_fintype 𝒰.J
  rw [← isCompact_univ_iff, ← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.map i)
                  (X.ofRestrict (Opens.openEmbedding ⟨_, (𝒰.IsOpen i).base_open.open_range⟩))
                  Subtype.range_coe.symm).hom.1.base))
#align algebraic_geometry.Scheme.open_cover.compact_space AlgebraicGeometry.Scheme.OpenCover.compactSpace

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def Scheme.OpenCover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.OpenCover.{v₁} X)
    (𝒰₂ : Scheme.OpenCover.{v₂} X) : X.OpenCover where
  J := 𝒰₁.J × 𝒰₂.J
  obj ij := pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map ij := pullback.fst ≫ 𝒰₁.map ij.1
  f x := ⟨𝒰₁.f x, 𝒰₂.f x⟩
  Covers x := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.Covers x, 𝒰₂.Covers x⟩
  -- Porting note : was automatic
  IsOpen x := PresheafedSpace.IsOpenImmersion.comp (hf := inferInstance) (hg := (𝒰₁.IsOpen _))
#align algebraic_geometry.Scheme.open_cover.inter AlgebraicGeometry.Scheme.OpenCover.inter

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! J obj map]
def Scheme.openCoverOfSuprEqTop {s : Type*} (X : Scheme) (U : s → Opens X)
    (hU : ⨆ i, U i = ⊤) : X.OpenCover where
  J := s
  obj i := X.restrict (U i).openEmbedding
  map i := X.ofRestrict (U i).openEmbedding
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X) by triv
    (Opens.mem_iSup.mp this).choose
  Covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X) by triv
    exact (Opens.mem_iSup.mp this).choose_spec
#align algebraic_geometry.Scheme.open_cover_of_supr_eq_top AlgebraicGeometry.Scheme.openCoverOfSuprEqTop

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    pullback f (Y.ofRestrict U.openEmbedding) ≅
      X.restrict ((Opens.map f.1.base).obj U).openEmbedding := by
  refine' IsOpenImmersion.isoOfRangeEq pullback.fst (X.ofRestrict _) _
  rw [IsOpenImmersion.range_pullback_fst_of_right]
  dsimp [Opens.inclusion]
  rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Subtype.range_val, Subtype.range_coe]
  rfl
#align algebraic_geometry.pullback_restrict_iso_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.ofRestrict _ := by
  delta pullbackRestrictIsoRestrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_inv_fst AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    (pullbackRestrictIsoRestrict f U).hom ≫ X.ofRestrict _ = pullback.fst := by
  delta pullbackRestrictIsoRestrict; simp
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_restrict

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    X.restrict ((Opens.map f.1.base).obj U).openEmbedding ⟶ Y.restrict U.openEmbedding :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd
#align algebraic_geometry.morphism_restrict AlgebraicGeometry.morphismRestrict

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:80 " ∣_ " => morphismRestrict

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme} (f : X ⟶ Y)
    (U : Opens Y) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_morphism_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict

@[simp, reassoc]
theorem morphismRestrict_ι {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    (f ∣_ U) ≫ Y.ofRestrict U.openEmbedding = X.ofRestrict _ ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_ι AlgebraicGeometry.morphismRestrict_ι

theorem isPullback_morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    IsPullback (f ∣_ U) (X.ofRestrict _) (Y.ofRestrict _) f := by
  delta morphismRestrict
  rw [← Category.id_comp f]
  refine'
    (IsPullback.of_horiz_isIso ⟨_⟩).paste_horiz
      (IsPullback.of_hasPullback f (Y.ofRestrict U.openEmbedding)).flip
  -- Porting note : changed `rw` to `erw`
  erw [pullbackRestrictIsoRestrict_inv_fst]; rw [Category.comp_id]
#align algebraic_geometry.is_pullback_morphism_restrict AlgebraicGeometry.isPullback_morphismRestrict

theorem morphismRestrict_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = ((f ∣_ (Opens.map g.val.base).obj U) ≫ g ∣_ U : _) := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_comp AlgebraicGeometry.morphismRestrict_comp

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens Y) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) (x) :
    @Coe.coe U Y (⟨fun x => x.1⟩) ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.val f) x)
    (morphismRestrict_ι f U)
#align algebraic_geometry.morphism_restrict_base_coe AlgebraicGeometry.morphismRestrict_base_coe

theorem morphismRestrict_val_base {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)
#align algebraic_geometry.morphism_restrict_val_base AlgebraicGeometry.morphismRestrict_val_base

theorem image_morphismRestrict_preimage {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y)
    (V : Opens U) :
    ((Opens.map f.val.base).obj U).openEmbedding.isOpenMap.functor.obj
        ((Opens.map (f ∣_ U).val.base).obj V) =
      (Opens.map f.val.base).obj (U.openEmbedding.isOpenMap.functor.obj V) := by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ V, rfl⟩
    refine' ⟨⟨_, hx⟩, _, rfl⟩
    -- Porting note : this rewrite was not necessary
    rw [SetLike.mem_coe]
    convert hx'
    -- Porting note : `ext1` is not compiling
    refine Subtype.ext ?_
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx' : _ ∈ V.1, rfl : x = _⟩
    refine' ⟨⟨_, hx⟩, (_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    -- Porting note : `ext1` is compiling
    refine Subtype.ext ?_
    exact morphismRestrict_base_coe f U ⟨x, hx⟩
#align algebraic_geometry.image_morphism_restrict_preimage AlgebraicGeometry.image_morphismRestrict_preimage

theorem morphismRestrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.openEmbedding.isOpenMap.functor.obj V)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  have :=
    Scheme.congr_app (morphismRestrict_ι f U) (op (U.openEmbedding.isOpenMap.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this
  have e : (Opens.map U.inclusion).obj (U.openEmbedding.isOpenMap.functor.obj V) = V := by
    ext1; exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eqToHom e).op).symm.trans ?_).trans this
  · rw [← IsIso.eq_comp_inv, ← Functor.map_inv, Category.assoc] at this
    rw [this]
    congr 1
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    congr 1
  · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _
    congr 1
#align algebraic_geometry.morphism_restrict_c_app AlgebraicGeometry.morphismRestrict_c_app

theorem Γ_map_morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.presheaf.map (eqToHom <| U.openEmbedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫
          X.presheaf.map (eqToHom <| ((Opens.map f.val.base).obj U).openEmbedding_obj_top).op := by
  rw [Scheme.Γ_map_op, morphismRestrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.Γ_map_morphism_restrict AlgebraicGeometry.Γ_map_morphismRestrict

/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange {X Y U : Scheme} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ Scheme.Hom.opensRange g) ≅ Arrow.mk (pullback.snd : pullback f g ⟶ _) := by
  let V : Opens Y := Scheme.Hom.opensRange g
  let e :=
    IsOpenImmersion.isoOfRangeEq g (Y.ofRestrict V.openEmbedding) Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f (Y.ofRestrict V.openEmbedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom, IsOpenImmersion.lift_fac])
  symm
  refine' Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e _
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g, Arrow.mk_hom, Arrow.mk_hom,
    IsOpenImmersion.isoOfRangeEq_inv, Category.assoc, Category.assoc, Category.assoc,
    IsOpenImmersion.lift_fac, ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_restrict_assoc, pullback.lift_fst_assoc, Category.comp_id]
#align algebraic_geometry.morphism_restrict_opens_range AlgebraicGeometry.morphismRestrictOpensRange

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)
#align algebraic_geometry.morphism_restrict_eq AlgebraicGeometry.morphismRestrictEq

-- Porting note : this does not compile under 200000 heart beats. The proof is more or less
-- preserved with some morphisms named so that instances about them can be made manually.
set_option maxHeartbeats 350000 in
/-- Restricting a morphism twice is isomorphic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) (V : Opens U) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.openEmbedding.isOpenMap.functor.obj V) := by
  set g := ((Y.restrict U.openEmbedding).ofRestrict (V.openEmbedding (X := TopCat.of U)) ≫
    Y.ofRestrict U.openEmbedding)
  have i1 : IsOpenImmersion g := PresheafedSpace.IsOpenImmersion.comp _ _
  have i2 : HasPullback f g := IsOpenImmersion.hasPullback_of_right g f
  set h : _ ⟶ pullback f g :=
    (pullbackRestrictIsoRestrict (f ∣_ U) V).inv ≫
      (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _)
        ((pullbackRestrictIsoRestrict f U).inv ≫ (pullbackSymmetry _ _).hom) (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (by aesop_cat) ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫ (pullbackSymmetry _ _).hom
  have i3 : IsIso h
  · repeat
      apply (config := { allowSynthFailures := true }) IsIso.comp_isIso
  have : (f ∣_ U ∣_ V) ≫ (Iso.refl _).hom = (asIso h).hom ≫ pullback.snd (f := f) (g := g)
  · simp only [Category.comp_id, pullbackRightPullbackFstIso_hom_fst, Iso.refl_hom,
      Category.assoc, pullbackSymmetry_hom_comp_snd, asIso_hom, pullback.lift_fst,
      pullbackSymmetry_hom_comp_fst]
    rfl
  refine'
    Arrow.isoMk' _ _ _ _ this.symm ≪≫
      (morphismRestrictOpensRange _ _).symm ≪≫ morphismRestrictEq _ _
  ext1
  dsimp
  rw [coe_comp, Set.range_comp]
  apply congr_arg (U.inclusion '' ·)
  exact Subtype.range_val
#align algebraic_geometry.morphism_restrict_restrict AlgebraicGeometry.morphismRestrictRestrict

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction.  -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y)
    (r : Y.presheaf.obj (op U)) :
    Arrow.mk
        (f ∣_ U ∣_
          (Y.restrict _).basicOpen (Y.presheaf.map (eqToHom U.openEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine' morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ _
  have e := Scheme.preimage_basicOpen (Y.ofRestrict U.openEmbedding) r
  erw [Scheme.ofRestrict_val_c_app, Opens.adjunction_counit_app_self, eqToHom_op] at e
  rw [← (Y.restrict U.openEmbedding).basicOpen_res_eq _ (eqToHom U.inclusion_map_eq_top).op]
  erw [← comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eqToHom_op, eqToHom_op, eqToHom_map, eqToHom_trans]
  erw [← e]
  ext1; dsimp [Opens.map, Opens.inclusion]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, ContinuousMap.coe_mk,
    Subtype.range_val]
  exact Y.basicOpen_le r
#align algebraic_geometry.morphism_restrict_restrict_basic_open AlgebraicGeometry.morphismRestrictRestrictBasicOpen

set_option maxHeartbeats 500000 in
/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) (x) :
    Arrow.mk (PresheafedSpace.stalkMap (f ∣_ U).1 x) ≅
      Arrow.mk (PresheafedSpace.stalkMap f.1 x.1) := by
  fapply Arrow.isoMk'
  · refine' Y.restrictStalkIso U.openEmbedding ((f ∣_ U).1.1 x) ≪≫ TopCat.Presheaf.stalkCongr _ _
    apply Inseparable.of_eq
    exact morphismRestrict_base_coe f U x
  · exact X.restrictStalkIso (Opens.openEmbedding _) _
  · apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    simp only [TopCat.Presheaf.stalkCongr_hom, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom]
    erw [PresheafedSpace.restrictStalkIso_hom_eq_germ_assoc]
    erw [PresheafedSpace.stalkMap_germ_assoc _ V ⟨_, hxV⟩]
    rw [TopCat.Presheaf.germ_stalk_specializes'_assoc]
    -- Porting note : explicit variables and proofs were not necessary
    erw [PresheafedSpace.stalkMap_germ _ (U.openEmbedding.isOpenMap.functor.obj V)
      ⟨x.1, ⟨⟨f.1.base x.1, x.2⟩, _, rfl⟩⟩]
    swap
    · rw [morphismRestrict_val_base] at hxV
      exact hxV
    erw [PresheafedSpace.restrictStalkIso_hom_eq_germ]
    rw [morphismRestrict_c_app, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
#align algebraic_geometry.morphism_restrict_stalk_map AlgebraicGeometry.morphismRestrictStalkMap

instance {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
      delta morphismRestrict
      refine PresheafedSpace.IsOpenImmersion.comp _ _

end MorphismRestrict

end AlgebraicGeometry
