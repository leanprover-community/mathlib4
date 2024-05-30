/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

#align_import algebraic_geometry.open_immersion.Scheme from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Open immersions of schemes

-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

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
abbrev IsOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsOpenImmersion f
#align algebraic_geometry.IsOpenImmersion AlgebraicGeometry.IsOpenImmersion

instance IsOpenImmersion.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
LocallyRingedSpace.IsOpenImmersion.comp f g

namespace LocallyRingedSpace.IsOpenImmersion

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpace.{u})
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.1.base : _) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    · exact Subtype.range_coe_subtype
    · exact Opens.openEmbedding _ -- Porting note (#11187): was `infer_instance`
#align algebraic_geometry.LocallyRingedSpace.IsOpenImmersion.Scheme AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.isOpen_range {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f.1.base) :=
  H.base_open.isOpen_range
#align algebraic_geometry.IsOpenImmersion.open_range AlgebraicGeometry.IsOpenImmersion.isOpen_range

@[deprecated (since := "2024-03-17")]
alias IsOpenImmersion.open_range := IsOpenImmersion.isOpen_range

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
  obj : J → Scheme
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
def affineCover (X : Scheme.{u}) : OpenCover X where
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
    erw [TopCat.coe_comp] -- now `erw` after #13170
    rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
    · erw [Subtype.range_coe_subtype]
      exact (X.local_affine x).choose.2
    erw [← TopCat.epi_iff_surjective] -- now `erw` after #13170
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
    rcases (f (𝒰.f x)).Covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    erw [hz, hy] -- now `erw` after #13170
  -- Porting note: weirdly, even though no input is needed, `inferInstance` does not work
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
def OpenCover.copy {X : Scheme.{u}} (𝒰 : OpenCover X) (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J, obj, map
    f := fun x => e₁.symm (𝒰.f x)
    Covers := fun x => by
      rw [e₂, Scheme.comp_val_base, TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr,
        Set.image_univ, e₁.rightInverse_symm]
      · exact 𝒰.Covers x
      · erw [← TopCat.epi_iff_surjective]; infer_instance -- now `erw` after #13170
    -- Porting note: weirdly, even though no input is needed, `inferInstance` does not work
    -- `PresheafedSpace.IsOpenImmersion.comp` is marked as `instance`
    IsOpen := fun i => by rw [e₂]; exact PresheafedSpace.IsOpenImmersion.comp _ _ }
#align algebraic_geometry.Scheme.open_cover.copy AlgebraicGeometry.Scheme.OpenCover.copy

-- Porting note: need more hint on universe level
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
def OpenCover.add {X Y : Scheme.{u}} (𝒰 : X.OpenCover) (f : Y ⟶ X) [IsOpenImmersion f] :
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

instance val_base_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_isIso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.Scheme.val_base_isIso

instance basic_open_isOpenImmersion {R : CommRingCat.{u}} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_openEmbedding (Localization.Away f) f : _)
  · intro x
    exact Spec_map_localization_isIso R (Submonoid.powers f) x
#align algebraic_geometry.Scheme.basic_open_IsOpenImmersion AlgebraicGeometry.Scheme.basic_open_isOpenImmersion

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec.obj (Opposite.op R)) where
  J := R
  obj r := Spec.obj (Opposite.op <| CommRingCat.of <| Localization.Away r)
  map r := Spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f _ := 1
  Covers r := by
    rw [Set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · -- Porting note: need more hand holding here because Lean knows that
      -- `CommRing.ofHom ...` is iso, but without `ofHom` Lean does not know what to do
      change Epi (Spec.map (CommRingCat.ofHom (algebraMap _ _)).op).1.base
      infer_instance
  IsOpen x := AlgebraicGeometry.Scheme.basic_open_isOpenImmersion x
#align algebraic_geometry.Scheme.affine_basis_cover_of_affine AlgebraicGeometry.Scheme.affineBasisCoverOfAffine

/-- We may bind the basic open sets of an open affine cover to form an affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme.{u}) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _
#align algebraic_geometry.Scheme.affine_basis_cover AlgebraicGeometry.Scheme.affineBasisCover

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2
#align algebraic_geometry.Scheme.affine_basis_cover_ring AlgebraicGeometry.Scheme.affineBasisCoverRing

theorem affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = Spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl
#align algebraic_geometry.Scheme.affine_basis_cover_obj AlgebraicGeometry.Scheme.affineBasisCover_obj

theorem affineBasisCover_map_range (X : Scheme.{u}) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 := by
  erw [coe_comp, Set.range_comp]
  -- Porting note: `congr` fails to see the goal is comparing image of the same function
  refine congr_arg (_ '' ·) ?_
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)
#align algebraic_geometry.Scheme.affine_basis_cover_map_range AlgebraicGeometry.Scheme.affineBasisCover_map_range

theorem affineBasisCover_is_basis (X : Scheme.{u}) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.map a)
  · rintro a U haU hU
    rcases X.affineCover.Covers a with ⟨x, e⟩
    let U' := (X.affineCover.map (X.affineCover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by rw [← e] at haU; exact haU
    rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affineCover.map (X.affineCover.f a)).1.base.continuous_toFun.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine ⟨_, ⟨⟨_, s⟩, rfl⟩, ?_, ?_⟩ <;> erw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU
#align algebraic_geometry.Scheme.affine_basis_cover_is_basis AlgebraicGeometry.Scheme.affineBasisCover_is_basis

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! obj map]
def OpenCover.finiteSubcover {X : Scheme.{u}} (𝒰 : OpenCover X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (IsOpenImmersion.isOpen_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.Covers x)
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
      H.base_open.isOpen_range
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

theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by
  cases X; cases Y; congr
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.Scheme_eq_of_LocallyRingedSpace_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_eq_of_locallyRingedSpace_eq

theorem scheme_toScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    toScheme Y f.1 = X := by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f
#align algebraic_geometry.PresheafedSpace.IsOpenImmersion.Scheme_to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersionₓ.scheme_toScheme

end ToScheme

end PresheafedSpace.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps! (config := .lemmasOnly) carrier, simps! presheaf_map presheaf_obj]
def Scheme.restrict {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X} (h : OpenEmbedding f) :
    Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
#align algebraic_geometry.Scheme.restrict AlgebraicGeometry.Scheme.restrict

lemma Scheme.restrict_toPresheafedSpace
    {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X} (h : OpenEmbedding f) :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := rfl

/-- The canonical map from the restriction to the subspace. -/
@[simps!]
def Scheme.ofRestrict {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X}
    (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.ofRestrict h
#align algebraic_geometry.Scheme.ofRestrict AlgebraicGeometry.Scheme.ofRestrict

instance IsOpenImmersion.ofRestrict {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X}
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

theorem to_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [h : IsOpenImmersion f] [Epi f.1.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.1 h _) _
#align algebraic_geometry.IsOpenImmersion.to_iso AlgebraicGeometry.IsOpenImmersion.to_iso

theorem of_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : OpenEmbedding f.1.base)
    [∀ x, IsIso (PresheafedSpace.stalkMap f.1 x)] : IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.1 hf
#align algebraic_geometry.IsOpenImmersion.of_stalk_iso AlgebraicGeometry.IsOpenImmersion.of_stalk_iso

theorem iff_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  ⟨fun H => ⟨H.1, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.of_stalk_iso _ _ f h₁ h₂⟩
#align algebraic_geometry.IsOpenImmersion.iff_stalk_iso AlgebraicGeometry.IsOpenImmersion.iff_stalk_iso

theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.1.base :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.to_iso _ _ f h₁ h₂⟩
#align algebraic_geometry.is_iso_iff_IsOpenImmersion AlgebraicGeometry.isIso_iff_isOpenImmersion

theorem _root_.AlgebraicGeometry.isIso_iff_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) := by
  rw [isIso_iff_isOpenImmersion, IsOpenImmersion.iff_stalk_iso, and_comm, ← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
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
  -- Porting note: was just `infer_instance`, it is a bit weird that no explicit class instance is
  -- provided but still class inference fail to find this
  exact LocallyRingedSpace.IsOpenImmersion.comp (H := inferInstance) _
#align algebraic_geometry.IsOpenImmersion.pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  -- Porting note: was just `infer_instance`, it is a bit weird that no explicit class instance is
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
      ((Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.isOpen_range⟩).1 := by
  rw [← show _ = (pullback.snd : pullback f g ⟶ _).1.base from
      PreservesPullback.iso_hom_snd Scheme.forgetToTop f g]
  -- Porting note (#10691): was `rw`
  erw [coe_comp]
  rw [Set.range_comp, Set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _)]
  -- Porting note (#10691): was `rw`
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  erw [← TopCat.epi_iff_surjective] -- now `erw` after #13170
  infer_instance
#align algebraic_geometry.IsOpenImmersion.range_pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_snd_of_left

theorem range_pullback_fst_of_right :
    Set.range (pullback.fst : pullback g f ⟶ Y).1.base =
      ((Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.isOpen_range⟩).1 := by
  rw [← show _ = (pullback.fst : pullback g f ⟶ _).1.base from
      PreservesPullback.iso_hom_fst Scheme.forgetToTop g f]
  -- Porting note (#10691): was `rw`
  erw [coe_comp]
  rw [Set.range_comp, Set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _)]
  -- Porting note (#10691): was `rw`
  · erw [TopCat.pullback_fst_image_snd_preimage]
    rw [Set.image_univ]
    rfl
  erw [← TopCat.epi_iff_surjective] -- now `erw` after #13170
  infer_instance
#align algebraic_geometry.IsOpenImmersion.range_pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_fst_of_right

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      Set.range f.1.base ∩ Set.range g.1.base := by
  rw [pullback.condition, Scheme.comp_val_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_snd_of_left, Opens.carrier_eq_coe,
    Opens.map_obj, Opens.coe_mk, Set.image_preimage_eq_inter_range]
#align algebraic_geometry.IsOpenImmersion.range_pullback_to_base_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base =
      Set.range g.1.base ∩ Set.range f.1.base := by
  rw [Scheme.comp_val_base, TopCat.coe_comp, Set.range_comp, range_pullback_fst_of_right,
    Opens.map_obj, Opens.carrier_eq_coe, Opens.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm]
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
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp
#align algebraic_geometry.IsOpenImmersion.iso_of_range_eq AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq

@[simp, reassoc]
lemma isoOfRangeEq_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac _ _ (le_of_eq e)

@[simp, reassoc]
lemma isoOfRangeEq_inv_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac _ _ (le_of_eq e.symm)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev _root_.AlgebraicGeometry.Scheme.Hom.opensFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : Opens X ⥤ Opens Y :=
  H.openFunctor
#align algebraic_geometry.Scheme.hom.opens_functor AlgebraicGeometry.Scheme.Hom.opensFunctor

/-- The isomorphism `Γ(X, U) ⟶ Γ(Y, f(U))` induced by an open immersion `f : X ⟶ Y`. -/
def _root_.AlgebraicGeometry.Scheme.Hom.invApp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] (U) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (f.opensFunctor.obj U)) :=
  H.invApp U
#align algebraic_geometry.Scheme.hom.inv_app AlgebraicGeometry.Scheme.Hom.invApp

theorem app_eq_inv_app_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U) :
    (Opens.map f.1.base).obj V = (Opens.map fg.1.base).obj (g.opensFunctor.obj V) := by
  subst H
  rw [Scheme.comp_val_base, Opens.map_comp_obj]
  congr 1
  ext1
  exact (Set.preimage_image_eq _ h.base_open.inj).symm
#align algebraic_geometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_invApp_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
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

theorem lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
    (V : Opens U) :
    (IsOpenImmersion.lift f g H).1.c.app (op V) =
      Scheme.Hom.invApp f _ ≫
        g.1.c.app _ ≫
          X.presheaf.map
            (eqToHom <|
                IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux _ _ _
                  (IsOpenImmersion.lift_fac f g H).symm V).op :=
  -- Porting note: `(lift_fac ...).symm` was done by unification magic in Lean3.
  IsOpenImmersion.app_eq_invApp_app_of_comp_eq _ _ _ (lift_fac _ _ H).symm _
#align algebraic_geometry.IsOpenImmersion.lift_app AlgebraicGeometry.IsOpenImmersion.lift_app

end IsOpenImmersion

namespace Scheme

theorem image_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X}
    (r : X.presheaf.obj (op U)) :
    f.opensFunctor.obj (X.basicOpen r) = Y.basicOpen (Scheme.Hom.invApp f U r) := by
  have e := Scheme.preimage_basicOpen f (Scheme.Hom.invApp f U r)
  rw [Scheme.Hom.invApp] at e
  -- Porting note (#10691): was `rw`
  erw [PresheafedSpace.IsOpenImmersion.invApp_app_apply] at e
  rw [Scheme.basicOpen_res, inf_eq_right.mpr _] at e
  · rw [← e]
    ext1
    -- Porting note: this `dsimp` was not necessary
    dsimp [Opens.map]
    refine Set.image_preimage_eq_inter_range.trans ?_
    erw [Set.inter_eq_left]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  refine le_trans (Scheme.basicOpen_le _ _) (le_of_eq ?_)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm
#align algebraic_geometry.Scheme.image_basic_open AlgebraicGeometry.Scheme.image_basicOpen

/-- The image of an open immersion as an open set. -/
@[simps]
def Hom.opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y :=
  ⟨_, H.base_open.isOpen_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.Scheme.Hom.opensRange

end Scheme

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def Scheme.OpenCover.pullbackCover {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback f (𝒰.map x)
  map x := pullback.fst
  f x := 𝒰.f (f.1.base x)
  Covers x := by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f (𝒰.map (𝒰.f (f.1.base x)))]
    -- Porting note: `rw` to `erw` on this single lemma
    rw [TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    · obtain ⟨y, h⟩ := 𝒰.Covers (f.1.base x)
      exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance
#align algebraic_geometry.Scheme.open_cover.pullback_cover AlgebraicGeometry.Scheme.OpenCover.pullbackCover

/-- Given an open cover on `X`, we may pull them back along a morphism `f : W ⟶ X` to obtain
an open cover of `W`. This is similar to `Scheme.OpenCover.pullbackCover`, but here we
take `pullback (𝒰.map x) f` instead of `pullback f (𝒰.map x)`. -/
@[simps]
def Scheme.OpenCover.pullbackCover' {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback (𝒰.map x) f
  map x := pullback.snd
  f x := 𝒰.f (f.1.base x)
  Covers x := by
    rw [←
      show _ = (pullback.snd : pullback (𝒰.map (𝒰.f (f.1.base x))) f ⟶ _).1.base from
        PreservesPullback.iso_hom_snd Scheme.forgetToTop (𝒰.map (𝒰.f (f.1.base x))) f]
    -- Porting note: `rw` to `erw` on this single lemma
    rw [TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_snd_range]
    · obtain ⟨y, h⟩ := 𝒰.Covers (f.1.base x)
      exact ⟨y, h⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance

theorem Scheme.OpenCover.iUnion_range {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⋃ i, Set.range (𝒰.map i).1.base = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact ⟨𝒰.f x, 𝒰.Covers x⟩
#align algebraic_geometry.Scheme.open_cover.Union_range AlgebraicGeometry.Scheme.OpenCover.iUnion_range

theorem Scheme.OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⨆ i, Scheme.Hom.opensRange (𝒰.map i) = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range
#align algebraic_geometry.Scheme.open_cover.supr_opens_range AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange

theorem Scheme.OpenCover.compactSpace {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.J]
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
                  (X.ofRestrict (Opens.openEmbedding ⟨_, (𝒰.IsOpen i).base_open.isOpen_range⟩))
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
  -- Porting note: was automatic
  IsOpen x := PresheafedSpace.IsOpenImmersion.comp (hf := inferInstance) (hg := (𝒰₁.IsOpen _))
#align algebraic_geometry.Scheme.open_cover.inter AlgebraicGeometry.Scheme.OpenCover.inter

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! J obj map]
def Scheme.openCoverOfSuprEqTop {s : Type*} (X : Scheme.{u}) (U : s → Opens X)
    (hU : ⨆ i, U i = ⊤) : X.OpenCover where
  J := s
  obj i := X.restrict (U i).openEmbedding
  map i := X.ofRestrict (U i).openEmbedding
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X) by trivial
    (Opens.mem_iSup.mp this).choose
  Covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X) by trivial
    exact (Opens.mem_iSup.mp this).choose_spec
#align algebraic_geometry.Scheme.open_cover_of_supr_eq_top AlgebraicGeometry.Scheme.openCoverOfSuprEqTop

namespace Scheme

/--
An affine open cover of `X` consists of a family of open immersions into `X` from
spectra of rings.
-/
structure AffineOpenCover (X : Scheme.{u}) where
  /-- index set of an affine open cover of a scheme `X` -/
  J : Type v
  /-- the ring associated to a component of an affine open cover -/
  obj : J → CommRingCat.{u}
  /-- the embedding of subschemes to `X` -/
  map : ∀ j : J, Spec.obj (.op <| obj j) ⟶ X
  /-- given a point of `x : X`, `f x` is the index of the subscheme which contains `x`  -/
  f : X.carrier → J
  /-- the subschemes covers `X` -/
  Covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  /-- the embedding of subschemes are open immersions -/
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance

namespace AffineOpenCover

attribute [instance] AffineOpenCover.IsOpen

/-- The open cover associated to an affine open cover. -/
@[simps]
def openCover {X : Scheme.{u}} (𝓤 : X.AffineOpenCover) : X.OpenCover where
  J := 𝓤.J
  map := 𝓤.map
  f := 𝓤.f
  Covers := 𝓤.Covers

end AffineOpenCover

/-- A choice of an affine open cover of a scheme. -/
def affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where
  J := X.affineCover.J
  map := X.affineCover.map
  f := X.affineCover.f
  Covers := X.affineCover.Covers

@[simp]
lemma openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover = X.affineCover :=
  rfl

/-- Given any open cover `𝓤`, this is an affine open cover which refines it.
The morphism in the category of open covers which proves that this is indeed a refinement, see
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement`.
-/
def OpenCover.affineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) : X.AffineOpenCover where
  J := (𝓤.bind fun j => (𝓤.obj j).affineCover).J
  map := (𝓤.bind fun j => (𝓤.obj j).affineCover).map
  f := (𝓤.bind fun j => (𝓤.obj j).affineCover).f
  Covers := (𝓤.bind fun j => (𝓤.obj j).affineCover).Covers

end Scheme

section category

/--
A morphism between open covers `𝓤 ⟶ 𝓥` indicates that `𝓤` is a refinement of `𝓥`.
Since open covers of schemes are indexed, the definition also involves a map on the
indexing types.
-/
structure Scheme.OpenCover.Hom {X : Scheme.{u}} (𝓤 𝓥 : Scheme.OpenCover.{v} X) where
  /-- The map on indexing types associated to a morphism of open covers. -/
  idx : 𝓤.J → 𝓥.J
  /-- The morphism between open subsets associated to a morphism of open covers. -/
  app (j : 𝓤.J) : 𝓤.obj j ⟶ 𝓥.obj (idx j)
  isOpen (j : 𝓤.J) : IsOpenImmersion (app j) := by infer_instance
  w (j : 𝓤.J) : app j ≫ 𝓥.map _ = 𝓤.map _ := by aesop_cat

attribute [reassoc (attr := simp)] Scheme.OpenCover.Hom.w
attribute [instance] Scheme.OpenCover.Hom.isOpen

/-- The identity morphism in the category of open covers of a scheme. -/
def Scheme.OpenCover.Hom.id {X : Scheme.{u}} (𝓤 : Scheme.OpenCover.{v} X) : 𝓤.Hom 𝓤 where
  idx j := j
  app j := 𝟙 _

/-- The composition of two morphisms in the category of open covers of a scheme. -/
def Scheme.OpenCover.Hom.comp {X : Scheme.{u}} {𝓤 𝓥 𝓦 : Scheme.OpenCover.{v} X}
    (f : 𝓤.Hom 𝓥) (g : 𝓥.Hom 𝓦) : 𝓤.Hom 𝓦 where
  idx j := g.idx <| f.idx j
  app j := f.app _ ≫ g.app _

instance Scheme.OpenCover.category {X : Scheme.{u}} : Category (Scheme.OpenCover.{v} X) where
  Hom 𝓤 𝓥 := 𝓤.Hom 𝓥
  id := Scheme.OpenCover.Hom.id
  comp f g := f.comp g

@[simp]
lemma Scheme.OpenCover.id_idx_apply {X : Scheme.{u}} (𝓤 : X.OpenCover) (j : 𝓤.J) :
    (𝟙 𝓤 : 𝓤 ⟶ 𝓤).idx j = j := rfl

@[simp]
lemma Scheme.OpenCover.id_app {X : Scheme.{u}} (𝓤 : X.OpenCover) (j : 𝓤.J) :
    (𝟙 𝓤 : 𝓤 ⟶ 𝓤).app j = 𝟙 _ := rfl

@[simp]
lemma Scheme.OpenCover.comp_idx_apply {X : Scheme.{u}} {𝓤 𝓥 𝓦 : X.OpenCover}
    (f : 𝓤 ⟶ 𝓥) (g : 𝓥 ⟶ 𝓦) (j : 𝓤.J) :
    (f ≫ g).idx j = g.idx (f.idx j) := rfl

@[simp]
lemma Scheme.OpenCover.comp_app {X : Scheme.{u}} {𝓤 𝓥 𝓦 : X.OpenCover}
    (f : 𝓤 ⟶ 𝓥) (g : 𝓥 ⟶ 𝓦) (j : 𝓤.J) :
    (f ≫ g).app j = f.app j ≫ g.app _ := rfl

end category

/-- Given any open cover `𝓤`, this is an affine open cover which refines it. -/
def Scheme.OpenCover.fromAffineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) :
    𝓤.affineRefinement.openCover ⟶ 𝓤 where
  idx j := j.fst
  app j := (𝓤.obj j.fst).affineCover.map _

end AlgebraicGeometry
