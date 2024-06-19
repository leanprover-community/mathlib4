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

/-- The image of an open immersion as an open set. -/
@[simps]
def Scheme.Hom.opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y :=
  ⟨_, H.base_open.isOpen_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.Scheme.Hom.opensRange

namespace Scheme

instance basic_open_isOpenImmersion {R : CommRingCat.{u}} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_openEmbedding (Localization.Away f) f : _)
  · intro x
    exact Spec_map_localization_isIso R (Submonoid.powers f) x
#align algebraic_geometry.Scheme.basic_open_IsOpenImmersion AlgebraicGeometry.Scheme.basic_open_isOpenImmersion

theorem exists_affine_mem_range_and_range_subset
    {X : Scheme.{u}} {x : X} {U : Opens X} (hxU : x ∈ U) :
    ∃ (R : CommRingCat) (f : Scheme.Spec.obj (op R) ⟶ X),
      IsOpenImmersion f ∧ x ∈ Set.range f.1.base ∧ Set.range f.1.base ⊆ U := by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.1.base ⟨x, hxV⟩ ∈ (Opens.map (e.inv.1.base ≫ V.inclusion)).obj U :=
    show ((e.hom ≫ e.inv).1.base ⟨x, hxV⟩).1 ∈ U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open this (Opens.is_open' _)
  let f : Scheme.Spec.obj (op (.of (Localization.Away r))) ⟶ X :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))).op ≫
      (e.inv ≫ X.ofRestrict _ : _)
  refine ⟨.of (Localization.Away r), f, inferInstance, ?_⟩
  rw [Scheme.comp_val_base, LocallyRingedSpace.comp_val, SheafedSpace.comp_base, TopCat.coe_comp,
    Set.range_comp]
  erw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact ⟨⟨_, hr, congr(($(e.hom_inv_id).1.base ⟨x, hxV⟩).1)⟩, Set.image_subset_iff.mpr hr'⟩

end Scheme

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace CommRingCat.{u}} (Y : Scheme.{u})
variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨R, i, _, h₁, h₂⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨_, H.base_open.isOpen_range⟩) ⟨x, rfl⟩
  refine ⟨R, LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f) _ h₂, ?_, ?_⟩
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]; exact h₁
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

end Scheme

end AlgebraicGeometry
