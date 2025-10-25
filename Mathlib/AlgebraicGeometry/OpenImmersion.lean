/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Open immersions of schemes

-/

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion : MorphismProperty (Scheme.{u}) :=
  fun _ _ f ↦ LocallyRingedSpace.IsOpenImmersion f.toLRSHom

instance IsOpenImmersion.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
  LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

namespace LocallyRingedSpace.IsOpenImmersion

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpace.{u})
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
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
    · exact Opens.isOpenEmbedding _

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.isOpen_range {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f) :=
  H.base_open.isOpen_range

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

theorem isOpenEmbedding : IsOpenEmbedding f :=
  H.base_open

/-- The image of an open immersion as an open set. -/
@[simps]
def opensRange : Y.Opens :=
  ⟨_, f.isOpenEmbedding.isOpen_range⟩

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
def opensFunctor : X.Opens ⥤ Y.Opens :=
  LocallyRingedSpace.IsOpenImmersion.opensFunctor f.toLRSHom

/-- `f ''ᵁ U` is notation for the image (as an open set) of `U` under an open immersion `f`.
The preferred name in lemmas is `image` and it should be treated as an infix. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ''ᵁ " U:90 => (Scheme.Hom.opensFunctor f).obj U

@[simp] lemma coe_image {U : X.Opens} : f ''ᵁ U = f '' U := rfl

lemma image_mono {U V : X.Opens} (e : U ≤ V) : f ''ᵁ U ≤ f ''ᵁ V := Set.image_mono e

@[deprecated (since := "2025-10-07")] alias image_le_image_of_le := image_mono

@[simp]
lemma opensFunctor_map_homOfLE {U V : X.Opens} (e : U ≤ V) :
    (Scheme.Hom.opensFunctor f).map (homOfLE e) = homOfLE (f.image_mono e) :=
  rfl

@[simp]
lemma image_top_eq_opensRange : f ''ᵁ ⊤ = f.opensRange := by
  apply Opens.ext
  simp

lemma opensRange_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g).opensRange = g ''ᵁ f.opensRange :=
  TopologicalSpace.Opens.ext (Set.range_comp g f)

lemma opensRange_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    f.opensRange = ⊤ :=
  TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr f.homeomorph.surjective)

lemma opensRange_comp_of_isIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] [IsOpenImmersion g] : (f ≫ g).opensRange = g.opensRange := by
  rw [opensRange_comp, opensRange_of_isIso, image_top_eq_opensRange]

lemma image_le_opensRange (U : X.Opens) : f ''ᵁ U ≤ f.opensRange := by
  simpa using f.image_mono le_top

@[simp]
lemma preimage_image_eq (U : X.Opens) : f ⁻¹ᵁ f ''ᵁ U = U := by
  apply Opens.ext
  simp [Set.preimage_image_eq _ f.isOpenEmbedding.injective]

lemma image_le_image_iff (f : X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens) :
    f ''ᵁ U ≤ f ''ᵁ U' ↔ U ≤ U' := by
  refine ⟨fun h ↦ ?_, f.image_mono⟩
  rw [← preimage_image_eq f U, ← preimage_image_eq f U']
  apply f.preimage_mono h

lemma image_preimage_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U := by
  apply Opens.ext
  simp [Set.image_preimage_eq_range_inter]

@[deprecated (since := "2025-10-07")]
alias image_preimage_eq_opensRange_inter := image_preimage_eq_opensRange_inf

lemma image_preimage_le (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U ≤ U :=
  (f.image_preimage_eq_opensRange_inf U).trans_le inf_le_right

lemma image_injective : Function.Injective (f ''ᵁ ·) := by
  intro U V hUV
  simpa using congrArg (f ⁻¹ᵁ ·) hUV

lemma image_iSup {ι : Sort*} (s : ι → X.Opens) :
    (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i : ι), f ''ᵁ s i := by
  ext : 1
  simp [Set.image_iUnion]

lemma image_iSup₂ {ι : Sort*} {κ : ι → Sort*} (s : (i : ι) → κ i → X.Opens) :
    (f ''ᵁ ⨆ (i : ι), ⨆ (j : κ i), s i j) = ⨆ (i : ι), ⨆ (j : κ i), f ''ᵁ s i j := by
  ext : 1
  simp [Set.image_iUnion₂]

@[simp]
lemma comp_image {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U :=
  TopologicalSpace.Opens.ext (Set.image_comp g f U)

@[simp]
lemma id_image {X : Scheme} (U : X.Opens) : 𝟙 X ''ᵁ U = U :=
  TopologicalSpace.Opens.ext (Set.image_id _)

@[simp]
lemma inv_image {X Y : Scheme} (e : X ≅ Y) (U : Y.Opens) : e.inv ''ᵁ U = e.hom ⁻¹ᵁ U :=
  TopologicalSpace.Opens.ext (Set.image_equiv_eq_preimage_symm _ (Scheme.homeoOfIso e.symm).toEquiv)

@[simp]
lemma apply_mem_image_iff {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {U : X.Opens} {x : X} : f x ∈ f ''ᵁ U ↔ x ∈ U :=
  f.isOpenEmbedding.injective.mem_set_image

@[deprecated (since := "2025-10-07")] alias map_mem_image_iff := apply_mem_image_iff

@[simp]
lemma preimage_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹ᵁ f.opensRange = ⊤ := by
  simp [Scheme.Hom.opensRange]

instance (U : X.Opens) : IsIso (f.app (f ''ᵁ U)) := by delta opensFunctor; infer_instance

lemma isIso_app (V : Y.Opens) (hV : V ≤ f.opensRange) : IsIso (f.app V) := by
  rw [show V = f ''ᵁ f ⁻¹ᵁ V from Opens.ext (Set.image_preimage_eq_of_subset hV).symm]
  infer_instance

/-- The isomorphism `Γ(Y, f(U)) ≅ Γ(X, U)` induced by an open immersion `f : X ⟶ Y`. -/
def appIso (U) : Γ(Y, f ''ᵁ U) ≅ Γ(X, U) :=
  (asIso <| LocallyRingedSpace.IsOpenImmersion.invApp f.toLRSHom U).symm

@[reassoc (attr := simp)]
theorem appIso_inv_naturality {U V : X.Opens} (i : op U ⟶ op V) :
    X.presheaf.map i ≫ (f.appIso V).inv =
      (f.appIso U).inv ≫ Y.presheaf.map (f.opensFunctor.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality _ _

theorem appIso_hom (U) :
    (f.appIso U).hom = f.app (f ''ᵁ U) ≫ X.presheaf.map
      (eqToHom (preimage_image_eq f U).symm).op :=
  (PresheafedSpace.IsOpenImmersion.inv_invApp f.toPshHom U).trans (by rw [eqToHom_op]; rfl)

/-- A variant of `appIso_hom` that uses `Hom.appLE`. -/
theorem appIso_hom' (U) :
    (f.appIso U).hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge :=
  f.appIso_hom U

@[reassoc (attr := simp)]
theorem app_appIso_inv (U) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

/-- A variant of `app_invApp` that gives an `eqToHom` instead of `homOfLE`. -/
@[reassoc]
theorem app_invApp' (U) (hU : U ≤ f.opensRange) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (eqToHom (Opens.ext <| by simpa [Set.image_preimage_eq_inter_range])).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

@[reassoc (attr := simp), elementwise nosimp]
theorem appIso_inv_app (U) :
    (f.appIso U).inv ≫ f.app (f ''ᵁ U) = X.presheaf.map (eqToHom (preimage_image_eq f U)).op :=
  (PresheafedSpace.IsOpenImmersion.invApp_app _ _).trans (by rw [eqToHom_op])

@[reassoc (attr := simp), elementwise nosimp]
lemma appLE_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e ≫ (f.appIso V).inv =
        Y.presheaf.map (homOfLE <| (f.image_mono e).trans
          (f.image_preimage_eq_opensRange_inf U ▸ inf_le_right)).op := by
  simp only [appLE, Category.assoc, appIso_inv_naturality, Functor.op_obj, Functor.op_map,
    Quiver.Hom.unop_op, opensFunctor_map_homOfLE, app_appIso_inv_assoc, Opens.carrier_eq_coe]
  rw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
lemma appIso_inv_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ f ''ᵁ U) :
    (f.appIso U).inv ≫ f.appLE (f ''ᵁ U) V e =
        X.presheaf.map (homOfLE (by rwa [preimage_image_eq] at e)).op := by
  simp only [appLE, appIso_inv_app_assoc, eqToHom_op]
  rw [← Functor.map_comp]
  rfl

end Scheme.Hom

/-- The open sets of an open subscheme corresponds to the open sets containing in the image. -/
@[simps]
def IsOpenImmersion.opensEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.Opens ≃ { U : Y.Opens // U ≤ f.opensRange } where
  toFun U := ⟨f ''ᵁ U, Set.image_subset_range _ _⟩
  invFun U := f ⁻¹ᵁ U
  left_inv _ := Opens.ext (Set.preimage_image_eq _ f.isOpenEmbedding.injective)
  right_inv U := Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2))

namespace Scheme

instance isOpenImmersion_SpecMap_localizationAway {R : CommRingCat.{u}} (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f :)
  · intro x
    exact isIso_SpecMap_stakMap_localization R (Submonoid.powers f) x

@[deprecated (since := "2025-10-07")]
  alias basic_open_isOpenImmersion := isOpenImmersion_SpecMap_localizationAway

instance {R} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  isOpenImmersion_SpecMap_localizationAway (R := .of R) f

lemma _root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization {R S} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have e := (IsLocalization.algEquiv (.powers f) S
    (Localization.Away f)).symm.toAlgHom.comp_algebraMap
  rw [← e, CommRingCat.ofHom_comp, Spec.map_comp]
  have H : IsIso (CommRingCat.ofHom (IsLocalization.algEquiv
    (Submonoid.powers f) S (Localization.Away f)).symm.toAlgHom.toRingHom) := by
    exact inferInstanceAs (IsIso <| (IsLocalization.algEquiv
      (Submonoid.powers f) S (Localization.Away f)).toRingEquiv.toCommRingCatIso.inv)
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom] at H ⊢
  infer_instance

theorem exists_affine_mem_range_and_range_subset
    {X : Scheme.{u}} {x : X} {U : X.Opens} (hxU : x ∈ U) :
    ∃ R, ∃ (f : Spec R ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f ∧ Set.range f ⊆ U := by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.base ⟨x, hxV⟩ ∈ (Opens.map (e.inv.base ≫ V.inclusion')).obj U :=
    show ((e.hom ≫ e.inv).base ⟨x, hxV⟩).1 ∈ U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open this (Opens.is_open' _)
  let f : Spec (.of <| Localization.Away r) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ ⟨e.inv ≫ X.ofRestrict _⟩
  refine ⟨.of (Localization.Away r), f, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact ⟨⟨_, hr, congr(($(e.hom_inv_id).base ⟨x, hxV⟩).1)⟩, Set.image_subset_iff.mpr hr'⟩

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

@[simp]
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  ⟨toLocallyRingedSpaceHom _ f⟩

@[simp]
theorem toSchemeHom_toPshHom : (toSchemeHom Y f).toPshHom = f :=
  rfl

instance toSchemeHom_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (toSchemeHom Y f) :=
  H

theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by
  cases X; cases Y; congr

theorem scheme_toScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    toScheme Y f.toPshHom = X := by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f.toLRSHom

end ToScheme

end PresheafedSpace.IsOpenImmersion

section Restrict

variable {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X} (h : IsOpenEmbedding f)

/-- The restriction of a Scheme along an open embedding. -/
@[simps! -isSimp carrier, simps! presheaf_obj]
def Scheme.restrict : Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }

lemma Scheme.restrict_toPresheafedSpace :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := rfl

/-- The canonical map from the restriction to the subspace. -/
@[simps! toLRSHom_base, simps! -isSimp toLRSHom_c_app]
def Scheme.ofRestrict : X.restrict h ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict h⟩

@[simp]
lemma Scheme.ofRestrict_app (V) :
    (X.ofRestrict h).app V = X.presheaf.map (h.isOpenMap.adjunction.counit.app V).op  :=
  rfl

instance IsOpenImmersion.ofRestrict : IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance

@[simp]
lemma Scheme.ofRestrict_appLE (V W e) :
    (X.ofRestrict h).appLE V W e = X.presheaf.map
      (homOfLE (show X.ofRestrict h ''ᵁ _ ≤ _ by exact Set.image_subset_iff.mpr e)).op := by
  dsimp [Hom.appLE]
  exact (X.presheaf.map_comp _ _).symm

@[simp]
lemma Scheme.ofRestrict_appIso (U) :
    (X.ofRestrict h).appIso U = Iso.refl _ := by
  ext1
  simp only [restrict_presheaf_obj, Hom.appIso_hom', ofRestrict_appLE, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Iso.refl_hom]

@[simp]
lemma Scheme.restrict_presheaf_map (V W) (i : V ⟶ W) :
    (X.restrict h).presheaf.map i = X.presheaf.map (homOfLE (show X.ofRestrict h ''ᵁ W.unop ≤
      X.ofRestrict h ''ᵁ V.unop from Set.image_mono i.unop.le)).op := rfl

end Restrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  LocallyRingedSpace.IsOpenImmersion.of_isIso _

theorem isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [Epi f.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.toPshHom ‹_› _) _

@[deprecated (since := "2025-10-07")] alias to_iso := isIso

theorem of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f)
    [∀ x, IsIso (f.stalkMap x)] : IsOpenImmersion f :=
  haveI (x : X) : IsIso (f.toShHom.stalkMap x) := inferInstanceAs <| IsIso (f.stalkMap x)
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.toShHom hf

@[deprecated (since := "2025-10-07")] alias of_stalk_iso := of_isIso_stalkMap

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.stalkMap x) :=
  inferInstanceAs <| IsIso (f.toLRSHom.stalkMap x)

lemma of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    [IsOpenImmersion (f ≫ g)] : IsOpenImmersion f :=
  haveI (x : X) : IsIso (f.stalkMap x) :=
    haveI : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    IsIso.of_isIso_comp_left (f := g.stalkMap (f x)) _
  IsOpenImmersion.of_isIso_stalkMap _ <|
    IsOpenEmbedding.of_comp _ (Scheme.Hom.isOpenEmbedding g) (Scheme.Hom.isOpenEmbedding (f ≫ g))

instance : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @IsOpenImmersion where
  of_postcomp f g _ _ := .of_comp f g

theorem iff_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ IsOpenEmbedding f ∧ ∀ x, IsIso (f.stalkMap x) :=
  ⟨fun H ↦ ⟨H.1, fun x ↦ inferInstanceAs <| IsIso (f.toPshHom.stalkMap x)⟩,
    fun ⟨h, _⟩ ↦ .of_isIso_stalkMap f h⟩

@[deprecated (since := "2025-10-07")] alias iff_stalk_iso := iff_isIso_stalkMap

theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.base :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => IsOpenImmersion.isIso f⟩

@[deprecated (since := "2025-10-07")]
alias _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion := isIso_iff_isOpenImmersion_and_epi_base

theorem _root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.base ∧ ∀ x, IsIso (f.stalkMap x) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base,
    IsOpenImmersion.iff_isIso_stalkMap, and_comm, ← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to
      IsIso
        (TopCat.isoOfHomeo
          (Equiv.toHomeomorphOfContinuousOpen
            (.ofBijective _ ⟨h₂.injective, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
            h₂.isOpenMap)).hom
    infer_instance
  · intro H; exact ⟨inferInstance, (TopCat.homeoOfIso (asIso f.base)).isOpenEmbedding⟩

@[deprecated (since := "2025-10-07")]
alias _root_.AlgebraicGeometry.isIso_iff_stalk_iso := isIso_iff_isIso_stalkMap

/-- An open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ Z.restrict f.isOpenEmbedding :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom)

local notation "forget" => Scheme.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (forget).mono_of_mono_map (inferInstanceAs (Mono f.toLRSHom))

lemma le_monomorphisms :
    IsOpenImmersion ≤ MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ ↦
  MorphismProperty.monomorphisms.infer_property _

instance : LocallyRingedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩

instance hasLimit_cospan_forget_of_left :
    HasLimit (cospan f g ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map f) ((forget).map g)))

open CategoryTheory.Limits.WalkingCospan

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map g) ((forget).map f)))

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.snd f.toLRSHom g.toLRSHom).toShHom)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.fst g.toLRSHom f.toLRSHom).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit _ _

instance : PreservesLimit (cospan g f) forget :=
  preservesPullback_symmetry _ _ _

instance hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget

instance hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget

instance : IsOpenImmersion (pullback.snd f g) := by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  change LocallyRingedSpace.IsOpenImmersion _
  rw [← this]
  infer_instance

instance : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

instance [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance

instance : PreservesLimit (cospan f g) Scheme.forgetToTop := by
  delta Scheme.forgetToTop
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ (K := cospan f g) _ _ (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace.forgetToTop]
  infer_instance

instance : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullback_symmetry _ _ _

instance : PreservesLimit (cospan f g) Scheme.forget := by delta Scheme.forget; infer_instance

instance : PreservesLimit (cospan g f) Scheme.forget := by delta Scheme.forget; infer_instance

theorem range_pullbackSnd :
    Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.snd f g).base from
    PreservesPullback.iso_hom_snd Scheme.forgetToTop f g, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, ← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

@[deprecated (since := "2025-10-07")] alias range_pullback_snd_of_left := range_pullbackSnd

theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd :
    (pullback.snd f g).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackSnd f g)

@[deprecated (since := "2025-10-07")]
alias opensRange_pullback_snd_of_left := Scheme.Hom.opensRange_pullbackSnd

theorem range_pullbackFst :
    Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.fst g f).base from
    PreservesPullback.iso_hom_fst Scheme.forgetToTop g f, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, ← @Set.preimage_univ _ _ (pullback.snd g.base f.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_fst_image_snd_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

@[deprecated (since := "2025-10-07")] alias range_pullback_fst_of_right := range_pullbackFst

theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst :
    (pullback.fst g f).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackFst f g)

@[deprecated (since := "2025-10-07")]
alias opensRange_pullback_fst_of_right := Scheme.Hom.opensRange_pullbackFst

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f g ≫ f) = Set.range f ∩ Set.range g := by
  rw [pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullbackSnd, Opens.map_obj, Opens.coe_mk,
    Set.image_preimage_eq_inter_range, Opens.carrier_eq_coe, Scheme.Hom.coe_opensRange]

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst g f ≫ g) = Set.range g ∩ Set.range f := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_pullbackFst,
    Opens.map_obj, Opens.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm, Opens.carrier_eq_coe, Scheme.Hom.coe_opensRange]

lemma image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (W : V.Opens) : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W := by
  ext x
  by_cases hx : x ∈ Set.range iU
  · obtain ⟨x, rfl⟩ := hx
    simp only [SetLike.mem_coe, Opens.map_coe, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← H.w]
    simp
  · constructor
    · rintro ⟨x, hx, rfl⟩; cases hx ⟨x, rfl⟩
    · rintro ⟨y, hy, e : iV y = f x⟩
      obtain ⟨x, rfl⟩ := (IsOpenImmersion.range_pullbackSnd iV f).ge ⟨y, e⟩
      rw [← H.isoPullback_inv_snd] at hx
      cases hx ⟨_, rfl⟩

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g ⊆ Set.range f) : Y ⟶ X :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩

@[reassoc (attr := simp)]
theorem lift_fac (H' : Set.range g ⊆ Set.range f) : lift f g H' ≫ f = g :=
  Scheme.Hom.ext' <| LocallyRingedSpace.IsOpenImmersion.lift_fac f.toLRSHom g.toLRSHom H'

theorem lift_uniq (H' : Set.range g ⊆ Set.range f) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  Scheme.Hom.ext' <| LocallyRingedSpace.IsOpenImmersion.lift_uniq
    f.toLRSHom g.toLRSHom H' l.toLRSHom congr(($hl).toLRSHom)

@[reassoc]
lemma comp_lift {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g ⊆ Set.range f) :
    g' ≫ lift f g H = lift f (g' ≫ g) (.trans (by simp [Set.range_comp_subset_range]) H) := by
  simp [← cancel_mono f]

theorem isPullback_lift_id
    {X U Y : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
    (H : Set.range f ⊆ Set.range g) :
    IsPullback (IsOpenImmersion.lift g f H) (𝟙 _) g f := by
  convert IsPullback.of_id_snd.paste_horiz (IsKernelPair.id_of_mono g)
  · exact (Category.comp_id _).symm
  · simp

/-- Two open immersions with equal range are isomorphic. -/
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f = Set.range g) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]
lemma isoOfRangeEq_inv_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac _ _ (le_of_eq e.symm)

theorem app_eq_invApp_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f ⁻¹ᵁ V = fg ⁻¹ᵁ (g ''ᵁ V) := by
  simp_all

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_appIso_inv_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f.app V = (g.appIso V).inv ≫ fg.app (g ''ᵁ V) ≫ Y.presheaf.map
      (eqToHom <| IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux f g fg H V).op := by
  subst H
  rw [Scheme.Hom.comp_app, Category.assoc, Scheme.Hom.appIso_inv_app_assoc, f.naturality_assoc,
    ← Functor.map_comp, ← op_comp, Quiver.Hom.unop_op, eqToHom_map, eqToHom_trans,
    eqToHom_op, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

theorem lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
    (V : U.Opens) :
    (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫
      X.presheaf.map (eqToHom <| app_eq_invApp_app_of_comp_eq_aux _ _ _ (lift_fac ..).symm V).op :=
  IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq _ _ _ (lift_fac _ _ _).symm _

/-- If `f` is an open immersion `X ⟶ Y`, the global sections of `X`
are naturally isomorphic to the sections of `Y` over the image of `f`. -/
noncomputable
def ΓIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Γ(X, f ⁻¹ᵁ U) ≅ Γ(Y, f.opensRange ⊓ U) :=
  (f.appIso (f⁻¹ᵁ U)).symm ≪≫
    Y.presheaf.mapIso (eqToIso <| (f.image_preimage_eq_opensRange_inf U).symm).op

@[simp]
lemma ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    (ΓIso f U).inv = f.appLE (f.opensRange ⊓ U) (f⁻¹ᵁ U)
      (by rw [← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  simp only [ΓIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
    Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

@[reassoc, elementwise]
lemma map_ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Y.presheaf.map (homOfLE inf_le_right).op ≫ (ΓIso f U).inv = f.app U := by
  simp [Scheme.Hom.appLE_eq_app]

@[reassoc, elementwise]
lemma app_ΓIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    f.app U ≫ (ΓIso f U).hom = Y.presheaf.map (homOfLE inf_le_right).op := by
  rw [← map_ΓIso_inv]
  simp [-ΓIso_inv]

@[deprecated (since := "2025-10-07")] alias map_ΓIso_hom := app_ΓIso_hom

/-- Given an open immersion `f : U ⟶ X`, the isomorphism between global sections
  of `U` and the sections of `X` at the image of `f`. -/
noncomputable
def ΓIsoTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Γ(X, ⊤) ≅ Γ(Y, f.opensRange) :=
  (f.appIso ⊤).symm ≪≫ Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op

instance {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f]
    (H' : Set.range g ⊆ Set.range f) [IsOpenImmersion g] :
    IsOpenImmersion (IsOpenImmersion.lift f g H') :=
  haveI : IsOpenImmersion (IsOpenImmersion.lift f g H' ≫ f) := by simpa
  IsOpenImmersion.of_comp _ f

end IsOpenImmersion

lemma isIso_of_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : f.opensRange = ⊤) : IsIso f := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

section MorphismProperty

instance isOpenImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsOpenImmersion where
  comp_mem f g _ _ := LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

instance isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance

instance isOpenImmersion_isMultiplicative :
    MorphismProperty.IsMultiplicative @IsOpenImmersion where
  id_mem _ := inferInstance

instance isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.IsStableUnderBaseChange.mk' <| by
    intro X Y Z f g _ H; infer_instance

end MorphismProperty

namespace Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

theorem image_basicOpen {U : X.Opens} (r : Γ(X, U)) :
    f ''ᵁ X.basicOpen r = Y.basicOpen ((f.appIso U).inv r) := by
  have e := Scheme.preimage_basicOpen f ((f.appIso U).inv r)
  rw [Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_res, inf_eq_right.mpr _] at e
  · rw [← e, f.image_preimage_eq_opensRange_inf, inf_eq_right]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  · exact (X.basicOpen_le r).trans (f.preimage_image_eq _).ge

lemma image_zeroLocus {U : X.Opens} (s : Set Γ(X, U)) :
    f '' X.zeroLocus s = Y.zeroLocus ((f.appIso U).inv.hom '' s) ∩ Set.range f := by
  ext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hx
    simp [f.isOpenEmbedding.injective.mem_set_image, ← Scheme.image_basicOpen]
  · simp only [Set.mem_inter_iff, hx, and_false, iff_false]
    exact fun H ↦ hx (Set.image_subset_range _ _ H)

end Scheme

end AlgebraicGeometry
