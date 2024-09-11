/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.Whiskering
/-!
# Equivalences of sheaf categories

Given a site `(C, J)` and a category `D` which is equivalent to `C`, with `C` and `D` possibly large
and possibly in different universes, we transport the Grothendieck topology `J` on `C` to `D` and
prove that the sheaf categories are equivalent.

We also prove that sheafification and the property `HasSheafCompose` transport nicely over this
equivalence, and apply it to essentially small sites. We also provide instances for existence of
sufficiently small limits in the sheaf category on the essentially small site.

## Main definitions

* `CategoryTheory.Equivalence.sheafCongr` is the equivalence of sheaf categories.

* `CategoryTheory.Equivalence.transportAndSheafify` is the functor which takes a presheaf on `C`,
  transports it over the equivalence to `D`, sheafifies there and then transports back to `C`.

* `CategoryTheory.Equivalence.transportSheafificationAdjunction`: `transportAndSheafify` is
  left adjoint to the functor taking a sheaf to its underlying presheaf.

* `CategoryTheory.smallSheafify` is the functor which takes a presheaf on an essentially small site
  `(C, J)`, transports to a small model, sheafifies there and then transports back to `C`.

* `CategoryTheory.smallSheafificationAdjunction`: `smallSheafify` is left adjoint to the functor
  taking a sheaf to its underlying presheaf.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

open Functor Limits GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)
variable (A : Type u₃) [Category.{v₃} A]

namespace Equivalence

instance (priority := 900) [G.IsEquivalence] : IsCoverDense G J where
  is_cover U := by
    let e := (asEquivalence G).symm
    convert J.top_mem U
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa [g] using this

instance : e.functor.IsDenseSubsite J (e.inverse.inducedTopology J) := by
  have : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext X S
    rw [show S ∈ (e.functor.inducedTopology (e.inverse.inducedTopology J)) X ↔ _
      from (GrothendieckTopology.pullback_mem_iff_of_isIso (i := e.unit.app X)).symm]
    congr!; ext Y f; simp
  nth_rw 1 [this]
  infer_instance

lemma eq_inducedTopology_of_isDenseSubsite [e.inverse.IsDenseSubsite K J] :
    K = e.inverse.inducedTopology J := by
  ext
  exact (e.inverse.functorPushforward_mem_iff K J).symm

variable [e.inverse.IsDenseSubsite K J]

instance : e.functor.IsDenseSubsite J K := by
  rw [e.eq_inducedTopology_of_isDenseSubsite J K]
  infer_instance

/-- The functor in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.functor : Sheaf J A ⥤ Sheaf K A where
  obj F := ⟨e.inverse.op ⋙ F.val, e.inverse.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.inverse.op f.val⟩

/-- The inverse in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.inverse : Sheaf K A ⥤ Sheaf J A where
  obj F := ⟨e.functor.op ⋙ F.val, e.functor.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.functor.op f.val⟩

/-- The unit iso in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.unitIso : 𝟭 (Sheaf J A) ≅ functor J K e A ⋙ inverse J K e A :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.unitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.unitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).inv_hom_id⟩ ) (by aesop)

/-- The counit iso in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.counitIso : inverse J K e A ⋙ functor J K e A ≅ 𝟭 (Sheaf _ A) :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.counitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.counitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).inv_hom_id⟩ ) (by aesop)

/-- The equivalence of sheaf categories. -/
def sheafCongr : Sheaf J A ≌ Sheaf K A where
  functor := sheafCongr.functor J K e A
  inverse := sheafCongr.inverse J K e A
  unitIso := sheafCongr.unitIso J K e A
  counitIso := sheafCongr.counitIso J K e A
  functor_unitIso_comp X := by
    ext
    simp only [id_obj, sheafCongr.functor_obj_val_obj, comp_obj,
      Sheaf.instCategorySheaf_comp_val, NatTrans.comp_app, sheafCongr.inverse_obj_val_obj,
      Opposite.unop_op, sheafCongr.functor_map_val_app,
      sheafCongr.unitIso_hom_app_val_app, sheafCongr.counitIso_hom_app_val_app,
      sheafCongr.functor_obj_val_map, Quiver.Hom.unop_op, Sheaf.instCategorySheaf_id_val,
      NatTrans.id_app]
    simp [← Functor.map_comp, ← op_comp]

variable [HasSheafify K A]

/-- Transport a presheaf to the equivalent category and sheafify there. -/
noncomputable
def transportAndSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J K A).inverse

/-- An auxiliary definition for the sheafification adjunction. -/
noncomputable
def transportIsoSheafToPresheaf : (e.sheafCongr J K A).functor ⋙
    sheafToPresheaf K A ⋙ e.op.congrLeft.inverse ≅ sheafToPresheaf J A :=
  NatIso.ofComponents (fun F ↦ isoWhiskerRight e.op.unitIso.symm F.val)
    (by intros; ext; simp [Equivalence.sheafCongr])

/-- Transporting and sheafifying is left adjoint to taking the underlying presheaf. -/
noncomputable
def transportSheafificationAdjunction : transportAndSheafify J K e A ⊣ sheafToPresheaf J A :=
  ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (transportIsoSheafToPresheaf _ _ _ _)

noncomputable instance : PreservesFiniteLimits <| transportAndSheafify J K e A where
  preservesFiniteLimits _ := compPreservesLimitsOfShape _ _

include K e in
/-- Transport `HasSheafify` along an equivalence of sites. -/
theorem hasSheafify : HasSheafify J A :=
  HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

variable {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B)
  [K.HasSheafCompose F]

include K e in
theorem hasSheafCompose : J.HasSheafCompose F where
  isSheaf P hP := by
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

variable [ConcreteCategory.{w} A]
variable {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)

end Equivalence

variable (B : Type u₄) [Category.{v₄} B] (F : A ⥤ B)

section
variable [EssentiallySmall.{w} C]
variable [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A]
variable [((equivSmallModel C).inverse.inducedTopology J).HasSheafCompose F]

/-- Transport to a small model and sheafify there. -/
noncomputable
def smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A := (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).inverse.inducedTopology J) A

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J _ A

noncomputable instance hasSheafifyEssentiallySmallSite : HasSheafify J A :=
  (equivSmallModel C).hasSheafify J ((equivSmallModel C).inverse.inducedTopology J) A

instance hasSheafComposeEssentiallySmallSite : HasSheafCompose J F :=
  (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).inverse.inducedTopology J) F

instance hasLimitsEssentiallySmallSite
    [HasLimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
    HasLimitsOfSize.{max v₃ w, max v₃ w} <| Sheaf J A :=
  Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

instance hasColimitsEssentiallySmallSite
    [HasColimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
    HasColimitsOfSize.{max v₃ w, max v₃ w} <| Sheaf J A :=
  Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

end

namespace GrothendieckTopology

variable {A}
variable [G.IsCoverDense J] [G.Full]

section
variable [Functor.IsContinuous.{v₃} G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]

open Localization

lemma W_inverseImage_whiskeringLeft :
    K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op) = J.W := by
  ext P Q f
  have h₁ : K.W (A := A) =
    Localization.LeftBousfield.W (· ∈ Set.range (sheafToPresheaf J A ⋙
      ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op)).obj) := by
    rw [W_eq_W_range_sheafToPresheaf_obj, ← LeftBousfield.W_isoClosure]
    conv_rhs => rw [← LeftBousfield.W_isoClosure]
    apply congr_arg
    ext P
    constructor
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨_, ⟨_, rfl⟩, ⟨e.trans ((sheafToPresheaf _ _).mapIso
        ((G.sheafPushforwardContinuous A K J).objObjPreimageIso R).symm)⟩⟩
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨G.op ⋙ R.val, ⟨(G.sheafPushforwardContinuous A K J).obj R, rfl⟩, ⟨e⟩⟩
  have h₂ : ∀ (R : Sheaf J A),
    Function.Bijective (fun (g : G.op ⋙ Q ⟶ G.op ⋙ R.val) ↦ whiskerLeft G.op f ≫ g) ↔
      Function.Bijective (fun (g : Q ⟶ R.val) ↦ f ≫ g) := fun R ↦ by
    rw [← Function.Bijective.of_comp_iff _
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G Q R.val R.cond)]
    exact Function.Bijective.of_comp_iff'
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P R.val R.cond)
        (fun g ↦ f ≫ g)
  rw [h₁, J.W_eq_W_range_sheafToPresheaf_obj, MorphismProperty.inverseImage_iff]
  constructor
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).1 (h _ ⟨R, rfl⟩)
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).2 (h _ ⟨R, rfl⟩)

lemma W_whiskerLeft_iff {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    K.W (whiskerLeft G.op f) ↔ J.W f := by
  rw [← W_inverseImage_whiskeringLeft J K G]
  rfl

end

lemma PreservesSheafification.transport
    [Functor.IsContinuous.{v₄} G K J] [Functor.IsContinuous.{v₃} G K J]
    [(G.sheafPushforwardContinuous B K J).EssSurj]
    [(G.sheafPushforwardContinuous A K J).EssSurj]
    [K.PreservesSheafification F] : J.PreservesSheafification F where
  le P Q f hf := by
    rw [← J.W_whiskerLeft_iff (G := G) (K := K)] at hf
    have := K.W_of_preservesSheafification F (whiskerLeft G.op f) hf
    rwa [whiskerRight_left,
      K.W_whiskerLeft_iff (G := G) (J := J) (f := whiskerRight f F)] at this

variable [Functor.IsContinuous.{v₃} G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]
variable [G.IsCocontinuous K J] [ConcreteCategory A]
  [K.WEqualsLocallyBijective A]

lemma WEqualsLocallyBijective.transport (hG : CoverPreserving K J G) :
    J.WEqualsLocallyBijective A where
  iff f := by
    rw [← W_whiskerLeft_iff J K G f, ← Presheaf.isLocallyInjective_whisker_iff K J G f hG,
      ← Presheaf.isLocallySurjective_whisker_iff K J G f hG, W_iff_isLocallyBijective]

variable [EssentiallySmall.{w} C]
  [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]

instance [((equivSmallModel C).inverse.inducedTopology J).WEqualsLocallyBijective A] :
    J.WEqualsLocallyBijective A :=
  WEqualsLocallyBijective.transport J ((equivSmallModel C).inverse.inducedTopology J)
    (equivSmallModel C).inverse (IsDenseSubsite.coverPreserving _ _ _)

variable [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) B]
variable [PreservesSheafification ((equivSmallModel C).inverse.inducedTopology J) F]

instance : PreservesSheafification J F :=
  PreservesSheafification.transport (A := A) J
    ((equivSmallModel C).inverse.inducedTopology J) (equivSmallModel C).inverse B F

end GrothendieckTopology

end CategoryTheory
