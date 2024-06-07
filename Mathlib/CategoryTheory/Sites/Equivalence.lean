/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.EpiMono
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

universe w v u

namespace CategoryTheory

open Functor Limits GrothendieckTopology Presheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable {D : Type*} [Category D] (K : GrothendieckTopology D) (e : C ≌ D)
variable (A : Type*) [Category A]

namespace Presheaf

variable (H : C ⥤ D) [ConcreteCategory A] {F G : Dᵒᵖ ⥤ A} (f : F ⟶ G)

lemma isLocallyInjective_whisker [H.IsCocontinuous J K] [IsLocallyInjective K f] :
    IsLocallyInjective J (whiskerLeft H.op f) where
  equalizerSieve_mem x y h := H.cover_lift J K (equalizerSieve_mem K f x y h)

lemma isLocallyInjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallyInjective J (whiskerLeft H.op f)] : IsLocallyInjective K f where
  equalizerSieve_mem {X} a b h := by
    apply K.transitive (Functor.IsCoverDense.is_cover (G := H) (K := K) X.unop)
    intro Y g ⟨⟨Z, lift, map, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    apply K.pullback_stable
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_)
      (hH.cover_preserve <| equalizerSieve_mem J (whiskerLeft H.op f)
        ((forget A).map (F.map map.op) a) ((forget A).map (F.map map.op) b) ?_)
    · intro W q hq
      simpa using hq
    · simp only [comp_obj, op_obj, whiskerLeft_app, Opposite.op_unop]
      erw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

lemma isLocallySurjective_whisker_isCocontinuous [H.IsCocontinuous J K] [IsLocallySurjective K f] :
    IsLocallySurjective J (whiskerLeft H.op f) where
  imageSieve_mem a := H.cover_lift J K (imageSieve_mem K f a)

lemma isLocallySurjective_of_whisker_coverPreserving_isCoverDense (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallySurjective J (whiskerLeft H.op f)] : IsLocallySurjective K f where
  imageSieve_mem {X} a := by
    apply K.transitive (Functor.IsCoverDense.is_cover (G := H) (K := K) X)
    intro Y g ⟨⟨Z, lift, map, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    apply K.pullback_stable
    have hh := hH.cover_preserve <|
      imageSieve_mem J (whiskerLeft H.op f) ((forget A).map (G.map map.op) a)
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_) hh
    intro W q ⟨x, h⟩
    simp only [Sieve.functorPullback_apply, Presieve.functorPullback_mem, Sieve.pullback_apply]
    exact ⟨x, by simpa using h⟩

end Presheaf

namespace Equivalence

theorem locallyCoverDense : LocallyCoverDense J e.inverse := by
  intro X T
  convert T.prop
  ext Z f
  constructor
  · rintro ⟨_, _, g', hg, rfl⟩
    exact T.val.downward_closed hg g'
  · intro hf
    refine ⟨e.functor.obj Z, (Adjunction.homEquiv e.toAdjunction _ _).symm f, e.unit.app Z, ?_, ?_⟩
    · simp only [Adjunction.homEquiv_counit, Functor.id_obj, Equivalence.toAdjunction_counit,
        Sieve.functorPullback_apply, Presieve.functorPullback_mem, Functor.map_comp,
        Equivalence.inv_fun_map, Functor.comp_obj, Category.assoc, Equivalence.unit_inverse_comp,
        Category.comp_id]
      exact T.val.downward_closed hf _
    · simp


theorem functorPushforward_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by
  ext Z f
  rw [← Sieve.functorPushforward_comp]
  simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left, id_obj,
    comp_obj, Sieve.pullback_apply]
  constructor
  · rintro ⟨W, g, hg, x, rfl⟩
    rw [Category.assoc]
    apply S.downward_closed
    simpa using S.downward_closed hg _
  · intro hf
    exact ⟨_, e.unitInv.app Z ≫ f ≫ e.unitInv.app U, S.downward_closed hf _,
      e.unit.app Z ≫ e.unit.app _, by simp⟩

theorem pullback_functorPushforward_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by
  ext Z f
  rw [← Sieve.functorPushforward_comp]
  simp only [id_obj, comp_obj, Sieve.pullback_apply, Sieve.functorPushforward_apply,
    Presieve.functorPushforward, Functor.comp_map, inv_fun_map, exists_and_left]
  constructor
  · intro ⟨W, g, hg, x, h⟩
    simp only [← Category.assoc] at h
    change _ ≫ (e.unitIso.app _).hom = _ ≫ (e.unitIso.app _).hom at h
    rw [Iso.cancel_iso_hom_right] at h
    rw [h]
    exact S.downward_closed hg _
  · intro hf
    exact ⟨_, e.unitInv.app Z ≫ f, S.downward_closed hf _, e.unit.app Z ≫ e.unit.app _, by simp⟩

theorem coverPreserving' : CoverPreserving J (e.locallyCoverDense J).inducedTopology e.functor where
  cover_preserve {U S} h := by
    change _ ∈ J.sieves (e.inverse.obj (e.functor.obj U))
    convert J.pullback_stable (e.unitInv.app U) h
    exact e.functorPushforward_eq_pullback S

instance : IsCoverDense e.functor (e.locallyCoverDense J).inducedTopology where
  is_cover U := by
    change _ ∈ J.sieves _
    convert J.top_mem (e.inverse.obj U)
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    exact ⟨e.functor.obj Y, (Adjunction.homEquiv e.toAdjunction _ _).symm f,
      Presieve.in_coverByImage _ _, e.unit.app _, by simp⟩

instance : IsCoverDense e.inverse J where
  is_cover U := by
    convert J.top_mem U
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa [g] using this

/-- A class saying that the equivalence `e` transports the Grothendieck topology `J` to `K`. -/
class TransportsGrothendieckTopology : Prop where
  /-- `K` is equal to the induced topology. -/
  eq_inducedTopology : K = (e.locallyCoverDense J).inducedTopology

instance : e.TransportsGrothendieckTopology J (e.locallyCoverDense J).inducedTopology := ⟨rfl⟩

variable [e.TransportsGrothendieckTopology J K]

theorem eq_inducedTopology_of_transports : K = (e.locallyCoverDense J).inducedTopology :=
  TransportsGrothendieckTopology.eq_inducedTopology

instance : e.symm.TransportsGrothendieckTopology K J where
  eq_inducedTopology := by
    rw [e.eq_inducedTopology_of_transports J K]
    ext X S
    change _ ↔ _ ∈ J.sieves _
    simp only [symm_inverse]
    constructor
    · intro h
      convert J.pullback_stable (e.unitInv.app X) h
      exact e.functorPushforward_eq_pullback S
    · intro h
      convert J.pullback_stable (e.unit.app X) h
      exact (e.pullback_functorPushforward_eq S).symm

theorem coverPreserving : CoverPreserving J K e.functor := by
  rw [e.eq_inducedTopology_of_transports J K]
  exact e.coverPreserving' J

theorem coverPreserving_symm : CoverPreserving K J e.inverse := by
  rw [e.symm.eq_inducedTopology_of_transports K J]
  exact e.symm.coverPreserving' K

instance : IsContinuous e.functor J K := by
  have : IsCoverDense e.functor K := by rw [e.eq_inducedTopology_of_transports J K]; infer_instance
  exact IsCoverDense.isContinuous _ _ _ (e.coverPreserving J K)

instance : IsCocontinuous e.functor J K := by
  rw [e.symm.eq_inducedTopology_of_transports K J]
  exact (e.symm.locallyCoverDense _).inducedTopology_isCocontinuous

instance : IsContinuous e.inverse K J :=
  IsCoverDense.isContinuous _ _ _ (e.coverPreserving_symm J K)

instance : IsCocontinuous e.inverse K J := by
  rw [e.eq_inducedTopology_of_transports J K]
  exact (e.locallyCoverDense _).inducedTopology_isCocontinuous

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

-- /-- The equivalence of sheaf categories explicitly stated for the induced topology. -/
-- abbrev sheafCongrRight : Sheaf J A ≌ Sheaf (e.locallyCoverDense J).inducedTopology A :=
--   sheafCongr e A rfl

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

/-- Transport `HasSheafify` along an equivalence of sites. -/
theorem hasSheafify : HasSheafify J A :=
  HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

variable {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B)
  [K.HasSheafCompose F]

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

open Presheaf

lemma isLocallyInjective_whisker [IsLocallyInjective J f] :
    IsLocallyInjective K (whiskerLeft e.inverse.op f) :=
  isLocallyInjective_whisker_isCocontinuous K J A e.inverse f

lemma isLocallyInjective_of_whisker [IsLocallyInjective K (whiskerLeft e.inverse.op f)] :
    IsLocallyInjective J f :=
  isLocallyInjective_of_whisker_coverPreserving_isCoverDense K J A _ f (e.coverPreserving_symm J K)

lemma isLocallySurjective_whisker [IsLocallySurjective J f] :
    IsLocallySurjective K (whiskerLeft e.inverse.op f) :=
  isLocallySurjective_whisker_isCocontinuous K J A e.inverse f

lemma isLocallySurjective_of_whisker [IsLocallySurjective K (whiskerLeft e.inverse.op f)] :
    IsLocallySurjective J f :=
  isLocallySurjective_of_whisker_coverPreserving_isCoverDense K J A _ f (e.coverPreserving_symm J K)

open ConcreteCategory Sheaf

variable [HasFunctorialSurjectiveInjectiveFactorization A] [K.WEqualsLocallyBijective A]
variable [HasSheafify K A] [K.HasSheafCompose (forget A)] [Balanced (Sheaf K A)]
variable {F G : Sheaf J A} (f : F ⟶ G)

lemma isLocallySurjective_iff_epi : IsLocallySurjective f ↔ Epi f := by
  constructor
  · intro
    have := e.hasSheafCompose J K (forget A)
    infer_instance
  · intro h
    rw [← (e.sheafCongr J K A).functor.epi_map_iff_epi, ← isLocallySurjective_iff_epi'] at h
    have : Presheaf.IsLocallySurjective K (whiskerLeft e.inverse.op f.val) := h
    exact e.isLocallySurjective_of_whisker J K f.val

end Equivalence

variable [EssentiallySmall C]
variable (B : Type*) [Category B] (F : A ⥤ B)
variable [HasSheafify ((equivSmallModel C).locallyCoverDense J).inducedTopology A]
variable [((equivSmallModel C).locallyCoverDense J).inducedTopology.HasSheafCompose F]

/-- Transport to a small model and sheafify there. -/
noncomputable
def smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A := (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).locallyCoverDense J).inducedTopology A

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J _ A

noncomputable instance hasSheafifyEssentiallySmallSite : HasSheafify J A :=
  (equivSmallModel C).hasSheafify J ((equivSmallModel C).locallyCoverDense J).inducedTopology A

instance hasSheafComposeEssentiallySmallSite : HasSheafCompose J F :=
  (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).locallyCoverDense J).inducedTopology F

instance hasLimitsEssentiallySmallSite
    [HasLimits <| Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A] :
    HasLimitsOfSize <| Sheaf J A :=
  Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).locallyCoverDense J).inducedTopology A).functor

instance hasColimitsEssentiallySmallSite
    [HasColimits <| Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A] :
    HasColimitsOfSize <| Sheaf J A :=
  Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).locallyCoverDense J).inducedTopology A).functor

open ConcreteCategory

variable [ConcreteCategory.{w} A]
variable [HasFunctorialSurjectiveInjectiveFactorization A]
  [((equivSmallModel C).locallyCoverDense J).inducedTopology.WEqualsLocallyBijective A]
variable [((equivSmallModel C).locallyCoverDense J).inducedTopology.HasSheafCompose (forget A)]
variable [Balanced (Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A)]
variable {F G : Sheaf J A} (f : F ⟶ G)

lemma Sheaf.isLocallySurjective_iff_epi_of_site_essentiallySmall :
    IsLocallySurjective f ↔ Epi f :=
  (equivSmallModel C).isLocallySurjective_iff_epi _
    ((equivSmallModel C).locallyCoverDense J).inducedTopology f

end CategoryTheory
