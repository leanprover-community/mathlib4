/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.InducedTopology
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

universe u

namespace CategoryTheory

open Functor Limits GrothendieckTopology

namespace Equivalence

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable {D : Type*} [Category D] (e : C ≌ D)
variable (A : Type*) [Category A]

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

theorem coverPreserving :
    CoverPreserving J (e.locallyCoverDense J).inducedTopology e.functor where
  cover_preserve {U S} h := by
    change _ ∈ J.sieves (e.inverse.obj (e.functor.obj U))
    convert J.pullback_stable (e.unitInv.app U) h
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
        e.unit.app Z ≫ e.unit.app _, (by simp)⟩

instance : IsCoverDense e.functor (e.locallyCoverDense J).inducedTopology where
  is_cover U := by
    change _ ∈ J.sieves _
    convert J.top_mem (e.inverse.obj U)
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    exact ⟨e.functor.obj Y, (Adjunction.homEquiv e.toAdjunction _ _).symm f,
      Presieve.in_coverByImage _ _, e.unit.app _, (by simp)⟩

instance : IsContinuous e.functor J (e.locallyCoverDense J).inducedTopology :=
  IsCoverDense.isContinuous _ _ _ (e.coverPreserving J)

instance : IsCoverDense e.inverse J where
  is_cover U := by
    convert J.top_mem U
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa using this

instance : IsContinuous e.inverse (e.locallyCoverDense J).inducedTopology J :=
  IsCoverDense.isContinuous _ _ _ (e.locallyCoverDense J).inducedTopology_coverPreserving

/-- The functor in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.functor : Sheaf J A ⥤ Sheaf (e.locallyCoverDense J).inducedTopology A where
  obj F := ⟨e.inverse.op ⋙ F.val, e.inverse.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.inverse.op f.val⟩

/-- The inverse in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.inverse : Sheaf (e.locallyCoverDense J).inducedTopology A ⥤ Sheaf J A where
  obj F := ⟨e.functor.op ⋙ F.val, e.functor.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.functor.op f.val⟩

/-- The unit iso in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.unitIso : 𝟭 (Sheaf J A) ≅ functor J e A ⋙ inverse J e A :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.unitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.unitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).inv_hom_id⟩ ) (by aesop)

/-- The counit iso in the equivalence of sheaf categories. -/
@[simps!]
def sheafCongr.counitIso : inverse J e A ⋙ functor J e A ≅ 𝟭 (Sheaf _ A) :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.counitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.counitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).inv_hom_id⟩ ) (by aesop)

/-- The equivalence of sheaf categories. -/
def sheafCongr : Sheaf J A ≌ Sheaf (e.locallyCoverDense J).inducedTopology A where
  functor := sheafCongr.functor J e A
  inverse := sheafCongr.inverse J e A
  unitIso := sheafCongr.unitIso J e A
  counitIso := sheafCongr.counitIso J e A
  functor_unitIso_comp X := by
    ext
    simp only [id_obj, sheafCongr.functor_obj_val_obj, comp_obj, Sheaf.instCategorySheaf_comp_val,
      NatTrans.comp_app, sheafCongr.inverse_obj_val_obj, Opposite.unop_op,
      sheafCongr.functor_map_val_app, sheafCongr.unitIso_hom_app_val_app,
      sheafCongr.counitIso_hom_app_val_app, sheafCongr.functor_obj_val_map, Quiver.Hom.unop_op,
      Sheaf.instCategorySheaf_id_val, NatTrans.id_app]
    simp [← Functor.map_comp, ← op_comp]

variable [HasSheafify (e.locallyCoverDense J).inducedTopology A]

/-- Transport a presheaf to the equivalent category and sheafify there. -/
noncomputable
def transportAndSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J A).inverse

/-- An auxiliary definition for the sheafification adjunction. -/
noncomputable
def transportIsoSheafToPresheaf : (e.sheafCongr J A).functor ⋙
    sheafToPresheaf (e.locallyCoverDense J).inducedTopology A ⋙
    e.op.congrLeft.inverse ≅ sheafToPresheaf J A :=
  NatIso.ofComponents (fun F ↦ isoWhiskerRight e.op.unitIso.symm F.val)
    (by intros; ext; simp [Equivalence.sheafCongr])

/-- Transporting and sheafifying is left adjoint to taking the underlying presheaf. -/
noncomputable
def transportSheafificationAdjunction : transportAndSheafify J e A ⊣ sheafToPresheaf J A :=
  ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr (A := A) J).symm.toAdjunction).ofNatIsoRight (transportIsoSheafToPresheaf _ _ _)

noncomputable instance : PreservesFiniteLimits <| transportAndSheafify J e A where
  preservesFiniteLimits _ := compPreservesLimitsOfShape _ _

/-- Transport `HasSheafify` along an equivalence of sites. -/
theorem hasSheafify : HasSheafify J A :=
  HasSheafify.mk' J A (transportSheafificationAdjunction J e A)

variable {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B)
  [(e.locallyCoverDense J).inducedTopology.HasSheafCompose F]

theorem hasSheafCompose : J.HasSheafCompose F where
  isSheaf P hP := by
    let K := (e.locallyCoverDense J).inducedTopology
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

end Equivalence

variable {C : Type*} [Category C] [EssentiallySmall C] (J : GrothendieckTopology C)
variable (A : Type*) [Category A]
variable (B : Type*) [Category B] (F : A ⥤ B)
variable [HasSheafify ((equivSmallModel C).locallyCoverDense J).inducedTopology A]
variable [((equivSmallModel C).locallyCoverDense J).inducedTopology.HasSheafCompose F]

/-- Transport to a small model and sheafify there. -/
noncomputable
def smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A := (equivSmallModel C).transportAndSheafify J A

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J A

noncomputable instance hasSheafifyEssentiallySmallSite : HasSheafify J A :=
  (equivSmallModel C).hasSheafify J A

instance hasSheafComposeEssentiallySmallSite : HasSheafCompose J F :=
  (equivSmallModel C).hasSheafCompose J F

instance hasLimitsEssentiallySmallSite
    [HasLimits <| Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A] :
    HasLimitsOfSize <| Sheaf J A :=
  Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J A).functor

instance hasColimitsEssentiallySmallSite
    [HasColimits <| Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A] :
    HasColimitsOfSize <| Sheaf J A :=
  Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J A).functor

end CategoryTheory
