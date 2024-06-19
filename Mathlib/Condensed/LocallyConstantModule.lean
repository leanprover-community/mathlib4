import Mathlib.Condensed.LocallyConstant
import Mathlib.Condensed.Module
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.LocallyConstant.Algebra

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor

namespace CategoryTheory.Sheaf

open Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]
  {B : Type*} [Category B] (U : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose U] [J.PreservesSheafification U]

@[simps!]
noncomputable def constantCommuteCompose :
    constantSheaf J A ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J A) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

@[simps!]
noncomputable def constantCommuteComposeApp (M : A) :
    (sheafCompose J U).obj ((constantSheaf J A).obj M) ≅ (constantSheaf J B).obj (U.obj M) :=
  (constantCommuteCompose J U).app M

@[reassoc (attr := simp)]
lemma sheafComposeNatIso_app_counit (P : Sheaf J A) :
    (sheafComposeNatIso J U (sheafificationAdjunction J A)
      (sheafificationAdjunction J B)).hom.app _ ≫ (sheafCompose J U).map
        ((sheafificationAdjunction J A).counit.app P) =
          (sheafificationAdjunction J B).counit.app ((sheafCompose J U).obj P) := by
  simp only [sheafToPresheaf_obj, Functor.comp_obj, whiskeringRight_obj_obj, Functor.id_obj,
    sheafComposeNatIso, sheafComposeNatTrans, sheafCompose_obj_val, sheafificationAdjunction_unit_app, asIso_hom]
  erw [Adjunction.homEquiv_counit]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj P).cond
  simp [← whiskerRight_comp]

variable {t : C} (ht : IsTerminal t)

lemma _root_.CategoryTheory.constantSheafAdj_counit_app (F : Sheaf J A) :
    (constantSheafAdj J A ht).counit.app F =
      (presheafToSheaf J A).map ((constantPresheafAdj A ht).counit.app F.val) ≫
        (sheafificationAdjunction J A).counit.app F := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.cond
  simp only [flip_obj_obj, sheafToPresheaf_obj, comp_obj, id_obj, constantSheafAdj, Adjunction.comp,
    evaluation_obj_obj, constantPresheafAdj, Opposite.op_unop, Adjunction.mkOfUnitCounit_unit,
    Adjunction.mkOfUnitCounit_counit, NatTrans.comp_app, associator_hom_app, whiskerLeft_app,
    whiskerRight_app, instCategorySheaf_comp_val, instCategorySheaf_id_val,
    sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, comp_id,
    toSheafify_sheafifyLift]
  erw [id_comp, toSheafify_sheafifyLift]

lemma constantCommuteComposeApp_counit_comp' (F : Sheaf J A) :
    (constantCommuteComposeApp J U _).inv ≫
      (sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F) =
        (constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F) := by
  simp only [constantSheafAdj_counit_app, constantCommuteComposeApp, constantCommuteCompose,
    flip_obj_obj, sheafToPresheaf_obj, id_obj, NatIso.trans_app, comp_obj,
    whiskeringRight_obj_obj, Iso.trans_inv, Iso.app_inv, isoWhiskerRight_inv, Iso.symm_inv,
    whiskerRight_app, isoWhiskerLeft_inv, whiskerLeft_app, evaluation_obj_obj, Functor.map_comp,
    assoc, sheafCompose_obj_val, ← sheafComposeNatIso_app_counit]
  simp only [← assoc]
  congr 1
  have : (compConstIso Cᵒᵖ U).hom.app (F.val.obj ⟨t⟩) ≫
      { app := fun Y ↦ (F.val ⋙ U).map (ht.from _).op
        naturality := by intros; simp; rw [← Functor.map_comp, ← Functor.map_comp]; congr; simp } =
      ((constantPresheafAdj B ht).counit.app (F.val ⋙ U)) := by ext; simp [constantPresheafAdj]
  simp only [← this, assoc, Functor.map_comp]
  congr 1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj ((presheafToSheaf J A).obj F.val)).cond
  simp only [sheafCompose_obj_val, instCategorySheaf_comp_val, sheafCompose_map_val, comp_obj,
    whiskeringRight_obj_obj, Functor.comp_map]
  erw [← toSheafify_naturality_assoc, sheafComposeIso_hom_fac, sheafComposeIso_hom_fac_assoc]
  ext
  simp only [comp_obj, const_obj_obj, NatTrans.comp_app, whiskerRight_app, ← Functor.map_comp]
  congr 1
  simp only [constantPresheafAdj, comp_obj, evaluation_obj_obj, id_obj, Opposite.op_unop,
    Adjunction.mkOfUnitCounit_counit, NatTrans.naturality]
  erw [← NatTrans.comp_app, ← toSheafify_naturality]
  simp only [NatTrans.comp_app, const_obj_obj, NatTrans.naturality]

lemma constantCommuteComposeApp_counit_comp (F : Sheaf J A) :
    (sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F) =
      (constantCommuteComposeApp J U _).hom ≫
        (constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F) := by
  simp [← constantCommuteComposeApp_counit_comp']


end CategoryTheory.Sheaf

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace Condensed.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHaus` given by locally constant
maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ comapₗ R f.unop }
  map f := { app := fun S ↦ mapₗ R f }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `Condensed.LocallyConstantModule.functorToPresheaves` lands in condensed modules. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) where
  obj X := {
    val := (functorToPresheaves.{w, u} R).obj X
    cond := by
      have := CompHausLike.preregular hs
      apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp (s :=
        CategoryTheory.forget (ModuleCat R))
      exact ((Condensed.LocallyConstant.functor P hs).obj _).cond }
  map f := ⟨(functorToPresheaves.{w, u} R).map f⟩

end Condensed.LocallyConstantModule

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u+1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

def LocallyConstant.functorIsoDiscrete_components (M : ModuleCat R) :
    (functor R).obj M ≅ (Condensed.discrete _).obj M := by
  simp only [functor, Condensed.LocallyConstantModule.functor, Condensed.discrete_obj]
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  sorry

def LocallyConstant.functorIsoDiscrete : functor R ≅ Condensed.discrete _ :=
  sorry

end CondensedMod

namespace LightCondMod

variable (R : Type u) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

def LocallyConstant.functorIsoDiscrete : functor R ≅ LightCondensed.discrete _ := sorry

end LightCondMod
