/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.LocallyConstant
import Mathlib.Topology.Category.Profinite.Extend
/-!

# The condensed set given by left Kan extension from `FintypeCat` to `Profinite`.
-/


universe u

noncomputable section

open CategoryTheory Functor Limits Condensed FintypeCat StructuredArrow CompHausLike.LocallyConstant

attribute [local instance] FintypeCat.discreteTopology ConcreteCategory.instFunLike

namespace Condensed

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
    (c : Cone <| F ⋙ toProfinite)

section LocallyConstantAsColimit

open Profinite.Extend

variable (X : Type (u+1))

abbrev locallyConstantPresheaf : Profiniteᵒᵖ ⥤ Type _ :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u+1}.obj X

noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i) = fj.comap (c.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [comp_obj, op_obj, toProfinite_obj, functorToPresheaves_obj_obj, CompHausLike.coe_of,
      Functor.comp_map, op_map, Quiver.Hom.unop_op, functorToPresheaves_obj_map]
    apply DFunLike.ext
    intro x'
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x'
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

variable (S : Profinite)

noncomputable def isColimitLocallyConstantPresheafDiagram :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

end LocallyConstantAsColimit

section LanPresheaf

@[simps!]
def lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

@[simps!]
def lanPresheafUnit (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :
    toProfinite.op ⋙ F ⟶ toProfinite.op ⋙ lanPresheaf F :=
  pointwiseLeftKanExtensionUnit _ _

instance (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :
    IsLeftKanExtension (lanPresheaf F) (lanPresheafUnit F) := by
  dsimp [lanPresheaf, lanPresheafUnit]
  infer_instance

variable {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G)

-- TODO: generalise and PR
def lanPresheafIso : lanPresheaf F ≅ lanPresheaf G where
  hom := descOfIsLeftKanExtension _ (lanPresheafUnit F) (lanPresheaf G) (i.hom ≫ lanPresheafUnit G)
  inv := descOfIsLeftKanExtension _ (lanPresheafUnit G) (lanPresheaf F) (i.inv ≫ lanPresheafUnit F)
  hom_inv_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf F) (α := lanPresheafUnit F)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)
      (G := lanPresheaf G) (β := i.hom ≫ lanPresheafUnit G), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)]
    simp
  inv_hom_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf G) (α := lanPresheafUnit G)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)
      (G := lanPresheaf F) (β := i.inv ≫ lanPresheafUnit F), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)]
    simp

end LanPresheaf

section ColimitLocallyConstant

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
  (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)

variable (S : Profinite.{u})

def functorToPresheaves_iso_colimit :
    colimit ((Profinite.Extend.functorOp S.asLimitCone) ⋙
      ((CostructuredArrow.proj toProfinite.op ⟨S⟩) ⋙ toProfinite.op ⋙ F)) ≅ F.obj ⟨S⟩ :=
  (colimit.isColimit _).coconePointUniqueUpToIso (hF S)

instance (S : Profinite) : Final <|
    Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

def functorToPresheaves_iso_colimit_lan :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    functorToPresheaves_iso_colimit F hF S

@[simp]
lemma functorToPresheaves_iso_colimit_lan_hom : (functorToPresheaves_iso_colimit_lan F hF S).hom =
    colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp only [lanPresheaf_obj, functorToPresheaves_iso_colimit_lan, Final.colimitIso, Iso.trans_hom,
    Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, colimit.pre_desc]
  rfl

def lanPresheaf_iso_functorToPresheaves : lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (functorToPresheaves_iso_colimit_lan F hF S)) fun _ ↦ ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, pointwiseLeftKanExtension_map,
    functorToPresheaves_iso_colimit_lan_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ ↦ (by simp)

end ColimitLocallyConstant

def lanPresheaf_iso_functorToPresheaves' (X : Type (u+1)) :
    lanPresheaf (locallyConstantPresheaf X) ≅
    locallyConstantPresheaf X :=
  lanPresheaf_iso_functorToPresheaves
    (locallyConstantPresheaf X)
    fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

def lanCondensedSet' (X : Type (u+1)) : Sheaf (coherentTopology Profinite.{u}) (Type (u+1)) where
  val := lanPresheaf (locallyConstantPresheaf X)
  cond := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheaf_iso_functorToPresheaves' X)]
    exact ((Condensed.LocallyConstant.functor.{u+1, u}
      (hs := fun _ _ _ ↦ ((Profinite.effectiveEpi_tfae _).out 0 2).mp)).obj X).cond

def lanCondensedSet (X : Type (u+1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanCondensedSet' X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) [p : PreservesFiniteProducts F]

open Opposite

@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u+1) where
  obj X := X.unop → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)
  map f g := g ∘ f.unop

def finYonedaIso :
    toProfinite.op ⋙ (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)))  ≅
    finYoneda F := by
  refine NatIso.ofComponents ?_ ?_
  · intro Y
    exact {
      hom := fun f ↦ f.toFun
      inv := fun f ↦ ⟨f, (by
        let _ : TopologicalSpace Y.unop := ⊥
        have : DiscreteTopology (toProfinite.obj Y.unop) :=
          inferInstanceAs (DiscreteTopology Y.unop)
        exact IsLocallyConstant.of_discrete _
        )⟩
      hom_inv_id := by aesop
      inv_hom_id := by aesop
    }
  · aesop

def mapOfElement {X : FintypeCat} (x : X) : FintypeCat.of (PUnit.{u+1}) ⟶ X := fun _ ↦ x

def fintypeCatAsCofan (X : FintypeCat) :
    Cofan (fun (_ : X) ↦ toProfinite.obj (of (PUnit.{u+1}))) :=
  Cofan.mk (toProfinite.obj X) (fun x ↦ toProfinite.map (mapOfElement x))

def fintypeCatAsCofanIsColimit (X : FintypeCat.{u}) :
    IsColimit (fintypeCatAsCofan X) := by
  refine mkCofanColimit _ (fun t ↦ ⟨fun x ↦ t.inj x PUnit.unit, continuous_bot⟩) (by aesop) ?_
  intro t m h
  ext x
  change m x = t.inj x _
  rw [← h x]
  rfl

def fintypeCatAsCofanOpIsLimit (X : FintypeCat.{u}) : IsLimit (fintypeCatAsCofan X).op :=
  Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X)

noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Fintype X' := Fintype.ofEquiv X e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F

@[simps!]
def finYonedaIso'_components (X : FintypeCat.{u}) :
    F.obj ((toProfinite.{u}.op.obj ⟨X⟩)) ≅ (X → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  (isLimitFanMkObjOfIsLimit F _ _ (fintypeCatAsCofanOpIsLimit X)).conePointUniqueUpToIso
    (Types.productLimitCone.{u, u+1} fun _ ↦ F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)).2

def finYonedaIso' : toProfinite.op ⋙ F ≅ finYoneda F := by
  refine NatIso.ofComponents (fun X ↦ finYonedaIso'_components F X.unop) ?_
  intro X Y f
  ext
  simp only [finYoneda_obj, op_obj, comp_obj, Functor.comp_map, op_map, types_comp_apply,
    finYonedaIso'_components_hom]
  ext
  simp only [finYoneda_map, op_obj, Function.comp_apply]
  simp only [Types.productLimitCone, const_obj_obj, fintypeCatAsCofan, Cofan.mk_pt, cofan_mk_inj,
    Fan.mk_pt, Fan.mk_π_app]
  rw [← FunctorToTypes.map_comp_apply]
  congr

def isoCompToProfinite : toProfinite.op ⋙ F ≅ toProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  finYonedaIso' F ≪≫ (finYonedaIso F).symm

def isoLanDiscrete (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ lanPresheaf (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  (lanPresheaf_iso_functorToPresheaves F hF).symm ≪≫ lanPresheafIso (isoCompToProfinite F)

def isoDiscrete (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  isoLanDiscrete F hF ≪≫
    lanPresheaf_iso_functorToPresheaves' (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))

end Condensed

namespace LightCondensed

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite)

section LocallyConstantAsColimit

open Profinite.Extend

variable (X : Type u)

abbrev locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i) = fj.comap (c.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [comp_obj, op_obj, toProfinite_obj, functorToPresheaves_obj_obj, CompHausLike.coe_of,
      Functor.comp_map, op_map, Quiver.Hom.unop_op, functorToPresheaves_obj_map]
    apply DFunLike.ext
    intro x'
    obtain ⟨x, hx⟩ := ((LightProfinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x'
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

variable (S : LightProfinite)

noncomputable def isColimitLocallyConstantPresheafDiagramAux :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

example : (coconeRightOpOfCone S.asLimitCone) =
  Cocone.whisker (opOpEquivalence ℕ).inverse S.asLimitCone.op := rfl

noncomputable def isColimitLocallyConstantPresheafDiagram :
    IsColimit <| (locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone) :=
  (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence ℕ).inverse _).symm
    (isColimitLocallyConstantPresheafDiagramAux _ S)

end LocallyConstantAsColimit

section LanPresheaf

instance (S : LightProfinite.{u}ᵒᵖ)  :
    HasColimitsOfShape (CostructuredArrow toLightProfinite.op S) (Type u) := by
  let F : (CostructuredArrow (Skeleton.incl.op ⋙ toLightProfinite.op) S) ⥤
      CostructuredArrow toLightProfinite.op S :=
    CostructuredArrow.pre _ _ S
  have : F.IsEquivalence := inferInstanceAs (CostructuredArrow.pre _ _ S).IsEquivalence
  exact hasColimitsOfShape_of_equivalence (asEquivalence F)

@[simps!]
def lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

@[simps!]
def lanPresheafUnit (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    toLightProfinite.op ⋙ F ⟶ toLightProfinite.op ⋙ lanPresheaf F :=
  pointwiseLeftKanExtensionUnit _ _

instance (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    IsLeftKanExtension (lanPresheaf F) (lanPresheafUnit F) := by
  dsimp [lanPresheaf, lanPresheafUnit]
  infer_instance

variable {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
  (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G)

-- TODO: generalise and PR
def lanPresheafIso : lanPresheaf F ≅ lanPresheaf G where
  hom := descOfIsLeftKanExtension _ (lanPresheafUnit F) (lanPresheaf G) (i.hom ≫ lanPresheafUnit G)
  inv := descOfIsLeftKanExtension _ (lanPresheafUnit G) (lanPresheaf F) (i.inv ≫ lanPresheafUnit F)
  hom_inv_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf F) (α := lanPresheafUnit F)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)
      (G := lanPresheaf G) (β := i.hom ≫ lanPresheafUnit G), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)]
    simp
  inv_hom_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf G) (α := lanPresheafUnit G)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)
      (G := lanPresheaf F) (β := i.inv ≫ lanPresheafUnit F), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)]
    simp

end LanPresheaf

section ColimitLocallyConstant

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
  (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))

variable (S : LightProfinite.{u})

def functorToPresheaves_iso_colimit :
    colimit ((LightProfinite.Extend.functorOp S.asLimitCone) ⋙
      ((CostructuredArrow.proj toLightProfinite.op ⟨S⟩) ⋙ toLightProfinite.op ⋙ F)) ≅ F.obj ⟨S⟩ :=
  (colimit.isColimit _).coconePointUniqueUpToIso (hF S)

instance (S : LightProfinite) : Final <|
    LightProfinite.Extend.functorOp S.asLimitCone :=
  LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

def functorToPresheaves_iso_colimit_lan :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    functorToPresheaves_iso_colimit F hF S

@[simp]
lemma functorToPresheaves_iso_colimit_lan_hom : (functorToPresheaves_iso_colimit_lan F hF S).hom =
    colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp only [lanPresheaf_obj, functorToPresheaves_iso_colimit_lan, Final.colimitIso, Iso.trans_hom,
    Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, colimit.pre_desc]
  rfl

def lanPresheaf_iso_functorToPresheaves : lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (functorToPresheaves_iso_colimit_lan F hF S)) fun _ ↦ ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, pointwiseLeftKanExtension_map,
    functorToPresheaves_iso_colimit_lan_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ ↦ (by simp)

end ColimitLocallyConstant

def lanPresheaf_iso_functorToPresheaves' (X : Type u) :
    lanPresheaf (locallyConstantPresheaf X) ≅
    locallyConstantPresheaf X :=
  lanPresheaf_iso_functorToPresheaves
    (locallyConstantPresheaf X)
    fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

def lanLightCondSet (X : Type u) : LightCondSet.{u} where
  val := lanPresheaf (locallyConstantPresheaf X)
  cond := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheaf_iso_functorToPresheaves' X)]
    exact (Condensed.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ ↦ ((LightProfinite.effectiveEpi_iff_surjective _).mp)).obj X).cond

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) [p : PreservesFiniteProducts F]

open Opposite

@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)
  map f g := g ∘ f.unop

def finYonedaIso :
    toLightProfinite.op ⋙
      (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) ≅
    finYoneda F := by
  refine NatIso.ofComponents ?_ ?_
  · intro Y
    exact {
      hom := fun f ↦ f.toFun
      inv := fun f ↦ ⟨f, (by
        let _ : TopologicalSpace Y.unop := ⊥
        have : DiscreteTopology (toLightProfinite.obj Y.unop) :=
          inferInstanceAs (DiscreteTopology Y.unop)
        exact IsLocallyConstant.of_discrete _
        )⟩
      hom_inv_id := by aesop
      inv_hom_id := by aesop
    }
  · aesop

def mapOfElement {X : FintypeCat} (x : X) : FintypeCat.of (PUnit.{u+1}) ⟶ X := fun _ ↦ x

def fintypeCatAsCofan (X : FintypeCat) :
    Cofan (fun (_ : X) ↦ toLightProfinite.obj (of (PUnit.{u+1}))) :=
  Cofan.mk (toLightProfinite.obj X) (fun x ↦ toProfinite.map (mapOfElement x))

def fintypeCatAsCofanIsColimit (X : FintypeCat.{u}) :
    IsColimit (fintypeCatAsCofan X) := by
  refine mkCofanColimit _ (fun t ↦ ⟨fun x ↦ t.inj x PUnit.unit, continuous_bot⟩) (by aesop) ?_
  intro t m h
  ext x
  change m x = t.inj x _
  rw [← h x]
  rfl

def fintypeCatAsCofanOpIsLimit (X : FintypeCat.{u}) : IsLimit (fintypeCatAsCofan X).op :=
  Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X)

noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Fintype X' := Fintype.ofEquiv X e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F

@[simps!]
def finYonedaIso'_components (X : FintypeCat.{u}) :
    F.obj ((toLightProfinite.{u}.op.obj ⟨X⟩)) ≅
      (X → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  (isLimitFanMkObjOfIsLimit F _ _ (fintypeCatAsCofanOpIsLimit X)).conePointUniqueUpToIso
    (Types.productLimitCone.{u, u} fun _ ↦ F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)).2

def finYonedaIso' : toLightProfinite.op ⋙ F ≅ finYoneda F := by
  refine NatIso.ofComponents (fun X ↦ finYonedaIso'_components F X.unop) ?_
  intro X Y f
  ext
  simp only [finYoneda_obj, op_obj, comp_obj, Functor.comp_map, op_map, types_comp_apply,
    finYonedaIso'_components_hom]
  ext
  simp only [finYoneda_map, op_obj, Function.comp_apply]
  simp only [Types.productLimitCone, const_obj_obj, fintypeCatAsCofan, Cofan.mk_pt, cofan_mk_inj,
    Fan.mk_pt, Fan.mk_π_app]
  rw [← FunctorToTypes.map_comp_apply]
  congr

def isoCompToProfinite : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  finYonedaIso' F ≪≫ (finYonedaIso F).symm

def isoLanDiscrete (hF : ∀ S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ lanPresheaf (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  (lanPresheaf_iso_functorToPresheaves F hF).symm ≪≫ lanPresheafIso (isoCompToProfinite F)

def isoDiscrete (hF : ∀ S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  isoLanDiscrete F hF ≪≫
    lanPresheaf_iso_functorToPresheaves' (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))

end LightCondensed
