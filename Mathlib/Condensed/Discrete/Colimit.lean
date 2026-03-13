/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Equivalence
public import Mathlib.Topology.Category.LightProfinite.Extend

/-!

# The condensed set given by left Kan extension from `FintypeCat` to `Profinite`.

This file provides the necessary API to prove that a condensed set `X` is discrete if and only if
for every profinite set `S = limᵢSᵢ`, `X(S) ≅ colimᵢX(Sᵢ)`, and the analogous result for light
condensed sets.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Functor Limits FintypeCat CompHausLike.LocallyConstant

namespace Condensed

section LocallyConstantAsColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone <| F ⋙ toProfinite) (X : Type (u + 1))

/-- The presheaf on `Profinite` of locally constant functions to `X`. -/
abbrev locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

/--
The functor `locallyConstantPresheaf` takes cofiltered limits of finite sets with surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

@[simp]
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [∀ i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toProfinite).op ⋙ locallyConstantPresheaf X))
    (i : I) (f : LocallyConstant (toProfinite.obj (F.obj i)) X) :
    (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app i).hom.hom) =
      s.ι.app ⟨i⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨i⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]
  rfl

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : Profinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

@[simp]
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : Profinite)
    (s : Cocone (S.diagram.op ⋙ locallyConstantPresheaf X))
    (i : DiscreteQuotient S) (f : LocallyConstant (S.diagram.obj i) X) :
    (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app i).hom.hom) = s.ι.app ⟨i⟩ f :=
  isColimitLocallyConstantPresheaf_desc_apply S.asLimitCone X S.asLimit s i f

end LocallyConstantAsColimit

/--
Given a presheaf `F` on `Profinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
abbrev lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

/--
To presheaves on `Profinite` whose restrictions to finite sets are isomorphic have isomorphic left
Kan extensions.
-/
def lanPresheafExt {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafExt_hom {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafExt_inv {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.inv) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : Profinite.{u}} {F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}

instance : Final <| Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

/--
A presheaf, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheafIso hF).hom = colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `lanPresheafIso` is natural in `S`. -/
def lanPresheafNatIso (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    lanPresheaf F ≅ F :=
  NatIso.ofComponents (fun ⟨S⟩ ↦ (lanPresheafIso (hF S)))
    fun _ ↦ (by simpa using colimit.hom_ext fun _ ↦ (by simp))

@[simp]
lemma lanPresheafNatIso_hom_app (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
    (S : Profiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
`lanPresheaf (locallyConstantPresheaf X)` is a sheaf for the coherent topology on `Profinite`.
-/
def lanSheafProfinite (X : Type (u + 1)) :
    Sheaf (coherentTopology Profinite.{u}) Type (u + 1) where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u + 1}
      (hs := fun _ _ _ ↦ ((Profinite.effectiveEpi_tfae _).out 0 2).mp)).obj X).property

/-- `lanPresheaf (locallyConstantPresheaf X)` as a condensed set. -/
def lanCondensedSet (X : Type (u + 1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`Profinite`.
-/
@[simps obj map]
abbrev finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := (X.unop → F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩))
  map f := TypeCat.ofHom ⟨fun g ↦ g ∘ f.unop⟩

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
@[simps! hom_app]
def locallyConstantIsoFinYoneda :
    toProfinite.op ⋙ (locallyConstantPresheaf (F.obj (toProfinite.op.obj
      ⟨of <| PUnit.{u + 1}⟩))) ≅
    finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := TypeCat.ofHom ⟨fun f ↦ f.1⟩
    inv := TypeCat.ofHom ⟨fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩⟩ }

/-- A finite set as a coproduct cocone in `Profinite` over itself. -/
def fintypeCatAsCofan (X : Profinite) :
    Cofan (fun (_ : X) ↦ (Profinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x ↦ ConcreteCategory.ofHom (ContinuousMap.const _ x))

/-- A finite set is the coproduct of its points in `Profinite`. -/
def fintypeCatAsCofanIsColimit (X : Profinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  mkCofanColimit _ (fun t ↦ ConcreteCategory.ofHom ⟨fun x ↦ t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h ↦ by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]

noncomputable instance (X : Profinite) [Finite X] :
    PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := .of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
def isoFinYonedaComponents (X : Profinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X → F.obj ⟨Profinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u + 1} fun _ ↦ F.obj ⟨Profinite.of PUnit.{u + 1}⟩).2

@[simp]
lemma isoFinYonedaComponents_hom (X : Profinite.{u}) [Finite X] :
    (isoFinYonedaComponents F X).hom =
    TypeCat.ofHom ⟨fun y x ↦ F.map ((Profinite.of PUnit.{u + 1}).const x).op y⟩ :=
  rfl

lemma isoFinYonedaComponents_hom_apply (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X) :
    (isoFinYonedaComponents F X).hom y x =
      F.map ((Profinite.of PUnit.{u + 1}).const x).op y :=
  rfl

lemma isoFinYonedaComponents_inv_comp {X Y : Profinite.{u}} [Finite X] [Finite Y]
    (f : Y → F.obj ⟨Profinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_apply]

attribute [local simp] toProfinite_obj

set_option backward.isDefEq.respectTransparency false in
/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps!]
def isoFinYoneda : toProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents F (toProfinite.obj X.unop)) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.hom_as_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, Function.comp_apply, toProfinite_obj,
      ← Functor.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit
    (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

set_option backward.isDefEq.respectTransparency false in
lemma isoLocallyConstantOfIsColimit_inv (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts X]
    (hX : ∀ S : Profinite.{u}, (IsColimit <| X.mapCocone S.asLimitCone.op)) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u + 1} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u + 1} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  simp only [toProfinite_obj, TypeCat.hom_as_apply, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, counitApp_app]
  apply presheaf_ext.{u, u + 1} (X := X) (Y := X) (f := f)
  intro x
  erw? [incl_of_counitAppApp]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u + 1} f x) :=
    Finite.of_injective (sigmaIncl.{u, u + 1} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u + 1} f x)).hom
  ext y
  simp only [toProfinite_obj, isoFinYonedaComponents_hom, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.mk_apply, ← Functor.map_comp_apply]
  rw [show (Profinite.of PUnit.{u + 1}).const y ≫ IsTerminal.from _ (fiber f x) = 𝟙 _ from rfl]
  simp only [op_comp, FunctorToTypes.map_comp_apply, op_id, FunctorToTypes.map_id_apply]
  rw [← isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u + 1} f x)]
  simpa [← isoFinYonedaComponents_hom_apply] using x.map_eq_image f y

end Condensed

namespace LightCondensed

section LocallyConstantAsColimit

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite) (X : Type u)

/-- The presheaf on `LightProfinite` of locally constant functions to `X`. -/
abbrev locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

/--
The functor `locallyConstantPresheaf` takes sequential limits of finite sets with surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((LightProfinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

@[simp]
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [∀ i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toLightProfinite).op ⋙ locallyConstantPresheaf X))
    (n : ℕᵒᵖ) (f : LocallyConstant (toLightProfinite.obj (F.obj n)) X) :
    (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app n).hom.hom) =
      s.ι.app ⟨n⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨n⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : LightProfinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone) :=
  (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence ℕ).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

@[simp]
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : LightProfinite)
    (s : Cocone (S.diagram.rightOp ⋙ locallyConstantPresheaf X))
    (n : ℕ) (f : LocallyConstant (S.diagram.obj ⟨n⟩) X) :
    (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app ⟨n⟩).hom.hom) = s.ι.app n f := by
  change ((((locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)).ι.app n) ≫
    (isColimitLocallyConstantPresheafDiagram X S).desc s) _ = _
  rw [(isColimitLocallyConstantPresheafDiagram X S).fac]

end LocallyConstantAsColimit

instance (S : LightProfinite.{u}ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow toLightProfinite.op S) (Type u) :=
  hasColimitsOfShape_of_equivalence (asEquivalence (CostructuredArrow.pre Skeleton.incl.op _ S))

/--
Given a presheaf `F` on `LightProfinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
abbrev lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

/--
To presheaves on `LightProfinite` whose restrictions to finite sets are isomorphic have isomorphic
left Kan extensions.
-/
def lanPresheafExt {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafExt_hom {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.hom) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafExt_inv {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.inv) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : LightProfinite.{u}} {F : LightProfinite.{u}ᵒᵖ ⥤ Type u}

instance : Final <| LightProfinite.Extend.functorOp S.asLimitCone :=
  LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

/--
A presheaf, which takes a light profinite set written as a sequential limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheafIso hF).hom = colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `lanPresheafIso` is natural in `S`. -/
def lanPresheafNatIso
    (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (lanPresheafIso (hF S))) fun _ ↦ ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ ↦ (by simp)

@[simp]
lemma lanPresheafNatIso_hom_app
    (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
    (S : LightProfiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
`lanPresheaf (locallyConstantPresheaf X)` as a light condensed set.
-/
def lanLightCondSet (X : Type u) : LightCondSet.{u} where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ ↦ ((LightProfinite.effectiveEpi_iff_surjective _).mp)).obj X).property

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`LightProfinite`.
-/
@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)
  map f g := g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
def locallyConstantIsoFinYoneda : toLightProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) ≅ finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := fun f ↦ f.1
    inv := fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/-- A finite set as a coproduct cocone in `LightProfinite` over itself. -/
def fintypeCatAsCofan (X : LightProfinite) :
    Cofan (fun (_ : X) ↦ (LightProfinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x ↦ ConcreteCategory.ofHom (ContinuousMap.const _ x))

/-- A finite set is the coproduct of its points in `LightProfinite`. -/
def fintypeCatAsCofanIsColimit (X : LightProfinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  mkCofanColimit _ (fun t ↦ ConcreteCategory.ofHom ⟨fun x ↦ t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h ↦ by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]

noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := Finite.of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
def isoFinYonedaComponents (X : LightProfinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X → F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u} fun _ ↦ F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩).2

lemma isoFinYonedaComponents_hom_apply (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩)
    (x : X) : (isoFinYonedaComponents F X).hom y x =
      F.map ((LightProfinite.of PUnit.{u + 1}).const x).op y := rfl

lemma isoFinYonedaComponents_inv_comp {X Y : LightProfinite.{u}} [Finite X] [Finite Y]
    (f : Y → F.obj ⟨LightProfinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [CategoryTheory.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, CategoryTheory.inv_hom_id_apply, Function.comp_apply]

/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps!]
def isoFinYoneda : toLightProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents F (toLightProfinite.obj X.unop)) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [types_comp_apply, isoFinYonedaComponents_hom_apply, finYoneda_map, op_obj,
      Function.comp_apply,
      ← FunctorToTypes.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a light profinite set written as a sequential limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit (hF : ∀ S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

set_option backward.isDefEq.respectTransparency false in
lemma isoLocallyConstantOfIsColimit_inv (X : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts X] (hX : ∀ S : LightProfinite.{u}, (IsColimit <|
      X.mapCocone (coconeRightOpOfCone S.asLimitCone))) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  simp only [types_comp_apply, counitApp_app]
  apply presheaf_ext.{u, u} (X := X) (Y := X) (f := f)
  intro x
  rw [incl_of_counitAppApp]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u} f x) :=
    Finite.of_injective (sigmaIncl.{u, u} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u} f x)).hom
  ext y
  simp only [isoFinYonedaComponents_hom_apply, ← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [show (LightProfinite.of PUnit.{u + 1}).const y ≫ IsTerminal.from _ (fiber f x) = 𝟙 _ from rfl]
  simp only [op_comp, FunctorToTypes.map_comp_apply, op_id, FunctorToTypes.map_id_apply]
  rw [← isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u} f x)]
  simpa [← isoFinYonedaComponents_hom_apply] using x.map_eq_image f y

end LightCondensed
