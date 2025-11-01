/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Induced map between Ext

-/

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The commute of `CochainComplex.singleFunctor` with `F` and `F.mapDerivedCategory`. -/
noncomputable def Functor.mapCochainComplexSingleFunctor (n : ℤ) :
    (CochainComplex.singleFunctor C n) ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F ⋙ (CochainComplex.singleFunctor D n) :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n

section ShiftedHom

open DerivedCategory in
/-- The map between `ShiftedHom` induced by `F.mapDerivedCategory` where `F` is exact. -/
noncomputable def Functor.mapShiftedHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n :=
  fun f ↦ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    f.map F.mapDerivedCategory ≫ ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧'

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

instance {ι : Type*} (c : ComplexShape ι) :
    PreservesFiniteLimits (F.mapHomologicalComplex c) where
  preservesFiniteLimits := sorry

instance {ι : Type*} (c : ComplexShape ι) :
    PreservesFiniteColimits (F.mapHomologicalComplex c) where
  preservesFiniteColimits := sorry

open DerivedCategory

lemma Functor.mapTriangleOfSES {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
    ((shiftFunctor (DerivedCategory D) (1 : ℤ)).map (F.mapDerivedCategoryFactors.inv.app S.X₁)) ≫
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁)) := by
  change F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
    ((shiftFunctor (DerivedCategory D) (1 : ℤ)).mapIso (F.mapDerivedCategoryFactors.app S.X₁)).inv ≫
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).app (Q.obj S.X₁)).inv
  rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv, Iso.eq_comp_inv]
  conv_lhs => simp only [comp_obj, ShortComplex.map_X₁, triangleOfSESδ,
    CochainComplex.mappingCone.triangle_obj₁, map_comp, map_inv, Iso.app_hom, Category.assoc,
    ← commShiftIso_comp_hom_app, mapIso_hom]
  rw [NatTrans.shift_app_comm]
  simp only [ShortComplex.map_X₁, triangleOfSESδ]
  rw [commShiftIso_comp_hom_app, IsIso.inv_comp_eq]
  simp only [← Category.assoc]
  change _ ≫ ((Q.commShiftIso (1 : ℤ)).app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    S.X₁)).hom = _ ≫ ((Q.commShiftIso (1 : ℤ)).app ((F.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj S.X₁)).hom
  rw [Iso.cancel_iso_hom_right]
  have eq1 : F.mapDerivedCategory.map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    F.mapDerivedCategoryFactors.hom.app S.X₃ = F.mapDerivedCategoryFactors.hom.app
    (CochainComplex.mappingCone S.f) ≫ Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (CochainComplex.mappingCone.descShortComplex S)) := by
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp
  have eq2 : F.mapDerivedCategory.map (Q.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
    F.mapDerivedCategoryFactors.hom.app ((shiftFunctor (CochainComplex C ℤ) 1).obj S.X₁) =
    F.mapDerivedCategoryFactors.hom.app (CochainComplex.mappingCone S.f) ≫ Q.map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (CochainComplex.mappingCone.triangle S.f).mor₃) := by
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp
  rw [eq1, eq2]
  simp only [Category.assoc]
  change (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone S.f)).hom ≫ _ =
    (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone S.f)).hom ≫ _
  rw [Iso.cancel_iso_hom_left, ← Q.map_comp, CochainComplex.mappingCone.map_δ, ← Category.assoc,
    Q.map_comp]
  congr 1
  rw [IsIso.eq_comp_inv, ← Q.map_comp]
  congr 1
  ext n
  simp [CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.descShortComplex,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    mapHomologicalComplex_map_f, CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl]

omit [HasDerivedCategory.{t} C] in
lemma CochainComplex.mappingCone.descShortComplex_hom {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (f : S₁ ⟶ S₂) : CochainComplex.mappingCone.descShortComplex S₁ ≫ f.τ₃ =
    CochainComplex.mappingCone.map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫
    CochainComplex.mappingCone.descShortComplex S₂ := by
  ext n
  simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.descShortComplex]
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  · simp
  · have : (S₁.g ≫ f.τ₃).f n = (f.τ₂ ≫ S₂.g).f n := by rw [f.comm₂₃]
    simpa

omit [HasDerivedCategory.{t} C] in
lemma CochainComplex.mappingCone.triangle_mor₃_hom {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : f ≫ b = a ≫ g) :
    (CochainComplex.mappingCone.triangle f).mor₃ ≫ (shiftFunctor (CochainComplex C ℤ) 1).map a =
    CochainComplex.mappingCone.map f g a b comm ≫ (CochainComplex.mappingCone.triangle g).mor₃ := by
  ext n
  simp [CochainComplex.mappingCone.map]
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  · simp
  · simp

lemma triangleOfSESδ_hom {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) : (triangleOfSESδ hS₁) ≫ ((shiftFunctor
    (DerivedCategory C) (1 : ℤ)).map (Q.map f.τ₁)) = (Q.map f.τ₃) ≫ triangleOfSESδ hS₂ := by
  simp only [triangleOfSESδ, CochainComplex.mappingCone.triangle_obj₁, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map, ← (Q.commShiftIso (1 : ℤ)).hom.naturality, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, ← Category.assoc]
  change _ ≫ ((Q.commShiftIso 1).app S₂.X₁).hom = _ ≫ ((Q.commShiftIso 1).app S₂.X₁).hom
  rw [Iso.cancel_iso_hom_right, ← Q.map_comp]
  let g := CochainComplex.mappingCone.map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm
  simp only [Functor.comp_obj, Functor.comp_map, CochainComplex.mappingCone.descShortComplex_hom f,
    Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Q.map_comp, ← Q.map_comp, CochainComplex.mappingCone.triangle_mor₃_hom]

lemma Functor.mapShiftedHom_singleδ {S : ShortComplex C} (hS : S.ShortExact) :
    (F.mapShiftedHom S.X₃ S.X₁ 1) hS.singleδ = (hS.map_of_exact F).singleδ := by
  simp only [mapShiftedHom, comp_obj, ShiftedHom.map, ShortComplex.ShortExact.singleδ,
    SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor, mapIso_hom,
    SingleFunctors.evaluation_map, ShortComplex.map_X₁, mapIso_inv, map_comp, Category.assoc,
    commShiftIso_hom_naturality, ShortComplex.map_X₃]
  rw [F.mapTriangleOfSES]
  simp only [ShortComplex.map_X₃, comp_obj, ShortComplex.map_X₁, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [singleFunctorsPostcompQIso_hom_hom, NatTrans.id_app, map_id,
    singleFunctorsPostcompQIso_inv_hom, SingleFunctors.postcomp_functor, comp_obj, Category.id_comp]
  erw [map_id, map_id, map_id]
  simp only [Category.id_comp, Category.comp_id]
  have eq1 : (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
    F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
    S.X₃) = Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app S.X₃) := by
    simp only [comp_obj, mapDerivedCategorySingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X', singleFunctorIsoCompQ,
      isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_inv,
      Iso.refl_inv, Category.id_comp, isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
      isoWhiskerLeft_inv, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
      associator_hom_app, whiskerLeft_app, Category.comp_id, Iso.inv_hom_id_app]
    exact Category.id_comp _
  have eq2 : (F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C (ComplexShape.up ℤ)
    0).obj S.X₁) ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁) =
    Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app S.X₁) := by
    simp only [comp_obj, mapDerivedCategorySingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X', singleFunctorIsoCompQ,
      isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
      associator_hom_app, whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app,
      Category.id_comp]
    erw [Category.id_comp]
    simp only [Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  rw [← (shiftFunctor (DerivedCategory D) 1).map_comp, eq2, ← Category.assoc, eq1]
  generalize_proofs _ _ _ _ _ _ _ h1 _ h2
  let f : ((S.map (CochainComplex.singleFunctor C 0)).map (F.mapHomologicalComplex
    (ComplexShape.up ℤ))) ⟶ (S.map F).map (CochainComplex.singleFunctor D 0) := {
    τ₁ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₁
    τ₂ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₂
    τ₃ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₃
    comm₁₂ := (NatTrans.naturality _ S.f).symm
    comm₂₃ := (NatTrans.naturality _ S.g).symm }
  change _ ≫ triangleOfSESδ h1 ≫ (shiftFunctor (DerivedCategory D) 1).map (Q.map f.τ₁) = _
  rw [triangleOfSESδ_hom h1 h2 f]
  change Q.map ((F.mapCochainComplexSingleFunctor 0).app S.X₃).inv ≫
    Q.map ((F.mapCochainComplexSingleFunctor 0).app S.X₃).hom ≫ _ = _
  rw [← Category.assoc, ← Q.map_comp]
  simp

end

lemma Functor.mapShiftedHom_zero [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (X Y : C) (n : ℤ) : F.mapShiftedHom X Y n 0 = 0 := by simp [mapShiftedHom, ShiftedHom.map]

open DerivedCategory in
lemma Functor.mapShiftedHom_add [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C)
    (n : ℤ) (x y : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n) :
    F.mapShiftedHom X Y n (x + y) = F.mapShiftedHom X Y n x + F.mapShiftedHom X Y n y := by
  rw [mapShiftedHom, ShiftedHom.map, F.mapDerivedCategory.map_add]
  simp [mapShiftedHom, ShiftedHom.map]

open DerivedCategory in
/-- The additive homomorphism between `ShiftedHom` induced by
`F.mapDerivedCategory` where `F` is exact. -/
noncomputable def Functor.mapShiftedHomAddHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →+
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n := {
  toFun := F.mapShiftedHom X Y n
  map_zero' := F.mapShiftedHom_zero ..
  map_add' _ _ := F.mapShiftedHom_add .. }

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

instance [F.Linear R] : Functor.Linear R (F.mapHomotopyCategory (ComplexShape.up ℤ)) where
  map_smul {X Y} f r:= by
    dsimp only [Functor.mapHomotopyCategory]
    have full : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).Full := Quotient.full_functor _
    rcases full.1 f with ⟨g, hg⟩
    rw [← hg, ← Functor.Linear.map_smul]
    simp only [HomotopyCategory.quotient, Quotient.lift_map_functor_map, Functor.comp_map,
      Functor.map_smul]
    rfl

instance [F.Linear R] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] :
    F.mapDerivedCategory.Linear R := by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) R
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).comp DerivedCategory.Qh)
    F.mapDerivedCategory]
  infer_instance

open DerivedCategory in
lemma Functor.mapShiftedHomAddHom_linear [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (X Y : C) (n : ℤ) (r : R)
    (x : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)) :
    (F.mapShiftedHomAddHom X Y n) (r • x) = r • ((F.mapShiftedHomAddHom X Y n) x)  := by
  simp only [mapShiftedHomAddHom, mapShiftedHom, comp_obj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Linear.comp_smul, ← Linear.smul_comp]
  congr
  simp [ShiftedHom.map, F.mapDerivedCategory.map_smul]

open DerivedCategory in
/-- Upgrade of `F.mapShiftedHomAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapShiftedHomLinearMap
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →ₗ[R]
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n where
  __ := F.mapShiftedHomAddHom X Y n
  map_smul' := F.mapShiftedHomAddHom_linear R X Y n

end ShiftedHom

section Ext

open Localization

instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    (((F ⋙ CochainComplex.singleFunctor D 0).obj X))
    (((F ⋙ CochainComplex.singleFunctor D 0).obj Y)) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExt [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExt_eq_mapShiftedHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n = Ext.homEquiv.symm ∘ F.mapShiftedHom X Y n ∘ Ext.homEquiv := by
  apply funext
  intro f
  apply Ext.homEquiv.injective
  simp only [mapExt, comp_obj, Function.comp_apply, mapShiftedHom, Equiv.apply_symm_apply]
  simp only [Ext.homEquiv]
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  let _ : NatTrans.CommShift F.mapDerivedCategoryFactors.symm.hom ℤ :=
    NatTrans.CommShift.of_iso_inv F.mapDerivedCategoryFactors ℤ
  apply Eq.trans ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).equiv_smallShiftedHomMap
    DerivedCategory.Q DerivedCategory.Q
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    F.mapDerivedCategory F.mapDerivedCategoryFactors.symm f)
  simp only [comp_obj, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom]
  congr 2
  · simp only [mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
      Iso.refl_trans, Iso.trans_inv, Iso.refl_inv, Category.id_comp, isoWhiskerRight_inv,
      Iso.symm_inv, Category.assoc, isoWhiskerLeft_inv, NatTrans.comp_app, comp_obj, Iso.refl_symm,
      associator_inv_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, Category.comp_id]
    exact (Category.id_comp _).symm
  · congr 1
    simp only [mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
      Iso.refl_symm, Iso.refl_trans, Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, comp_obj, associator_hom_app,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app, Category.id_comp]
    nth_rw 2 [← Category.assoc]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

lemma Functor.mapExt_eq_mapShiftedHom' [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n = (Ext.homAddEquiv.symm.toAddMonoidHom.comp
      (F.mapShiftedHomAddHom X Y n)).comp Ext.homAddEquiv.toAddMonoidHom :=
  F.mapExt_eq_mapShiftedHom X Y n

end

lemma Functor.mapExt_zero [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n 0 = 0 := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExt_eq_mapShiftedHom']

lemma Functor.mapExt_add [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) (f g : Ext.{w} X Y n) :
    F.mapExt X Y n (f + g) = F.mapExt X Y n f + F.mapExt X Y n g := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExt_eq_mapShiftedHom']

/-- The additive homomorphism between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun := F.mapExt X Y n
  map_zero' := F.mapExt_zero X Y n
  map_add' := F.mapExt_add X Y n

@[simp]
lemma Functor.mapExtAddHom_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = F.mapExt X Y n := rfl

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtAddHom_eq_mapShiftedHomAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = (Ext.homAddEquiv.symm.toAddMonoidHom.comp
      (F.mapShiftedHomAddHom X Y n)).comp Ext.homAddEquiv.toAddMonoidHom :=
  AddMonoidHom.ext (fun _ ↦ congr_fun (F.mapExt_eq_mapShiftedHom X Y n) _)

end

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtAddHom_eq_mapShiftedHomAddHom' [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
    (n : ℕ) : F.mapExtAddHom X Y n = (Ext.homLinearEquiv.symm.toLinearMap.comp
    (F.mapShiftedHomLinearMap R X Y n)).comp Ext.homLinearEquiv.toLinearMap :=
  F.mapExtAddHom_eq_mapShiftedHomAddHom X Y n

end

lemma Functor.mapExtAddHom_linear [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (r : R) (f : Ext.{w} X Y n) : F.mapExtAddHom X Y n (r • f) = r • (F.mapExtAddHom X Y n f) := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExtAddHom_eq_mapShiftedHomAddHom' R]

/-- Upgrade of `F.mapExtAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapExtLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := F.mapExtAddHom_linear R X Y n

@[simp]
lemma Functor.mapExtLinearMap_toAddMonoidHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n := rfl

lemma Functor.mapExtLinearMap_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExt X Y n := rfl

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtLinearMap_eq_mapShiftedHomLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
    (n : ℕ) : F.mapExtLinearMap R X Y n = (Ext.homLinearEquiv.symm.toLinearMap.comp
    (F.mapShiftedHomLinearMap R X Y n)).comp Ext.homLinearEquiv.toLinearMap :=
  LinearMap.ext (fun _ ↦ congr_fun (F.mapExt_eq_mapShiftedHom X Y n) _)

end

namespace Abelian.Ext

lemma mapExt_mk₀_eq_mk₀_map [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    F.mapExt X Y 0 (mk₀ f) = mk₀ (F.map f) := by
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  simp only [Functor.mapExt, Functor.comp_obj, Int.cast_ofNat_Int, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl ((CochainComplex.singleFunctor C 0).map f)]
  congr
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom]
  exact NatIso.naturality_1 _ f

lemma mapExt_comp_eq_comp_mapExt [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    F.mapExt X Z c (α.comp β h) = (F.mapExt X Y a α).comp (F.mapExt Y Z b β) h := by
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  simp [Functor.mapExt, comp]
  have h' : b + a = (c : ℤ) := by simp [← h, add_comm]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_comp
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    ((F.mapCochainComplexSingleFunctor 0).app Z) α β h']

lemma mapExt_extClass_eq_extClass_map [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : F.mapExt S.X₃ S.X₁ 1 hS.extClass = (hS.map_of_exact F).extClass := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  have : F.mapShiftedHom S.X₃ S.X₁ 1 hS.extClass.hom = (hS.map_of_exact F).extClass.hom := by
    rw [hS.extClass_hom, (hS.map_of_exact F).extClass_hom, F.mapShiftedHom_singleδ hS]
  simpa only [F.mapExt_eq_mapShiftedHom, Int.cast_ofNat_Int, Function.comp_apply,
    Equiv.symm_apply_eq]

end Abelian.Ext

end Ext

end CategoryTheory
