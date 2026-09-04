/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Map between Ext groups induced by an exact functor

In this file, we define the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

# Main Definition and results

* `CategoryTheory.Abelian.Ext.mapExactFunctor` : The map between `Ext` induced by
  `CategoryTheory.LocalizerMorphism.smallShiftedHomMap`.

* `CategoryTheory.Functor.mapExtAddHom` : Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor`
  into an additive homomorphism.

* `CategoryTheory.Functor.mapExtLinearMap` : Upgrade of `F.mapExtAddHom` assuming `F` is linear.

* `Ext.mapExactFunctor_mk₀` : `Ext.mapExactFunctor` commutes with `Ext.mk₀`

* `Ext.mapExactFunctor_comp` : `Ext.mapExactFunctor` preserves `Ext.comp`

* `mapExactFunctor_extClass` :
  `Ext.mapExactFunctor` commutes with `ShortComplex.ShortExact.extClass`

* `id_mapExactFunctor`: the identity functor acts by the identity on `Ext` groups

* `comp_mapExactFunctor`: compatibility with the composition of two exact functors

* `mapExactFunctor_comp_mk₀_natTransApp`: compatibility with a natural
transformation between two exact functors

-/

@[expose] public section

universe t t' w w' w''

namespace CategoryTheory

open Limits Abelian

variable {C : Type*} [Category* C] [Abelian C]
variable {D : Type*} [Category* D] [Abelian D]
variable {E : Type*} [Category* E] [Abelian E]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section

open DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma DerivedCategory.map_triangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    dsimp% F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
      triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex _)) ≫
        (F.mapDerivedCategoryFactors.inv.app S.X₁)⟦1⟧' ≫
          (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S))), ← Functor.map_comp,
    descShortComplex_triangleOfSESδ, F.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex,
    Functor.map_comp_assoc, descShortComplex_triangleOfSESδ_assoc]
  dsimp
  rw  [← Functor.map_comp_assoc]
  rw [← CochainComplex.mappingCone.map_δ, Functor.map_comp_assoc,
    ← F.mapDerivedCategoryFactors_hom_naturality_assoc, Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ'
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
      ShiftedHom.map hS.singleδ F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦1⟧' =
    (hS.map_of_exact F).singleδ := by
  dsimp [ShiftedHom.map, ShortComplex.ShortExact.singleδ]
  simp only [Category.assoc, DerivedCategory.map_triangleOfSESδ]
  generalize_proofs _ _ _ _ _ _ h1 _ _ h2
  dsimp
  rw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
    dsimp% triangleOfSESδ_naturality h1 h2
      (S.mapNatTrans (F.mapCochainComplexSingleFunctor 0).hom),
    ← Functor.map_comp_assoc]
  simp

@[reassoc]
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ShiftedHom.map hS.singleδ F.mapDerivedCategory =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (hS.map_of_exact F).singleδ ≫ ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₁)⟦1⟧' := by
  simp [← hS.mapShiftedHom_singleδ'_assoc, ← Functor.map_comp]

end

section Ext

open Localization

instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    ((F ⋙ CochainComplex.singleFunctor D 0).obj X)
    ((F ⋙ CochainComplex.singleFunctor D 0).obj Y) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `LocalizerMorphism.smallShiftedHomMap`. -/
noncomputable def Abelian.Ext.mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ}
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

set_option backward.isDefEq.respectTransparency false in
lemma Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this, ← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · simp [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  · simp [← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]

section

attribute [local simp] Abelian.Ext.mapExactFunctor_hom
attribute [local instance] HasDerivedCategory.standard

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

@[simp]
lemma Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F = 0 := by
  aesop

@[simp]
lemma Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

/-- Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor` into an additive homomorphism. -/
noncomputable def Functor.mapExtAddHom (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun e := e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]
lemma Functor.mapExtAddHom_coe : ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F := rfl

lemma Functor.mapExtAddHom_apply (e : Ext X Y n) : F.mapExtAddHom X Y n e = e.mapExactFunctor F :=
  rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

@[simp]
lemma Functor.mapExactFunctor_smul (r : R) (f : Ext.{w} X Y n) :
    (r • f).mapExactFunctor F = r • (f.mapExactFunctor F) := by
  aesop

/-- Upgrade of `F.mapExtAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapExtLinearMap (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]
lemma Functor.mapExtLinearMap_toAddMonoidHom : F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n :=
  rfl

lemma Functor.mapExtLinearMap_coe : ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F := rfl

lemma Functor.mapExtLinearMap_apply (e : Ext X Y n) :
    F.mapExtLinearMap R X Y n e = e.mapExactFunctor F := rfl

end

namespace Abelian.Ext

lemma mapExactFunctor_mk₀ [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    (mk₀ f).mapExactFunctor F = mk₀ (F.map f) := by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using! NatIso.naturality_1 _ f

lemma mapExactFunctor₀ [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    Ext.mapExactFunctor F (X := X) (Y := Y) = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]

lemma mapExactFunctor_comp [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).mapExactFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : ℤ) by grind)

attribute [local instance] HasDerivedCategory.standard in
lemma mapExactFunctor_extClass [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).extClass := by
  ext
  rw [Ext.mapExactFunctor_hom, hS.extClass_hom]
  exact (hS.mapShiftedHom_singleδ' F).trans (hS.map_of_exact F).extClass_hom.symm

open CategoryTheory.Functor in
attribute [local instance] HasDerivedCategory.standard in
@[simp]
lemma id_mapExactFunctor [HasExt.{w} C] {X Y : C} {n : ℕ}
    (α : Ext X Y n) :
    α.mapExactFunctor (𝟭 C) = α := by
  ext
  rw [mapExactFunctor_hom, ← α.hom.map_naturality_2 (Functor.mapDerivedCategoryIdIso C)]
  simp [ShiftedHom.id_map, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    mapDerivedCategoryIdIso_hom_app_singleFunctor_obj, ← Functor.map_comp,
    mapDerivedCategoryIdIso_inv_app_singleFunctor_obj]

open CategoryTheory.Functor in
attribute [local instance] HasDerivedCategory.standard in
lemma comp_mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E] {X Y : C} {n : ℕ}
    (α : Ext X Y n) (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    α.mapExactFunctor (F ⋙ G) = (α.mapExactFunctor F).mapExactFunctor G := by
  ext
  simp only [mapExactFunctor_hom]
  rw [← α.hom.map_naturality_1 (Functor.mapDerivedCategoryCompIso F G), ShiftedHom.comp_map]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    ShiftedHom.map, Functor.map_comp, Category.assoc]
  simp [mapDerivedCategorySingleFunctor_inv_app_comp_mapDerivedCategoryCompIso_inv_app_assoc,
    commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app]

attribute [local instance] HasDerivedCategory.standard in
lemma mapExactFunctor_comp_mk₀_natTransApp
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ}
    (α : Ext X Y n) {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G) :
    (α.mapExactFunctor F).comp (Ext.mk₀ (τ.app Y)) (add_zero n) =
      ((Ext.mk₀ (τ.app X))).comp (α.mapExactFunctor G) (zero_add n) := by
  ext
  have := ShiftedHom.map_naturality α.hom (NatTrans.mapDerivedCategory τ)
  simp [← cancel_mono (((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧'),
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    NatTrans.mapDerivedCategory_app_singleFunctor_obj,
    ← Functor.map_comp] at this
  simp [mapExactFunctor_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    ← Functor.map_comp, this]

end Abelian.Ext

end Ext

end CategoryTheory
