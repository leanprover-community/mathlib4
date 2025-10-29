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

universe u u' v v' w w'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section ShiftedHom

open DerivedCategory in
/-- The map between `ShiftedHom` induced by `F.mapDerivedCategory` where `F` is exact. -/
noncomputable def Functor.mapShiftedHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n :=
  fun f ↦ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    f.map F.mapDerivedCategory ≫ ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧'

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

/-- The commute of `CochainComplex.singleFunctor` with `F` and `F.mapDerivedCategory`. -/
noncomputable def Functor.mapCochainComplexSingleFunctor (n : ℤ) :
    (CochainComplex.singleFunctor C n) ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F ⋙ (CochainComplex.singleFunctor D n) :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n

#check LocalizerMorphism.smallShiftedHomMap

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

lemma Functor.mapExt_zero [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n 0 = 0 := by
  --simp [mapExt]
  --#check SmallShiftedHom.mk
  sorry

lemma Functor.mapExt_add [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) (f g : Ext.{w} X Y n) :
    F.mapExt X Y n (f + g) = F.mapExt X Y n f + F.mapExt X Y n g := by
  --simp [mapExt]
  --#check SmallShiftedHom.mk
  sorry

/-- The additive homomorphism between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun := F.mapExt X Y n
  map_zero' := F.mapExt_zero X Y n
  map_add' := F.mapExt_add X Y n

@[simp]
lemma Functor.mapExtAddHom_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = F.mapExt X Y n := rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

lemma Functor.mapExtAddHom_linear [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (r : R) (f : Ext.{w} X Y n) : F.mapExtAddHom X Y n (r • f) = r • (F.mapExtAddHom X Y n f) := by
  sorry

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
    (hS : S.ShortExact) : F.mapExt S.X₃ S.X₁ 1 hS.extClass = (hS.map_of_exact F).extClass :=
  sorry

end Abelian.Ext

end Ext

end CategoryTheory
