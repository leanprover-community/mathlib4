/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.SpectralSequence.EInt

/-!
# Truncations for a t-structure

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

noncomputable def eTruncLT : EInt ⥤ C ⥤ C where
  obj n := by
    induction n with
    | bot => exact 0
    | coe a => exact t.truncLT a
    | top => exact 𝟭 C
  map {x y} f := by
    induction x with
    | bot =>
      induction y with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x <;> induction y <;> induction z <;> cat_disch

@[simp]
lemma eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0 := rfl

@[simp]
lemma eTruncLT_obj_mk (n : ℤ) : t.eTruncLT.obj (EInt.mk n) = t.truncLT n := rfl

@[simp]
lemma eTruncLT_map_eq_truncLTι (n : ℤ) :
    t.eTruncLT.map (homOfLE (show EInt.mk n ≤ ⊤ by simp)) = t.truncLTι n := rfl

noncomputable def eTruncGE : EInt ⥤ C ⥤ C where
  obj n := by
    induction n with
    | bot => exact 𝟭 C
    | coe a => exact t.truncGE a
    | top => exact 0
  map {x y} f := by
    induction x with
    | bot =>
      induction y with
      | bot => exact 𝟙 _
      | coe b => exact t.truncGEπ b
      | top => exact 0
    | coe a =>
      induction y with
      | bot => exact 0
      | coe b => exact t.natTransTruncGEOfLE a b (by simpa using leOfHom f)
      | top => exact 0
    | top =>
      induction y with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x <;> induction y <;> induction z <;> cat_disch

@[simp]
lemma eTruncGE_obj_bot :
    t.eTruncGE.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma eTruncGE_obj_top :
    t.eTruncGE.obj ⊤ = 0 := rfl

@[simp]
lemma eTruncGE_obj_mk (n : ℤ) : t.eTruncGE.obj (EInt.mk n) = t.truncGE n := rfl

noncomputable def eTruncGEδLTt :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := by
    induction a with
    | bot => exact 0
    | coe a => exact t.truncGEδLT a
    | top => exact 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma eTruncGEδLTt_mk (n : ℤ) :
    t.eTruncGEδLTt.app (EInt.mk n) = t.truncGEδLT n := rfl

noncomputable abbrev eTruncLTι (i : EInt) : t.eTruncLT.obj i ⟶ 𝟭 _ :=
  t.eTruncLT.map (homOfLE (le_top))

instance : IsIso (t.eTruncLTι ⊤) := by
  dsimp [eTruncLTι]
  infer_instance

@[reassoc (attr := simp)]
lemma eTruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.map f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

noncomputable abbrev eTruncGEπ (i : EInt) : 𝟭 _ ⟶ t.eTruncGE.obj i :=
  t.eTruncGE.map (homOfLE (bot_le))

instance : IsIso (t.eTruncGEπ ⊥) := by
  dsimp [eTruncGEπ]
  infer_instance

@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGE_map_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.map f).app X = (t.eTruncGEπ j).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

@[simps!]
noncomputable def eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where
  obj i := Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLTt.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

lemma eTriangleLTGE_distinguished (i : EInt) (X : C) :
    (t.eTriangleLTGE.obj i).obj X ∈ distTriang _ := by
  induction i with
  | bot =>
    rw [Triangle.distinguished_iff_of_isZero₁ _ (Functor.zero_obj X)]
    dsimp
    infer_instance
  | coe n => exact t.triangleLTGE_distinguished n X
  | top =>
    rw [Triangle.distinguished_iff_of_isZero₃ _ (Functor.zero_obj X)]
    dsimp
    infer_instance

instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncLT.obj i).obj X) n := by
  induction i with
  | bot => exact isLE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ (by simp) _

end TStructure

end Triangulated

end CategoryTheory
