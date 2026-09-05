/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Ext-modules in linear categories

In this file, we show that if `C` is an `R`-linear abelian category,
then there is an `R`-module structure on the groups `Ext X Y n`
for `X` and `Y` in `C` and `n : ℕ`.

-/

@[expose] public section

universe w' w t v u

namespace CategoryTheory

namespace Abelian

namespace Ext

section End

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {A G : C} {n : ℕ}

noncomputable instance smulEndRight : SMul (End G) (Ext A G n) where
  smul r x := x.comp (mk₀ r) (add_zero n)

lemma smul_end_def (r : End G) (x : Ext A G n) : r • x = x.comp (mk₀ r) (add_zero n) := rfl

noncomputable instance moduleEndRight : Module (End G) (Ext A G n) where
  one_smul x := by simp [smul_end_def, End.one_def]
  mul_smul r s x := by
    simp only [smul_end_def]
    rw [End.mul_def, ← mk₀_comp_mk₀, comp_assoc_of_third_deg_zero]
  smul_zero r := by simp [smul_end_def]
  zero_smul x := by
    simp only [smul_end_def]
    rw [show (0 : End G) = (0 : G ⟶ G) from rfl, mk₀_zero, comp_zero]
  smul_add r x y := by simp [smul_end_def]
  add_smul r s x := by
    simp only [smul_end_def]
    rw [show mk₀ (r + s) = mk₀ r + mk₀ s from mk₀_add r s, comp_add]

lemma smul_comp_mk₀_of_comm {G' : C} (φ : G ⟶ G') (α : End G) (β : End G')
    (h : α ≫ φ = φ ≫ β) (x : Ext A G n) :
    (α • x).comp (mk₀ φ) (add_zero n) = β • x.comp (mk₀ φ) (add_zero n) := by
  simp only [smul_end_def, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, h]

end End

section Ring

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

noncomputable instance : Module R (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  homAddEquiv.module R

lemma smul_eq_comp_mk₀ (x : Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  let := HasDerivedCategory.standard C
  ext
  apply ((homAddEquiv.linearEquiv R).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom, mk₀_hom, Functor.map_smul, Functor.map_id, ShiftedHom.mk₀_smul,
    ShiftedHom.comp_smul, ShiftedHom.comp_mk₀_id]

@[simp]
lemma smul_hom (x : Ext X Y n) (r : R) [HasDerivedCategory C] :
    (r • x).hom = r • x.hom := by
  simp [smul_eq_comp_mk₀]

@[simp]
lemma comp_smul {X Y Z : C} {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    α.comp (r • β) h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

@[simp]
lemma smul_comp {X Y Z : C} {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

open DerivedCategory in
/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the `R`-linear
equivalence between `Ext.{w} X Y n` and a type of morphisms in the derived category
of the `R`-linear abelian category `C`. -/
@[simps]
noncomputable def homLinearEquiv [HasDerivedCategory.{w'} C] :
    Ext X Y n ≃ₗ[R]
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  __ := homAddEquiv
  map_smul' := by simp

lemma mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ (r • f) = r • mk₀ f := by
  let := HasDerivedCategory.standard C
  aesop

/-- The linear equivalence `Ext X Y 0 ≃ₜ[R] (X ⟶ Y)`. -/
@[simps! symm_apply]
noncomputable def linearEquiv₀ :
    Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  toAddEquiv := addEquiv₀
  map_smul' m x := homEquiv₀.symm.injective (by simp [mk₀_smul])

@[simp]
lemma mk₀_linearEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (linearEquiv₀ (R := R) f) = f :=
  addEquiv₀.left_inv f

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

noncomputable instance {R : Type t} [CommRing R] [Linear R C] {X Y : C} {n : ℕ} :
    IsScalarTower R (End Y) (Ext X Y n) where
  smul_assoc r s x := by rw [smul_end_def, smul_end_def, mk₀_smul, comp_smul]

/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
noncomputable def bilinearCompOfLinear (R : Type t) [CommRing R] [Linear R C] (X Y Z : C)
    (a b c : ℕ) (h : a + b = c) :
    Ext X Y a →ₗ[R] Ext Y Z b →ₗ[R] Ext X Z c where
  toFun α :=
    { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

/-- The postcomposition `Ext X Y a →ₗ[R] Ext X Z b` with `β : Ext Y Z n` when `a + n = b`. -/
noncomputable abbrev postcompOfLinear {Y Z : C} {n : ℕ} (β : Ext Y Z n)
    (R : Type t) [CommRing R] [Linear R C] (X : C) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →ₗ[R] Ext X Z b :=
  (bilinearCompOfLinear R X Y Z a n b h).flip β

/-- The precomposition `Ext Y Z a →ₗ[R] Ext X Z b` with `α : Ext X Y n` when `n + a = b`. -/
noncomputable abbrev precompOfLinear {X Y : C} {n : ℕ} (α : Ext X Y n)
    (R : Type t) [CommRing R] [Linear R C] (Z : C) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →ₗ[R] Ext X Z b :=
  bilinearCompOfLinear R X Y Z n a b h α

end CommRing

end Ext

end Abelian

end CategoryTheory
