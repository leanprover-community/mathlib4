/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Ext-modules in linear categories

In this file, we show that if `C` is a `R`-linear abelian category,
then there is a `R`-module structure on the groups `Ext X Y n`
for `X` and `Y` in `C` and `n : ℕ`.

-/

universe w' w t v u

namespace CategoryTheory

namespace Abelian


namespace Ext

section Ring

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

noncomputable instance : Module R (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  Equiv.module R homEquiv

lemma smul_eq_comp_mk₀ (x : Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  letI := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
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
  letI := HasDerivedCategory.standard C
  aesop

@[simp]
lemma smul_comp {X Y Z : C} {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  letI := HasDerivedCategory.standard C
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

end Ring

section CommRing

variable (R : Type t) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C] (X Y Z : C)

/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
noncomputable def bilinearCompOfLinear (a b c : ℕ) (h : a + b = c) :
    Ext X Y a →ₗ[R] Ext Y Z b →ₗ[R] Ext X Z c where
  toFun α :=
    { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

end CommRing

end Ext

end Abelian

end CategoryTheory
