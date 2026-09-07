/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Horseshoe

-/

universe w

@[expose] public section

namespace CategoryTheory

open CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace InjectiveResolution

structure Horseshoe {S : ShortComplex C} (hS : S.ShortExact)
    (R₁ : InjectiveResolution S.X₁) (R₂ : InjectiveResolution S.X₂)
    (R₃ : InjectiveResolution S.X₃) where
  f : R₁.cocomplex ⟶ R₂.cocomplex
  g : R₂.cocomplex ⟶ R₃.cocomplex
  w_f (n : ℕ) : f.f n ≫ g.f n = 0 := by cat_disch
  ι_f : R₁.ι ≫ f = (single₀ C).map S.f ≫ R₂.ι := by cat_disch
  ι_g : R₂.ι ≫ g = (single₀ C).map S.g ≫ R₃.ι := by cat_disch
  splitting (n : ℕ) : (ShortComplex.mk _ _ (w_f n)).Splitting

namespace Horseshoe

variable {S : ShortComplex C} {hS : S.ShortExact}
  {R₁ : InjectiveResolution S.X₁} {R₂ : InjectiveResolution S.X₂}
  {R₃ : InjectiveResolution S.X₃} (h : Horseshoe hS R₁ R₂ R₃)

attribute [reassoc (attr := simp)] w_f ι_f ι_g

@[reassoc (attr := simp)]
lemma w : h.f ≫ h.g = 0 := by cat_disch

@[reassoc (attr := simp)]
lemma ι_f_zero_comp :
    dsimp% R₁.ι.f 0 ≫ h.f.f 0 = S.f ≫ R₂.ι.f 0 := by
  simp [dsimp% (HomologicalComplex.eval _ _ 0).congr_map h.ι_f]

@[reassoc (attr := simp)]
lemma ι_g_zero_comp :
    dsimp% R₂.ι.f 0 ≫ h.g.f 0 = S.g ≫ R₃.ι.f 0 := by
  simp [dsimp% (HomologicalComplex.eval _ _ 0).congr_map h.ι_g]

def shortComplex : ShortComplex (CochainComplex C ℕ) := .mk _ _ h.w

lemma shortExact_shortComplex : h.shortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦ (h.splitting n).shortExact)

lemma extMk_comp_extClass
    [HasExt.{w} C] {X : C} {n : ℕ} (x₃ : X ⟶ R₃.cocomplex.X n)
    (x₂ : X ⟶ R₂.cocomplex.X n) (hx₂ : x₂ ≫ h.g.f n = x₃)
    (m : ℕ) (hm : n + 1 = m)
    (x₁ : X ⟶ R₁.cocomplex.X m) (hx₁ : x₁ ≫ h.f.f m = x₂ ≫ R₂.cocomplex.d n m)
    (m' : ℕ) (hm' : m + 1 = m') :
    (R₃.extMk x₃ m hm (by simp [← hx₂, ← reassoc_of% hx₁])).comp hS.extClass hm =
    -- in principle, there should be no sign here
    R₁.extMk x₁ m' hm' (by
      have := (h.splitting m').shortExact.mono_f
      simp [← cancel_mono (h.f.f m'), ← HomologicalComplex.Hom.comm, reassoc_of% hx₁]) := by
  sorry

end Horseshoe

end InjectiveResolution

end CategoryTheory
