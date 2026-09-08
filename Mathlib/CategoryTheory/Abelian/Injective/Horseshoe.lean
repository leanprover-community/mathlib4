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

open Limits CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace InjectiveResolution

/-- Given a short exact sequence `S : ShortComplex` in an abelian category,
this is the data of a horseshoe diagram involving injective resolutions of
`S.X₁`, `S.X₂`, `S.X₃`. -/
structure Horseshoe {S : ShortComplex C} (hS : S.ShortExact)
    (R₁ : InjectiveResolution S.X₁) (R₂ : InjectiveResolution S.X₂)
    (R₃ : InjectiveResolution S.X₃) where
  /-- A morphism between the injective resolutions `R₁` and `R₂` which extends `S.f`. -/
  f : Hom R₁ R₂ S.f
  /-- A morphism between the injective resolutions `R₂` and `R₃` which extends `S.g`. -/
  g : Hom R₂ R₃ S.g
  w_f (n : ℕ) : f.hom.f n ≫ g.hom.f n = 0 := by cat_disch
  /-- A degreewise splitting of the short exact sequence of complexes
  `0 ⟶ R₁.cocomplex ⟶ R₂.cocomplex ⟶ R₃.cocomplex ⟶ 0`. -/
  splitting (n : ℕ) : (ShortComplex.mk _ _ (w_f n)).Splitting

namespace Horseshoe

variable {S : ShortComplex C} {hS : S.ShortExact}
  {R₁ : InjectiveResolution S.X₁} {R₂ : InjectiveResolution S.X₂}
  {R₃ : InjectiveResolution S.X₃} (h : Horseshoe hS R₁ R₂ R₃)

attribute [reassoc (attr := simp)] w_f

@[reassoc (attr := simp)]
lemma w : h.f.hom ≫ h.g.hom = 0 := by cat_disch

/-- The short exact sequence of cochain complexes
`0 ⟶ R₁.cocomplex ⟶ R₂.cocomplex ⟶ R₃.cocomplex ⟶ 0` of a horseshoe diagram. -/
def shortComplex : ShortComplex (CochainComplex C ℕ) := .mk _ _ h.w

lemma shortExact_shortComplex : h.shortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦ (h.splitting n).shortExact)

lemma extMk_comp_extClass'_aux
    {X : C} {n : ℕ} (x₃ : X ⟶ R₃.cocomplex.X n) {m : ℕ}
    (hx₃ : x₃ ≫ R₃.cocomplex.d n m = 0) (m' : ℕ) :
    (x₃ ≫ (h.splitting n).s ≫ R₂.cocomplex.d n m ≫ (h.splitting m).r) ≫
      R₁.cocomplex.d m m' = 0 := by
  have := (h.splitting m').shortExact.mono_f
  let x₂ := x₃ ≫ (h.splitting n).s
  let x₁ := x₂ ≫ R₂.cocomplex.d n m ≫ (h.splitting m).r
  have hx₂ : x₂ ≫ h.g.hom.f n = x₃ := by simp [x₂, (h.splitting n).s_g]
  have hx₁ : x₁ ≫ h.f.hom.f m = x₂ ≫ R₂.cocomplex.d n m := by
    dsimp [x₁]
    simp [(h.splitting m).r_f, ← HomologicalComplex.Hom.comm_assoc, reassoc_of% hx₂,
      reassoc_of% hx₃]
  have : x₁ ≫ R₁.cocomplex.d m m' = 0 := by
    simp [← cancel_mono (h.f.hom.f m'), ← HomologicalComplex.Hom.comm, reassoc_of% hx₁]
  simpa [x₁, x₂] using this

@[implicit_reducible, simps]
noncomputable def shortComplexExtend : ShortComplex (CochainComplex C ℤ) where
  X₁ := R₁.cochainComplex
  X₂ := R₂.cochainComplex
  X₃ := R₃.cochainComplex
  f := HomologicalComplex.extendMap h.f.hom _
  g := HomologicalComplex.extendMap h.g.hom _
  zero := by
    dsimp [cochainComplex]
    rw [← HomologicalComplex.extendMap_comp, w, HomologicalComplex.extendMap_zero]
    rfl

lemma shortExact_shortComplexExtend :
    h.shortComplexExtend.ShortExact := by
  have : PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor C) := sorry
  have : PreservesFiniteColimits (ComplexShape.embeddingUpNat.extendFunctor C):= sorry
  exact h.shortExact_shortComplex.map_of_exact (ComplexShape.embeddingUpNat.extendFunctor C)

/- TODO, relate these three triangles:

variable [HasDerivedCategory C]
have T₁ := DerivedCategory.triangleOfSES h.shortExact_shortComplexExtend
have T₂ := DerivedCategory.Q.mapTriangle.obj
  (triangleOfDegreewiseSplit h.shortComplexExtend sorry)
have T₃ := ShortComplex.ShortExact.singleTriangle hS

-/

lemma extMk_comp_extClass'
    [HasExt.{w} C] {X : C} {n : ℕ} (x₃ : X ⟶ R₃.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hx₃ : x₃ ≫ R₃.cocomplex.d n m = 0) (m' : ℕ) (hm' : m + 1 = m') :
    -- hopefully, there will be no sign here
    (R₃.extMk x₃ m hm hx₃).comp hS.extClass hm =
    R₁.extMk (x₃ ≫ (h.splitting n).s ≫ R₂.cocomplex.d n m ≫ (h.splitting m).r) m' hm'
      (h.extMk_comp_extClass'_aux x₃ hx₃ m') := by
  sorry

lemma extMk_comp_extClass
    [HasExt.{w} C] {X : C} {n : ℕ} (x₃ : X ⟶ R₃.cocomplex.X n)
    (x₂ : X ⟶ R₂.cocomplex.X n) (hx₂ : x₂ ≫ h.g.hom.f n = x₃)
    (m : ℕ) (hm : n + 1 = m)
    (x₁ : X ⟶ R₁.cocomplex.X m) (hx₁ : x₁ ≫ h.f.hom.f m = x₂ ≫ R₂.cocomplex.d n m)
    (m' : ℕ) (hm' : m + 1 = m') :
    (R₃.extMk x₃ m hm (by simp [← hx₂, ← reassoc_of% hx₁])).comp hS.extClass hm =
    R₁.extMk x₁ m' hm' (by
      have := (h.splitting m').shortExact.mono_f
      simp [← cancel_mono (h.f.hom.f m'), ← HomologicalComplex.Hom.comm, reassoc_of% hx₁]) := by
  have hx₃ : x₃ ≫ R₃.cocomplex.d n m = 0 := by simp [← hx₂, ← reassoc_of% hx₁]
  rw [h.extMk_comp_extClass' x₃ m hm hx₃ m' hm',
    ← sub_eq_zero, sub_extMk, extMk_eq_zero_iff _ _ _ _ _ _ hm]
  obtain ⟨u, rfl⟩ :
      ∃ (u : X ⟶ R₁.cocomplex.X n), x₂ = u ≫ h.f.hom.f n + x₃ ≫ (h.splitting n).s :=
    ⟨x₂ ≫ (h.splitting n).r, by simpa [← hx₂] using x₂ ≫= (h.splitting n).id.symm⟩
  refine ⟨-u, ?_⟩
  have := (h.splitting m).shortExact.mono_f
  simp [← cancel_mono (h.f.hom.f m),
    (h.splitting m).r_f, ← HomologicalComplex.Hom.comm_assoc, (h.splitting n).s_g_assoc,
    hx₁, reassoc_of% hx₃]

end Horseshoe

end InjectiveResolution

end CategoryTheory
