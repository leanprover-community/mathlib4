/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The Ext class of a short exact sequence

In this file, given a short exact short complex `S : ShortComplex C`
in an abelian category, we construct the associated class in
`Ext S.X₃ S.X₁ 1`.

-/

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

open Abelian

namespace ShortComplex

variable (S : ShortComplex C)

lemma ext_mk₀_f_comp_ext_mk₀_g : (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0 := by simp

namespace ShortExact

variable {S}
variable (hS : S.ShortExact)

section

local notation "W" => HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
local notation "S'" => S.map (CochainComplex.singleFunctor C 0)
local notation "hS'" => hS.map_of_exact (HomologicalComplex.single _ _ _)
local notation "K" => CochainComplex.mappingCone (ShortComplex.f S')
local notation "qis" => CochainComplex.mappingCone.descShortComplex S'
local notation "hqis" => CochainComplex.mappingCone.quasiIso_descShortComplex hS'
local notation "δ" => Triangle.mor₃ (CochainComplex.mappingCone.triangle (ShortComplex.f S'))

instance : HasSmallLocalizedShiftedHom.{w} W ℤ (S').X₃ (S').X₁ := by
  dsimp
  infer_instance

include hS in
private lemma hasSmallLocalizedHom_S'_X₃_K :
    HasSmallLocalizedHom.{w} W (S').X₃ K := by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)

include hS in
private lemma hasSmallLocalizedShiftedHom_K_S'_X₁ :
    HasSmallLocalizedShiftedHom.{w} W ℤ K (S').X₁ := by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ qis hqis (S').X₁]
  infer_instance

/-- The class in `Ext S.X₃ S.X₁ 1` that is attached to a short exact
short complex `S` in an abelian category. -/
noncomputable def extClass : Ext.{w} S.X₃ S.X₁ 1 := by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : ℤ)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

@[simp]
lemma extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ := by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp, Iso.homToEquiv_apply]
  rw [SmallHom.equiv_mkInv, SmallHom.equiv_mk]
  dsimp [singleδ, triangleOfSESδ]
  rw [Category.assoc, Category.assoc, Category.assoc,
    singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_inv_hom,
    NatTrans.id_app, Category.id_comp, NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id, Category.comp_id]
  rfl

end

@[simp]
lemma comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]
lemma comp_extClass_assoc {Y : C} {n : ℕ} (γ : Ext S.X₁ Y n) {n' : ℕ} (h : 1 + n = n') :
    (Ext.mk₀ S.g).comp (hS.extClass.comp γ h) (zero_add n') = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by omega) (by omega) (by omega),
    comp_extClass, Ext.zero_comp]

@[simp]
lemma extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

@[simp]
lemma extClass_comp_assoc {Y : C} {n : ℕ} (γ : Ext S.X₂ Y n) {n' : ℕ} {h : 1 + n = n'} :
    hS.extClass.comp ((Ext.mk₀ S.f).comp γ (zero_add n)) h = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by omega) (by omega) (by omega),
    extClass_comp, Ext.zero_comp]

end ShortExact

end ShortComplex

end CategoryTheory
