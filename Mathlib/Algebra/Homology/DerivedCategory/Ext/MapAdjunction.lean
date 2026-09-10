/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Adjunctions between exact functors and Ext-groups

Assume that `adj : F ⊣ G` is an adjunction between two exact
functors `F : C ⥤ D` and `G : D ⥤ C` between abelian categories.
In this file, we promote the bijection
`adj.homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)` into
additive equivalences
`adj.extEquiv : Ext (F.obj X) Y n ≃+ Ext X (G.obj Y) n`.

-/

@[expose] public section

universe w₁ w₂

namespace CategoryTheory

open Abelian Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

namespace Adjunction

/-- The bijection of `Ext`-groups that is induced by an adjunction
between exact functors. -/
@[simps -isSimp apply symm_apply]
noncomputable def extEquiv (adj : F ⊣ G) {X : C} {Y : D} {n : ℕ} :
    Ext (F.obj X) Y n ≃+ Ext X (G.obj Y) n where
  toFun e := (Ext.mk₀ (adj.unit.app X)).comp (e.mapExactFunctor G) (zero_add n)
  invFun e := (e.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero n)
  left_inv e := by
    dsimp
    rw [Ext.mapExactFunctor_comp, Ext.comp_assoc _ _ _ _ (add_zero n) (by lia),
      ← Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp_mk₀_natTransApp,
      Ext.id_mapExactFunctor, Ext.mapExactFunctor_mk₀,
      ← Ext.comp_assoc _ _ _ (zero_add 0) (by lia) (by lia),
      Ext.mk₀_comp_mk₀, adj.left_triangle_components, Ext.mk₀_id_comp]
  right_inv e := by
    dsimp
    rw [Ext.mapExactFunctor_comp, ← Ext.comp_assoc _ _ _ (zero_add n) (by lia) (by lia),
      ← Ext.comp_mapExactFunctor, ← Ext.mapExactFunctor_comp_mk₀_natTransApp,
      Ext.id_mapExactFunctor, Ext.comp_assoc _ _ _ _ (add_zero 0) (by lia),
      Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.right_triangle_components]
    simp
  map_add' := by simp

@[simp]
lemma extEquiv_mk₀ (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    adj.extEquiv (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv _ _ f) := by
  simp [extEquiv_apply, Ext.mapExactFunctor_mk₀, homEquiv_unit]

lemma extEquiv_symm_mk₀ (adj : F ⊣ G) {X : C} {Y : D} (f : X ⟶ G.obj Y) :
    adj.extEquiv.symm (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv _ _).symm f) :=
  adj.extEquiv.injective (by simp [extEquiv_mk₀])

@[simp]
lemma extEquiv_symm_mk₀_unit_app (adj : F ⊣ G) (X : C) :
    dsimp% adj.extEquiv.symm (Ext.mk₀ (adj.unit.app X)) = Ext.mk₀ (𝟙 (F.obj X)) := by
  simp [extEquiv_symm_mk₀]

@[simp high]
lemma extEquiv_mk₀_counit_app (adj : F ⊣ G) (Y : D) :
    dsimp% adj.extEquiv (Ext.mk₀ (adj.counit.app Y)) = Ext.mk₀ (𝟙 (G.obj Y)) := by
  simp [extEquiv_mk₀, homEquiv_unit]

lemma extEquiv_naturality_left (adj : F ⊣ G) {X₁ X₂ : C} {Y : D} {a b : ℕ}
    (e : Ext X₁ X₂ a) (e' : Ext (F.obj X₂) Y b) {c : ℕ} (h : a + b = c) :
    adj.extEquiv ((e.mapExactFunctor F).comp e' h) =
      e.comp (adj.extEquiv e') h := by
  rw [extEquiv_apply, extEquiv_apply, Ext.mapExactFunctor_comp,
    ← Ext.comp_mapExactFunctor,
    ← Ext.comp_assoc _ _ _ (zero_add a) (by lia) (by lia),
    ← Ext.mapExactFunctor_comp_mk₀_natTransApp]
  simp

lemma extEquiv_naturality_left₀ (adj : F ⊣ G) {X₁ X₂ : C} {Y : D}
    (f : X₁ ⟶ X₂) {n : ℕ} (e : Ext (F.obj X₂) Y n) :
    adj.extEquiv ((Ext.mk₀ (F.map f)).comp e (zero_add n)) =
      (Ext.mk₀ f).comp (adj.extEquiv e) (zero_add n) := by
  simpa [Ext.mapExactFunctor_mk₀] using
    adj.extEquiv_naturality_left (Ext.mk₀ f) e (zero_add n)

lemma extEquiv_naturality_right (adj : F ⊣ G) {X : C} {Y₁ Y₂ : D} {a b : ℕ}
    (e : Ext (F.obj X) Y₁ a) (e' : Ext Y₁ Y₂ b) {c : ℕ} (h : a + b = c) :
    adj.extEquiv (e.comp e' h) = (adj.extEquiv e).comp (e'.mapExactFunctor G) h := by
  rw [extEquiv_apply, extEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.comp_assoc _ _ _ (zero_add a) h (by lia)]

lemma extEquiv_naturality_right₀ (adj : F ⊣ G) {X : C} {Y₁ Y₂ : D} {n : ℕ}
    (e : Ext (F.obj X) Y₁ n) (f : Y₁ ⟶ Y₂) :
    adj.extEquiv (e.comp (Ext.mk₀ f) (add_zero n)) =
      (adj.extEquiv e).comp (Ext.mk₀ (G.map f)) (add_zero n) := by
  simpa [Ext.mapExactFunctor_mk₀] using
    adj.extEquiv_naturality_right e (Ext.mk₀ f) (add_zero n)

lemma extEquiv_symm_naturality_left (adj : F ⊣ G) {X₁ X₂ : C} {Y : D} {a b : ℕ}
    (e : Ext X₁ X₂ a) (e' : Ext X₂ (G.obj Y) b) {c : ℕ} (h : a + b = c) :
    adj.extEquiv.symm (e.comp e' h) =
      (e.mapExactFunctor F).comp (adj.extEquiv.symm e') h :=
  adj.extEquiv.injective (by simp [extEquiv_naturality_left])

lemma extEquiv_symm_naturality_left₀ (adj : F ⊣ G) {X₁ X₂ : C} {Y : D} {n : ℕ}
    (f : X₁ ⟶ X₂) (e : Ext X₂ (G.obj Y) n) :
    adj.extEquiv.symm ((Ext.mk₀ f).comp e (zero_add n)) =
      (Ext.mk₀ (F.map f)).comp (adj.extEquiv.symm e) (zero_add n) := by
  simpa [Ext.mapExactFunctor_mk₀] using
    adj.extEquiv_symm_naturality_left (Ext.mk₀ f) e (zero_add n)

lemma extEquiv_symm_naturality_right (adj : F ⊣ G) {X : C} {Y₁ Y₂ : D} {a b : ℕ}
    (e : Ext X (G.obj Y₁) a) (e' : Ext Y₁ Y₂ b) {c : ℕ} (h : a + b = c) :
    adj.extEquiv.symm (e.comp (e'.mapExactFunctor G) h) =
    (adj.extEquiv.symm e).comp e' h :=
  adj.extEquiv.injective (by simp [extEquiv_naturality_right])

lemma extEquiv_symm_naturality_right₀ (adj : F ⊣ G) {X : C} {Y₁ Y₂ : D} {n : ℕ}
    (e : Ext X (G.obj Y₁) n) (f : Y₁ ⟶ Y₂) :
    adj.extEquiv.symm (e.comp (Ext.mk₀ (G.map f)) (add_zero n)) =
    (adj.extEquiv.symm e).comp (Ext.mk₀ f) (add_zero n) := by
  simpa [Ext.mapExactFunctor_mk₀] using
    adj.extEquiv_symm_naturality_right e (Ext.mk₀ f) (add_zero n)

/-- The linear equivalence on `Ext`-modules that is induced by an adjunction
between exact linear functors. -/
noncomputable abbrev extLinearEquiv (adj : F ⊣ G) (R : Type*) [Ring R] [Linear R C] [Linear R D]
    [Functor.Linear R G]
    {X : C} {Y : D} {n : ℕ} :
    Ext (F.obj X) Y n ≃ₗ[R] Ext X (G.obj Y) n where
  toAddEquiv := adj.extEquiv
  map_smul' := by simp [extEquiv_apply]

end Adjunction

end CategoryTheory
