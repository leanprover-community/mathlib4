/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Adjunctions between exact functors and Ext-groups

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
  invFun e :=
    (e.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero n)
  left_inv := sorry
  right_inv := sorry
  map_add' := by simp

/-- The linear equivalence on `Ext`-modules that is induced by an adjunction
between exact linear functors. -/
noncomputable abbrev extLinearquiv (adj : F ⊣ G) (R : Type*) [Ring R] [Linear R C] [Linear R D]
    [Functor.Linear R F] [Functor.Linear R G]
    {X : C} {Y : D} {n : ℕ} :
    Ext (F.obj X) Y n ≃ₗ[R] Ext X (G.obj Y) n where
  toAddEquiv := adj.extEquiv
  map_smul' := by simp [extEquiv_apply]

end Adjunction

end CategoryTheory
