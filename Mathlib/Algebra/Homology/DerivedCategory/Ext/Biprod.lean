/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Ext and binary biproducts

In this file, we decompose the abelian group
`Ext (X₁ ⊞ X₂) Y n` as the product of `Ext X₁ Y n` and `Ext X₂ Y n`.

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

variable {X₁ X₂ Y : C} {n : ℕ}

/-- The additive equivalence `Ext.{w} (X₁ ⊞ X₂) Y n ≃+ Ext.{w} X₁ Y n × Ext.{w} X₂ Y n`. -/
@[simps (config := .lemmasOnly) apply apply_fst apply_snd symm_apply]
noncomputable def fromBiprodEquiv : Ext.{w} (X₁ ⊞ X₂) Y n ≃+ Ext.{w} X₁ Y n × Ext.{w} X₂ Y n where
  toFun e := ⟨(mk₀ biprod.inl).comp e (zero_add n), (mk₀ biprod.inr).comp e (zero_add n)⟩
  invFun e := (mk₀ biprod.fst).comp e.1 (zero_add n) + (mk₀ biprod.snd).comp e.2 (zero_add n)
  left_inv e := by simp [← add_comp, ← mk₀_add]
  right_inv e := by aesop
  map_add' e₁ e₂ := by aesop

variable (X₁ X₂ Y n)

/-- The isomorphism in the category `AddCommGrp` between `AddCommGrp.of (Ext.{w} (X₁ ⊞ X₂) Y n)`
and `AddCommGrp.of (Ext.{w} X₁ Y n) ⊞ AddCommGrp.of (Ext.{w} X₂ Y n)`. -/
noncomputable def fromBiprodIso : AddCommGrp.of (Ext.{w} (X₁ ⊞ X₂) Y n) ≅
    AddCommGrp.of (Ext.{w} X₁ Y n) ⊞ AddCommGrp.of (Ext.{w} X₂ Y n) :=
  (AddEquiv.toAddCommGrpIso fromBiprodEquiv).trans (AddCommGrp.biprodIsoProd _ _).symm

variable {X₁ X₂ Y n}

lemma fromBiprodIso_inv_apply (e₁ : Ext.{w} X₁ Y n) (e₂ : Ext.{w} X₂ Y n) :
  (fromBiprodIso X₁ X₂ Y n).inv
    ((AddCommGrp.biprodIsoProd (AddCommGrp.of (Ext.{w} X₁ Y n))
    (AddCommGrp.of (Ext.{w} X₂ Y n))).inv ⟨e₁, e₂⟩) =
      fromBiprodEquiv.symm ⟨e₁, e₂⟩ := by
  sorry

lemma biprod_inl_comp_fromBiprodIso_inv_apply
    (x : ((AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n)) :)) :
    (mk₀ biprod.inl).comp ((fromBiprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.fst : AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n) ⟶ _) x := by
  sorry

lemma biprod_inr_comp_fromBiprodIso_inv_apply
    (x : ((AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n)) :)) :
    (mk₀ biprod.inr).comp ((fromBiprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.snd : AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n) ⟶ _) x := by
  sorry

end Ext

end Abelian

end CategoryTheory
