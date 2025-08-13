/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Ring.PUnit
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Chosen finite products in `Grp` and friends
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace Grp

/-- Construct limit data for a binary product in `Grp`, using `Grp.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : Grp.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `Grp.of (G × H)` as the product of `G` and `H` and `Grp.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategoryGrp : CartesianMonoidalCategory Grp.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (Grp.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory Grp.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget Grp.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : Grp.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : Grp.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget Grp.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget Grp.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget Grp.{u}) G H) (p, q)

end Grp

namespace AddGrp

/-- Construct limit data for a binary product in `AddGrp`, using `AddGrp.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddGrp.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `AddGrp.of (G × H)` as the product of `G` and `H` and `AddGrp.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategoryAddGrp : CartesianMonoidalCategory AddGrp.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrp.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory AddGrp.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget AddGrp.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : AddGrp.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : AddGrp.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddGrp.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddGrp.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddGrp.{u}) G H) (p, q)

end AddGrp

namespace CommGrp

/-- Construct limit data for a binary product in `CommGrp`, using `CommGrp.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : CommGrp.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `CommGrp.of (G × H)` as the product of `G` and `H` and `CommGrp.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategoryCommGrp : CartesianMonoidalCategory CommGrp.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrp.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory CommGrp.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget CommGrp.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : CommGrp.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : CommGrp.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget CommGrp.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget CommGrp.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget CommGrp.{u}) G H) (p, q)

end CommGrp

namespace AddCommGrp

/-- We choose `AddCommGrp.of (G × H)` as the product of `G` and `H` and `AddCommGrp.of PUnit` as
the terminal object. -/
noncomputable def cartesianMonoidalCategoryAddCommGrp : CartesianMonoidalCategory AddCommGrp.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrp.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

@[deprecated (since := "2025-05-15")]
alias chosenFiniteProductsAddCommGrp := cartesianMonoidalCategoryAddCommGrp

attribute [local instance] cartesianMonoidalCategoryAddCommGrp

noncomputable instance : BraidedCategory AddCommGrp.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget AddCommGrp.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : AddCommGrp.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : AddCommGrp.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddCommGrp.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddCommGrp.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddCommGrp.{u}) G H) (p, q)

end AddCommGrp
