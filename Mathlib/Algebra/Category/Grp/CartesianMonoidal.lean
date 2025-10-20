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
# Chosen finite products in `GrpCat` and friends
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace GrpCat

/-- Construct limit data for a binary product in `GrpCat`, using `GrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : GrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `GrpCat.of (G × H)` as the product of `G` and `H` and `GrpCat.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategoryGrp : CartesianMonoidalCategory GrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (GrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory GrpCat.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget GrpCat.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : GrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : GrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget GrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

end GrpCat

namespace AddGrpCat

/-- Construct limit data for a binary product in `AddGrpCat`, using `AddGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `AddGrpCat.of (G × H)` as the product of `G` and `H` and `AddGrpCat.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategoryAddGrp : CartesianMonoidalCategory AddGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory AddGrpCat.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget AddGrpCat.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : AddGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : AddGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

end AddGrpCat

namespace CommGrpCat

/-- Construct limit data for a binary product in `CommGrpCat`, using `CommGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (G H : CommGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `CommGrpCat.of (G × H)` as the product of `G` and `H` and `CommGrpCat.of PUnit` as
the terminal object. -/
noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory CommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

noncomputable instance : BraidedCategory CommGrpCat.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget CommGrpCat.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : CommGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : CommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget CommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

end CommGrpCat

namespace AddCommGrpCat

/-- We choose `AddCommGrpCat.of (G × H)` as the product of `G` and `H` and
`AddCommGrpCat.of PUnit` as the terminal object. -/
noncomputable def cartesianMonoidalCategory : CartesianMonoidalCategory AddCommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H ↦ binaryProductLimitCone G H

@[deprecated (since := "2025-10-10")]
alias cartesianMonoidalCategoryAddCommGrp := cartesianMonoidalCategory

@[deprecated (since := "2025-05-15")]
alias chosenFiniteProductsAddCommGrp := cartesianMonoidalCategory

attribute [local instance] cartesianMonoidalCategory

noncomputable instance : BraidedCategory AddCommGrpCat.{u} := .ofCartesianMonoidalCategory

noncomputable instance : (forget AddCommGrpCat.{u}).Braided := .ofChosenFiniteProducts _

theorem tensorObj_eq (G H : AddCommGrpCat.{u}) : (G ⊗ H) = of (G × H) := rfl

@[simp]
theorem μ_forget_apply {G H : AddCommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddCommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

end AddCommGrpCat
