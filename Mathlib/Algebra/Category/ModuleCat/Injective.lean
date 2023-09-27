/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Category of $R$-modules has enough injectives

we lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`

## Implementation notes
This file is not part of `Algebra/Module/Injective.lean` to prevent import loop: enough-injectives
of abelian groups needs `Algebra/Module/Injective.lean` and this file needs enough-injectives of
abelian groups.
-/

open CategoryTheory

universe u v
variable (R : Type u) [Ring R]

instance : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction
    (L := forget₂ (ModuleCat.{max v u} R) AddCommGroupCat.{max v u})
    (R := (forget₂ (ModuleCat.{max v u} ℤ) AddCommGroupCat.{max v u}).asEquivalence.inverse ⋙
      ModuleCat.coextendScalars (algebraMap ℤ R)) <|
    let iso : ModuleCat.restrictScalars.{max v u} (algebraMap ℤ R) ⋙
      (forget₂ (ModuleCat.{max v u} ℤ) AddCommGroupCat.{max v u}).asEquivalence.functor ≅
      forget₂ (ModuleCat.{max v u} R) AddCommGroupCat.{max v u} :=
    { hom :=
      { app := fun _ => 𝟙 _
        naturality := by aesop_cat }
      inv :=
      { app := fun _ => 𝟙 _
        naturality := by aesop_cat }
      hom_inv_id := by aesop_cat
      inv_hom_id := by aesop_cat }
    (((ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))).comp <|
      (forget₂ (ModuleCat ℤ) AddCommGroupCat).asEquivalence.toAdjunction).ofNatIsoLeft iso
