/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category* C] [Category* D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero := { app := fun _ => 0 }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β := { app := fun X => α.app X + β.app X }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α := { app := fun X => -α.app X }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_nsmul, NatTrans.naturality, nsmul_comp] }
      zsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_zsmul, NatTrans.naturality, zsmul_comp] }
      sub α β := { app := fun X => α.app X - β.app X }
      add_assoc _ _ _ := NatTrans.ext <| add_assoc _ _ _
      zero_add _ := NatTrans.ext <| zero_add _
      add_zero _ := NatTrans.ext <| add_zero _
      nsmul_zero _ := NatTrans.ext <| zero_nsmul _
      nsmul_succ _ _ := NatTrans.ext <| succ_nsmul _ _
      sub_eq_add_neg _ _ := NatTrans.ext <| sub_eq_add_neg _ _
      zsmul_zero' _ := NatTrans.ext <| zero_zsmul _
      zsmul_succ' _ _ := NatTrans.ext <| SubNegMonoid.zsmul_succ' _ _
      zsmul_neg' _ _ := NatTrans.ext <| SubNegMonoid.zsmul_neg' _ _
      neg_add_cancel _ := NatTrans.ext <| neg_add_cancel _
      add_comm _ _ := NatTrans.ext <| add_comm _ _ }
  add_comp _ _ _ _ _ _ := NatTrans.ext <| funext fun _ ↦ add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := NatTrans.ext <| funext fun _ ↦ comp_add _ _ _ _ _ _

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appHom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X) where
  toFun α := α.app X
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem app_zero (X : C) : (0 : F ⟶ G).app X = 0 :=
  rfl

@[simp]
theorem app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X :=
  rfl

@[simp]
theorem app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X :=
  rfl

@[simp]
theorem app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X :=
  rfl

@[simp]
theorem app_nsmul (X : C) (α : F ⟶ G) (n : ℕ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
theorem app_zsmul (X : C) (α : F ⟶ G) (n : ℤ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
theorem app_units_zsmul (X : C) (α : F ⟶ G) (n : ℤˣ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
theorem app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι → (F ⟶ G)) :
    (∑ i ∈ s, α i).app X = ∑ i ∈ s, (α i).app X := by
  simp only [← appHom_apply, map_sum]

end NatTrans

end CategoryTheory
