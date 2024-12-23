/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Endomorphism

/-!
# Center of a category

-/
universe v u w

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

@[ext]
lemma ext (x y : CatCenter C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext (funext h)

@[reassoc]
lemma naturality (x : CatCenter C) {X Y : C} (f : X ⟶ Y) :
    f ≫ x.app Y = x.app X ≫ f :=
  NatTrans.naturality x f

/-- `(x * y).app X = y.app X ≫ x.app X`. -/
@[reassoc]
lemma mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

@[reassoc]
lemma mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)

lemma mul_comm (x y : CatCenter C) : x * y = y * x := by
  ext X
  rw [mul_app' x y, mul_app y x]

instance : CommMonoid (CatCenter C) where
  mul_comm := mul_comm

def unitsMulEquiv : (CatCenter C)ˣ ≃* Aut (𝟭 C) := Aut.unitsEndEquivAut _

@[simp]
lemma unitsMulEquiv_apply_hom_app (x : (CatCenter C)ˣ) (X : C) :
    (unitsMulEquiv x).hom.app X = x.val.app X := rfl

@[simp]
lemma unitsMulEquiv_apply_inv_app (x : (CatCenter C)ˣ) (X : C) :
    (unitsMulEquiv x).inv.app X = x.inv.app X := rfl

end CatCenter

-- to be moved

namespace Aut

variable {C} {X : C}

@[reassoc (attr := simp)]
lemma mul_hom (x y : Aut X) : (x * y).hom = y.hom ≫ x.hom := rfl

@[reassoc (attr := simp)]
lemma mul_inv (x y : Aut X) : (x * y).inv = x.inv ≫ y.inv := rfl

end Aut

namespace Functor

variable {C}

class CommutesWithCenterElement (F : C ⥤ C) (z : CatCenter C) : Prop where
  map_app (X : C) : F.map (z.app X) = z.app (F.obj X)

@[simp]
lemma map_app_of_commutesWithCenterElement (F : C ⥤ C) (z : CatCenter C) (X : C)
    [F.CommutesWithCenterElement z] :
    F.map (z.app X) = z.app (F.obj X) :=
  CommutesWithCenterElement.map_app X

end Functor

end CategoryTheory
