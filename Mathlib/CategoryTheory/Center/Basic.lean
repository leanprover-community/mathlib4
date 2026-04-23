/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# The center of a category

Given a category `C`, we introduce an abbreviation `CatCenter C` for
the center of the category `C`, which is `End (𝟭 C)`, the
type of endomorphisms of the identity functor of `C`.

## References
* https://ncatlab.org/nlab/show/center+of+a+category

-/

@[expose] public section
universe v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The center of a category `C` is the type `End (𝟭 C)` of the endomorphisms
of the identify functor of `C`. -/
abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

/-- The action of the center of a category on an object. (This is necessary as
`NatTrans.app x X` is syntactically an endomorphism of `(𝟭 C).obj X`
rather than of `X`.) -/
abbrev app (x : CatCenter C) (X : C) : X ⟶ X := NatTrans.app x X

@[ext]
lemma ext (x y : CatCenter C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext (funext h)

@[reassoc]
lemma naturality (z : CatCenter C) {X Y : C} (f : X ⟶ Y) :
    f ≫ z.app Y = z.app X ≫ f := NatTrans.naturality z f

@[reassoc]
lemma mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

@[reassoc]
lemma mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)

instance : IsMulCommutative (CatCenter C) where
  is_comm.comm x y := by
    ext X
    rw [mul_app' x y, mul_app y x]

instance {X Y : C} : SMul (CatCenter C) (X ⟶ Y) where
  smul z f := f ≫ z.app Y

lemma smul_eq (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = f ≫ z.app Y := rfl

lemma smul_eq' (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = z.app X ≫ f :=
  z.naturality f

instance {X Y : C} : SMul (CatCenter C)ˣ (X ≅ Y) where
  smul z e :=
    { hom := z.1 • e.hom
      inv := (z⁻¹).1 • e.inv
      hom_inv_id := by
        rw [smul_eq, smul_eq', Category.assoc, ← mul_app_assoc]
        simp
      inv_hom_id := by
        rw [smul_eq, smul_eq', Category.assoc, ← mul_app_assoc]
        simp }

@[reassoc]
lemma smul_iso_hom_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = f.hom ≫ z.1.app Y := rfl

@[reassoc]
lemma smul_iso_hom_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = z.1.app X ≫ f.hom :=
  z.1.naturality f.hom

@[reassoc]
lemma smul_iso_inv_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = f.inv ≫ (z⁻¹.1).app X := rfl

@[reassoc]
lemma smul_iso_inv_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = (z⁻¹.1).app Y ≫ f.inv :=
  z.2.naturality f.inv

end CatCenter

end CategoryTheory
