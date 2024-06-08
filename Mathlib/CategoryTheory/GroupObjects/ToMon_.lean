import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

open CategoryTheory Limits

universe v u v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
variable [HasFiniteProducts C] [HasFiniteProducts D]

namespace GroupObject

attribute [local instance] monoidalOfHasFiniteProducts

@[simps]
noncomputable def toMon_ : GroupObject C ⥤ Mon_ C where
  obj G := {
    X := G.X
    one := G.one
    mul := G.mul
    one_mul := G.one_mul
    mul_one := G.mul_one
    mul_assoc := G.mul_assoc }
  map f := {
    hom := f.hom
    one_hom := f.one_hom
    mul_hom := f.mul_hom }
  map_id _ := rfl
  map_comp _ _ := rfl

end GroupObject
