import Mathlib.CategoryTheory.Endomorphism

universe v u w

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

abbrev Center := End (𝟭 C)

namespace Center

variable {C}

@[ext]
lemma ext (x y : Center C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext _ _ (funext h)

lemma mul_app' (x y : Center C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

lemma mul_app (x y : Center C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)

lemma mul_comm (x y : Center C) : x * y = y * x := by
  ext X
  rw [mul_app' x y, mul_app y x]

end Center

end CategoryTheory
