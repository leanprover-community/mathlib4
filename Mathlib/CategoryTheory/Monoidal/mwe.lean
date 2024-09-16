import Mathlib.CategoryTheory.Monoidal.Braided.Basic

universe v₁ u₁

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

namespace mwe

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class Mon_Class (X : C) where
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul : one ▷ X ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : X ◁ one ≫ mul = (ρ_ X).hom := by aesop_cat
  mul_assoc : mul ▷ X ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

namespace Mon_Class

scoped notation "μ" => Mon_Class.mul
scoped notation "μ["M"]" => Mon_Class.mul (X := M)
scoped notation "η" => Mon_Class.one
scoped notation "η["M"]" => Mon_Class.one (X := M)

end Mon_Class

class Comon_Class (X : C) where
  counit : X ⟶ 𝟙_ C
  comul : X ⟶ X ⊗ X
  counit_comul : comul ≫ counit ▷ X = (λ_ X).inv := by aesop_cat
  comul_counit : comul ≫ X ◁ counit = (ρ_ X).inv := by aesop_cat
  comul_assoc : comul ≫ X ◁ comul = comul ≫ comul ▷ X ≫ (α_ X X X).hom := by aesop_cat

namespace Comon_Class

scoped notation "Δ" => Comon_Class.comul
scoped notation "Δ["M"]" => Comon_Class.comul (X := M)
scoped notation "ε" => Comon_Class.counit
scoped notation "ε["M"]" => Comon_Class.counit (X := M)

end Comon_Class

end mwe
