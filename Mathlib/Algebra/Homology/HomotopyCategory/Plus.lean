import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory

open CategoryTheory Category Limits Triangulated

namespace HomotopyCategory

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

-- needs a refactor of `Subcategory` so as to allow non strictly full subcategories
--def subcategoryPlus : Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) := sorry

end HomotopyCategory
