import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.IsLE
import Mathlib.CategoryTheory.Triangulated.Subcategory

open CategoryTheory Category Limits Triangulated ZeroObject

namespace HomotopyCategory

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-def subcategoryPlus : Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) where
  set K := ∃ (n : ℤ), CochainComplex.IsStrictlyLE K.1 n
  zero' := by
    refine' ⟨⟨0⟩, _, ⟨0, _⟩⟩
    · change IsZero ((quotient _ _).obj 0)
      rw [IsZero.iff_id_eq_zero, ← (quotient _ _).map_id, id_zero, Functor.map_zero]
    · dsimp
      infer_instance
  shift := by
    rintro X n ⟨k, _⟩
    refine' ⟨k - n, _⟩
    dsimp
    -- Quotient.functor_obj_shift
    -- CochainComplex.isStrictlyLE_shift
    sorry
  ext₂' := sorry-/

end HomotopyCategory
