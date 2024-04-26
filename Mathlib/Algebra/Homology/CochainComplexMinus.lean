import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

def Minus [HasZeroMorphisms C] := FullSubcategory (fun (K : CochainComplex C ℤ) => ∃ (n : ℤ), K.IsStrictlyLE n)

instance [HasZeroMorphisms C] : Category (Minus C) := by dsimp [Minus]; infer_instance

namespace Minus

section

variable [HasZeroMorphisms C]

def ι : Minus C ⥤ CochainComplex C ℤ := fullSubcategoryInclusion _

instance : (ι C).Full := FullSubcategory.full _
instance : (ι C).Faithful := FullSubcategory.faithful _

end

variable [Preadditive C]

noncomputable instance : HasShift (Minus C) ℤ := hasShiftOfFullyFaithful (Minus.ι C)
  (fun (n : ℤ) => FullSubcategory.lift _
    (Minus.ι C ⋙ CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) (by
      rintro ⟨K, k, hk⟩
      exact ⟨k - n, K.isStrictlyLE_shift k n _ (by omega)⟩))
    (fun n => FullSubcategory.lift_comp_inclusion _ _ _)

instance : (ι C).CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

end Minus

end CochainComplex
