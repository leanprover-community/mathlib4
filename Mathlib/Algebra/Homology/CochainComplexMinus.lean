import Mathlib.Algebra.Homology.Embedding.CochainComplex

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C]

def Minus := FullSubcategory (fun (K : CochainComplex C ℤ) => ∃ (n : ℤ), K.IsStrictlyLE n)

instance : Category (Minus C) := by dsimp [Minus]; infer_instance

namespace Minus

def ι : Minus C ⥤ CochainComplex C ℤ := fullSubcategoryInclusion _

instance : (ι C).Full := FullSubcategory.full _
instance : (ι C).Faithful := FullSubcategory.faithful _

end Minus

end CochainComplex
