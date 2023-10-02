import Mathlib.Algebra.Homology.Braiding

open CategoryTheory Category Limits MonoidalCategory Preadditive

namespace HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] {c : ComplexShape I} [DecidableEq I]
  [c.Symmetry]
  [(curryObj (MonoidalCategory.tensor C)).Additive]

variable [SymmetricCategory C]

namespace Monoidal

open SymmetricCategory

variable (K L : HomologicalComplex C c) [HasTensor K L] [HasTensor L K]

lemma symmetry :
    (braiding K L).hom ≫ (braiding L K).hom = 𝟙 _ := by
  ext n x y h
  rw [comp_f, ιTensorObj_braiding_hom_assoc, id_f, comp_id, zsmul_comp, assoc,
    ιTensorObj_braiding_hom, comp_zsmul, smul_smul, symmetry_assoc, c.σ_ε_symm,
    ComplexShape.σ_mul_self, one_smul]

end Monoidal

end HomologicalComplex
