import Mathlib.Algebra.Homology.Braiding

open CategoryTheory Category Limits MonoidalCategory Preadditive

namespace HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] {c : ComplexShape I} [DecidableEq I]
  {s : c.TensorSigns} (β : s.Braiding)
  [(curryObj (MonoidalCategory.tensor C)).Additive]

variable [SymmetricCategory C]

namespace Monoidal

open SymmetricCategory

variable (K L : HomologicalComplex C c) [HasTensor K L] [HasTensor L K]
  (hβ : ∀ (i₁ i₂ : I), β.σ.ε i₁ i₂ = β.σ.ε i₂ i₁)

lemma symmetry :
    (braiding K L β ).hom ≫ (braiding L K β ).hom = 𝟙 _ := by
  ext n x y h
  rw [comp_f, ιTensorObj_braiding_hom_assoc, id_f, comp_id, zsmul_comp, assoc,
    ιTensorObj_braiding_hom, comp_zsmul, smul_smul, symmetry_assoc, hβ,
    TotalComplexShapeSymmetry.ε_mul_self, one_smul]

end Monoidal

end HomologicalComplex
