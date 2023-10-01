import Mathlib.Algebra.Homology.Braiding

open CategoryTheory Category Limits MonoidalCategory Preadditive

namespace ComplexShape

variable {I : Type*} [AddCommMonoid I] (c : ComplexShape I)

class Symmetry extends c.Braiding where
  symm (i₁ i₂ : I) : c.σ.ε i₁ i₂ = c.σ.ε i₂ i₁

lemma σ_ε_symm [c.Symmetry] (i₁ i₂ : I) : c.σ.ε i₁ i₂ = c.σ.ε i₂ i₁ := by
  apply Symmetry.symm

instance : (ComplexShape.up ℤ).Symmetry where
  symm p q := by
    change Int.negOnePow _ = Int.negOnePow _
    rw [mul_comm]

end ComplexShape

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
    TotalComplexShapeSymmetry.ε_mul_self, one_smul]

end Monoidal

end HomologicalComplex
