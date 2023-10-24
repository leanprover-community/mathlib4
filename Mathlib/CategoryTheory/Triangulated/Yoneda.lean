import Mathlib.CategoryTheory.Triangulated.Opposite
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

namespace CategoryTheory

open Limits Pretriangulated Pretriangulated.Opposite

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

instance (A : Cᵒᵖ) : (preadditiveCoyoneda.obj A).IsHomological where
  exact T hT := by
    rw [ShortComplex.ab_exact_iff]
    intro (x₂ : A.unop ⟶ T.obj₂) (hx₂ : x₂ ≫ T.mor₂ = 0)
    obtain ⟨x₁, hx₁⟩ := T.coyoneda_exact₂ hT x₂ hx₂
    exact ⟨x₁, hx₁.symm⟩

instance (A : C) : (preadditiveYoneda.obj A).IsHomological where
  exact T hT := by
    rw [ShortComplex.ab_exact_iff]
    intro (x₂ : T.obj₂.unop ⟶ A) (hx₂ : T.mor₂.unop ≫ x₂ = 0)
    obtain ⟨x₃, hx₃⟩ := Triangle.yoneda_exact₂ _ (unop_distinguished T hT) x₂ hx₂
    exact ⟨x₃, hx₃.symm⟩

lemma preadditive_yoneda_map_distinguished
    (T : Triangle C) (hT : T ∈ distTriang C) (A : C) :
    ((shortComplexOfDistTriangle T hT).op.map (preadditiveYoneda.obj A)).Exact :=
  (preadditiveYoneda.obj A).map_distinguished_op_exact T hT

end CategoryTheory
