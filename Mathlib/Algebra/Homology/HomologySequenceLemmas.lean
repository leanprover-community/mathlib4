import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

open CategoryTheory Category ComposableArrows Limits Abelian

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex.HomologySequence

@[simps]
noncomputable def mapSnakeInput (i j : ι) (hij : c.Rel i j) :
    snakeInput hS₁ i j hij ⟶ snakeInput hS₂ i j hij where
  f₀ := (homologyFunctor C c i).mapShortComplex.map φ
  f₁ := (opcyclesFunctor C c i).mapShortComplex.map φ
  f₂ := (cyclesFunctor C c j).mapShortComplex.map φ
  f₃ := (homologyFunctor C c j).mapShortComplex.map φ

lemma δ_naturality (i j : ι) (hij : c.Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ _ =
      HomologicalComplex.homologyMap φ.τ₃ _ ≫ hS₂.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (mapSnakeInput φ hS₁ hS₂ i j hij)

end HomologicalComplex.HomologySequence
