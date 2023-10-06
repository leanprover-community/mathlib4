import Mathlib.Algebra.Homology.Factorizations.CM5b

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)

structure HomFactorization where
  I : C
  i : X ⟶ I
  p : I ⟶ Y
  fac : i ≫ p = f

attribute [reassoc (attr := simp)] HomFactorization.fac

end CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace CochainComplex

variable [Mono f]

namespace CM5aCof

end CM5aCof

/-lemma CM5a_cof (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f :=
  sorry

lemma CM5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f := by
  obtain ⟨L', _, i₁, p₁, _, hp₁, _, rfl⟩ := CM5b f n
  obtain ⟨L'', _, i₂, p₂, _, _, hp₂, rfl⟩ := CM5a_cof i₁ n
  refine' ⟨L'', inferInstance, i₂, p₂ ≫ p₁, inferInstance, inferInstance,
    MorphismProperty.comp_mem _ _ _ hp₂ hp₁, by simp⟩-/

end CochainComplex
