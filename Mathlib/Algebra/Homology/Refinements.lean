import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Category

namespace HomologicalComplex

variable {C : Type _} [Category C] [Abelian C] {ι : Type _} {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

lemma eq_liftCycles_homologyπ_up_to_refinements {A : C} {i : ι} (γ : A ⟶ K.newHomology i)
  (j : ι) (hj : c.next i = j) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ K.X i) (hz : z ≫ K.d i j = 0),
      π ≫ γ = K.liftCycles z j hj hz ≫ K.homologyπ i := by
  subst hj
  exact (K.sc i).eq_liftCycles_homologyπ_up_to_refinements γ

lemma liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} {i : ι} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0)
      (i' : ι) (hi' : c.prev i = i'):
    K.liftCycles k j hj hk ≫ K.homologyπ i = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (l : A' ⟶ K.X i'), π ≫ k = l ≫ K.d i' i := by
  subst hi'
  apply (K.sc i).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements

lemma liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    {A : C} {i : ι} (k k' : A ⟶ K.X i) (j : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0)
      (hk' : k' ≫ K.d i j = 0)
      (i' : ι) (hi' : c.prev i = i'):
    K.liftCycles k j hj hk ≫ K.homologyπ i = K.liftCycles k' j hj hk' ≫ K.homologyπ i ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (l : A' ⟶ K.X i'), π ≫ k = π ≫ k' + l ≫ K.d i' i := by
  subst hi'
  apply (K.sc i).liftCycles_comp_homologyπ_eq_iff_up_to_refinements

variable {K L}

lemma mono_homologyMap_iff_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Mono (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0) (y₁ : A ⟶ L.X i)
          (_ : x₂ ≫ φ.f j = y₁ ≫ L.d i j),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i),
          π ≫ x₂ = x₁ ≫ K.d i j := by
  subst hi hk
  apply ShortComplex.mono_homologyMap_iff_up_to_refinements

lemma epi_homologyMap_iff_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Epi (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ L.X j) (_ : y₂ ≫ L.d j k = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0)
          (y₁ : A' ⟶ L.X i), π ≫ y₂ = x₂ ≫ φ.f j + y₁ ≫ L.d i j := by
  subst hi hk
  apply ShortComplex.epi_homologyMap_iff_up_to_refinements

end HomologicalComplex
