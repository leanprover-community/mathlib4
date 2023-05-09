import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.NewHomology

open CategoryTheory Category

namespace HomologicalComplex

variable {C : Type _} [Category C] [Abelian C] {ι : Type _} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

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

end HomologicalComplex
