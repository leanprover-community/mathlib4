import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Orthogonal

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  (K L : CochainComplex C ℤ)

class KInjective : Prop where
  nonempty_homotopy_zero (K : CochainComplex C ℤ) (hK : ∀ (n : ℤ), K.ExactAt n) (f : K ⟶ L) :
    Nonempty (Homotopy f 0)

variable {K L}

noncomputable irreducible_def homotopyZero (f : K ⟶ L)
    (hK : ∀ (n : ℤ), K.ExactAt n) [L.KInjective] :
    Homotopy f 0 :=
  (KInjective.nonempty_homotopy_zero K hK f).some

variable (L)

lemma KInjective_iff_mem_rightOrthogonal :
    L.KInjective ↔
      (HomotopyCategory.quotient _ _).obj L ∈
        (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.set := by
  constructor
  · intro _ ⟨(K : CochainComplex C ℤ)⟩ f hK
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    erw [HomotopyCategory.mem_subcategoryAcyclic_iff_exactAt] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (homotopyZero f hK), Functor.map_zero]
  · intro hL
    refine' ⟨fun K hK f => _⟩
    rw [← HomotopyCategory.mem_subcategoryAcyclic_iff_exactAt] at hK
    refine' ⟨HomotopyCategory.homotopyOfEq _ _ _⟩
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

variable {L}

lemma KInjective_iff_of_iso (e : K ≅ L) :
    K.KInjective ↔ L.KInjective := by
  simp only [KInjective_iff_mem_rightOrthogonal]
  exact Set.mem_iff_of_iso _ ((HomotopyCategory.quotient _ _).mapIso e)

lemma KInjective_of_iso (e : K ≅ L) [K.KInjective] : L.KInjective := by
  rw [← KInjective_iff_of_iso e]
  infer_instance

variable (K)

instance KInjective_shift [hK : K.KInjective] (n : ℤ) : K⟦n⟧.KInjective := by
  simp only [KInjective_iff_mem_rightOrthogonal] at hK ⊢
  erw [Set.mem_iff_of_iso _ ((((HomotopyCategory.quotient C
    (ComplexShape.up ℤ))).commShiftIso n).app K)]
  exact Triangulated.Subcategory.shift _ _ n hK

lemma KInjective_shift_iff (n : ℤ) :
    K⟦n⟧.KInjective ↔ K.KInjective := by
  constructor
  · intro
    exact KInjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K)
  · intro
    infer_instance

end CochainComplex
