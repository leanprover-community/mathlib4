import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Refinements

open CategoryTheory Category Limits Preadditive
  HomologicalComplex
variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

namespace MappingCone

noncomputable def fromOfShortComplex :
  mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

variable {S}

/-
lemma isIso_homologyMap_fromOfShortComplex (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (fromOfShortComplex S) n) := by
  rw [isIso_iff_mono_and_epi]
  constructor
  . rw [mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨A₁, π₁, hπ₁, z, hz, hz'⟩ := eq_liftCycles_homologyπ_up_to_refinements _ x (n+1) (by simp)
    replace hx := π₁ ≫= hx
    simp [reassoc_of% hz'] at hx
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ _ (n-1) (by simp)] at hx
    obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hx
    simp at hy
    simp only [← cancel_epi π₁, ← cancel_epi π₂, comp_zero, hz', comp_liftCycles_assoc]
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ _ (n-1) (by simp)]
    refine' ⟨_, 𝟙 _, inferInstance, _, sorry⟩
    sorry
  . sorry-/

end MappingCone

end CochainComplex
