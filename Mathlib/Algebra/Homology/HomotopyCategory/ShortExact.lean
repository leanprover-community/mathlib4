import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Refinements

import Mathlib.Tactic.LibrarySearch

open CategoryTheory Category Limits Preadditive
  HomologicalComplex
variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

namespace MappingCone

noncomputable def fromOfShortComplex :
  mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

variable {S}

lemma isIso_homologyMap_fromOfShortComplex (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (fromOfShortComplex S) n) := by
  have : ∀ i, PreservesFiniteLimits (HomologicalComplex.eval C (ComplexShape.up ℤ) i) := sorry
  have : ∀ i, PreservesFiniteColimits (HomologicalComplex.eval C (ComplexShape.up ℤ) i) := sorry
  have hS' := fun i => hS.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
  have : ∀ i, Mono (S.f.f i) := fun i => (hS' i).mono_f
  have : ∀ i, Epi (S.g.f i) := fun i => (hS' i).epi_g
  rw [isIso_iff_mono_and_epi]
  constructor
  . rw [mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨A₁, π₁, hπ₁, z, hz, hz'⟩ := eq_liftCycles_homologyπ_up_to_refinements _ x (n+1) (by simp)
    obtain ⟨z₁, z₂, hz₁₂⟩ := to_break _ z _ rfl
    simp [hz₁₂] at hz
    rw [to_ext_iff _ _ _ (n+2) (by linarith)] at hz
    simp [inl_v_d_assoc _ (n+1) n (n+2) (by linarith) (by linarith)] at hz
    replace hx := π₁ ≫= hx
    simp [reassoc_of% hz'] at hx
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ _ (n-1) (by simp)] at hx
    obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hx
    simp [hz₁₂, fromOfShortComplex] at hy
    obtain ⟨A₃, π₃, hπ₃, w, hw⟩ := surjective_up_to_refinements_of_epi (S.g.f (n-1)) y
    obtain ⟨A₄, π₄, hπ₄, t, ht⟩ := (hS' n).exact.exact_up_to_refinements (π₃ ≫ π₂ ≫ z₂ - w ≫ S.X₂.d (n-1) n) (by
      dsimp
      simp only [sub_comp, assoc, ← S.g.comm, ← reassoc_of% hw, hy, sub_self])
    dsimp at t ht
    simp only [comp_sub] at ht
    simp only [← cancel_epi π₁, ← cancel_epi π₂, ← cancel_epi π₃, ← cancel_epi π₄, hz',
      comp_zero, comp_liftCycles_assoc]
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ _ (n-1) (by simp)]
    refine' ⟨A₄, 𝟙 _, inferInstance,
      t ≫ (inl S.f).v n (n-1) (by linarith) + π₄ ≫ w ≫ (inr S.f).f (n-1), _⟩
    simp [to_ext_iff _ _ _ (n+1) rfl, hz₁₂]
    constructor
    . simp only [← cancel_mono (S.f.f (n+1)), assoc, neg_comp, ← S.f.comm, ← reassoc_of% ht,
        sub_comp, d_comp_d, comp_zero, sub_zero]
      simp only [← add_eq_zero_iff_eq_neg, ← comp_add, hz.2, comp_zero]
    . rw [← ht]
      abel
  . sorry

end MappingCone

end CochainComplex
