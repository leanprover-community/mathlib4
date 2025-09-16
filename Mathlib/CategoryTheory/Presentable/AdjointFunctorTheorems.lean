import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

universe v u

open CategoryTheory Limits Functor

namespace CategoryTheory.Adjunction

variable {C D : Type u} [Category.{v} C] [Category.{v} D] [IsLocallyPresentable.{v} C]
    [IsLocallyPresentable.{v} D]

lemma presentableAdjointFunctorTheorem₁ (L : C ⥤ D) [PreservesColimits L] [HasColimits C] :
    L.IsLeftAdjoint := by
  sorry

lemma presentableAdjointFunctorTheorem₂ (R : C ⥤ D) [IsAccessible.{v} R] [PreservesLimits R]
    [HasLimits C] : R.IsRightAdjoint := by
  apply isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  intro A
  obtain ⟨κ, _, ⟨h⟩⟩ := IsAccessible.exists_cardinal (F := R)
  obtain ⟨κ₁, _, h₁⟩ := IsLocallyPresentable.exists_cardinal (C := C)
  obtain ⟨ι, G, ⟨h₁, h₂⟩⟩ := h₁.toHasCardinalFilteredGenerators.exists_generators
  refine ⟨(i : ι) × (A ⟶ R.obj (G i)), (fun i ↦ G i.fst), fun i ↦ i.snd, ?_⟩ -- ?
  intro X h
  obtain ⟨J, _, _, ⟨diag, incl, hc⟩, hp⟩ := h₂ X
  dsimp only at hp
  obtain ⟨κ₁D, _, h₁D⟩ := IsLocallyPresentable.exists_cardinal (C := D)
  obtain ⟨ιD, GD, ⟨h₁D, h₂D⟩⟩ := h₁D.toHasCardinalFilteredGenerators.exists_generators
  obtain ⟨JD, _, _, ⟨diagD, inclD, hcD⟩, hpD⟩ := h₂D A
  sorry

end CategoryTheory.Adjunction
