import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The functor from `Set X` to types preserves filtered colimits

Given `X : Type u`, the functor `Set.functorToTypes : Set X ⥤ Type u`
which sends `A : Set X` to its underlying type preserves filtered colimits.

-/

@[expose] public section

universe w w' u

open CategoryTheory Limits CompleteLattice

namespace Set

open CompleteLattice in
instance {J : Type w} [Category.{w'} J] {X : Type u} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (functorToTypes (X := X)) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimitCocone F).isColimit
    apply Types.FilteredColimit.isColimitOf
    · rintro ⟨x, hx⟩
      simp only [colimitCocone_cocone_pt, iSup_eq_iUnion, mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · intro i j ⟨x, hx⟩ ⟨y, hy⟩ h
      obtain rfl : x = y := by simpa using h
      exact ⟨IsFiltered.max i j, IsFiltered.leftToMax i j, IsFiltered.rightToMax i j, rfl⟩

end Set
