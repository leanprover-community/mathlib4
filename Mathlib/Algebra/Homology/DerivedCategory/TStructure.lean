import Mathlib.Algebra.Homology.DerivedCategory.TruncLE
import Mathlib.CategoryTheory.Triangulated.TStructure

open CategoryTheory Category Pretriangulated Triangulated Limits

namespace DerivedCategory

variable {C : Type _} [Category C] [Abelian C]

namespace TStructure

/-def t : TStructure (DerivedCategory C) where
  setLE n := fun K => ∀ (i : ℤ) (hi : n < i), IsZero ((homologyFunctor C i).obj K)
  setGE n := fun K => ∀ (i : ℤ) (hi : i < n), IsZero ((homologyFunctor C i).obj K)
  setLE_respectsIso n := ⟨fun X Y e hX i hi =>
    IsZero.of_iso (hX i hi) ((homologyFunctor C i).mapIso e.symm)⟩
  setGE_respectsIso n := ⟨fun X Y e hX i hi =>
    IsZero.of_iso (hX i hi) ((homologyFunctor C i).mapIso e.symm)⟩
  shift_mem_setGE n a n' hn' X hX i hi :=
    IsZero.of_iso (hX (a + i) (by linarith)) (((homologyFunctor C 0).shiftIso a i _ rfl).app X)
  shift_mem_setLE n a n' hn' X hX i hi :=
    IsZero.of_iso (hX (a + i) (by linarith)) (((homologyFunctor C 0).shiftIso a i _ rfl).app X)
  zero' X Y f hX hY := by
    sorry
  setLE_zero_subset X hX i hi := hX i (by linarith)
  setGE_one_subset X hX i hi := hX i (by linarith)
  exists_triangle_zero_one X := by
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle (X.truncLEι 0)
    refine' ⟨_, _, _, _, _, _, _, mem⟩
    . intro i hi
      exact isZero_homology_truncLE _ _ _ hi
    . intro i hi
      apply (HomologySequence.exact₃ _ mem i (i+1) rfl).isZero_of_both_zeros
      . dsimp
        have := X.isIso_homologyMap_truncLEι 0 i (by linarith)
        have eq := comp_dist_triangle_mor_zero₁₂ _ mem
        dsimp at eq
        rw [← cancel_epi ((homologyFunctor C i).map (truncLEι X 0)),
          ← Functor.map_comp, eq, Functor.map_zero, comp_zero]
      . dsimp
        by_cases hi' : i < 0
        . have := X.isIso_homologyMap_truncLEι 0 (i+1) (by linarith)
          dsimp
          erw [← cancel_mono ((homologyFunctor C (i+1)).map (truncLEι X 0)),
            zero_comp, HomologySequence.δ_comp _ mem]
        . apply IsZero.eq_of_tgt
          apply isZero_homology_truncLE
          linarith-/

end TStructure

end DerivedCategory
