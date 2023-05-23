import Mathlib.CategoryTheory.ExactCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactCategory

variable (C)

def splitShortExact : Set (ShortComplex C) := fun S => Nonempty S.Splitting

/- WIP
def splitExactSequences : ExactCategory C where
  shortExact' := splitShortExact C
  respectsIso_shortExact' := ⟨fun S₁ S₂ e => by
    rintro ⟨h₁⟩
    exact ⟨h₁.ofIso e⟩⟩
  shortExact_kernel' := by
    rintro S ⟨hS⟩
    exact ⟨hS.fIsKernel⟩
  shortExact_cokernel' := by
    rintro S ⟨hS⟩
    exact ⟨hS.gIsCokernel⟩
  admissibleMono_id X := ⟨0, 0, comp_zero, ⟨ShortComplex.Splitting.ofIsIsoOfIsZero _
    (by dsimp ; infer_instance) (isZero_zero _)⟩⟩
  admissibleEpi_id X := ⟨0, 0, zero_comp, ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _
    (isZero_zero _) (by dsimp ; infer_instance)⟩⟩
  admissibleMono_stableUnderComposition := by
    rintro X Y Z f₁ f₂ ⟨A₁, g₁, zero₁, ⟨h₁⟩⟩ ⟨A₂, g₂, zero₂, ⟨h₂⟩⟩
    refine' ⟨A₁ ⊞ A₂, biprod.lift _ g₂, _ , _⟩
    . sorry
    . sorry
    . sorry
  admissibleEpi_stableUnderComposition := sorry
  admissibleMono_coquarrable := sorry
  admissibleEpi_quarrable := sorry
  admissibleMono_stableUnderCobaseChange := sorry
  admissibleEpi_stableUnderBaseChange := sorry -/

end ExactCategory

end CategoryTheory
