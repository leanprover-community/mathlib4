/-import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

namespace CategoryTheory

open Category Limits Pretriangulated

variable (C ι : Type _) [Category C] [Category ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type _} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {A : Type _} [Category A] [Abelian A]

namespace Triangulated

structure SpectralObject where
  ω₁ : Arrow ι ⥤ C
  δ : Arrow₂.δ₀ ⋙ ω₁ ⟶ Arrow₂.δ₂ ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : Arrow₂ ι) :
    Triangle.mk (ω₁.map (Arrow₂.δ₂Toδ₁.app D))
      (ω₁.map (Arrow₂.δ₁Toδ₀.app D)) (δ.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

def ω₂ : Arrow₂ ι ⥤ Triangle C where
  obj D := Triangle.mk (X.ω₁.map (Arrow₂.δ₂Toδ₁.app D)) (X.ω₁.map (Arrow₂.δ₁Toδ₀.app D)) (X.δ.app D)
  map f :=
    { hom₁ := X.ω₁.map (Arrow₂.δ₂.map f)
      hom₂ := X.ω₁.map (Arrow₂.δ₁.map f)
      hom₃ := X.ω₁.map (Arrow₂.δ₀.map f)
      comm₁ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality]
      comm₂ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality]
      comm₃ := (X.δ.naturality f).symm }

lemma distinguished (D : Arrow₂ ι) :
    X.ω₂.obj D ∈ distTriang C := X.distinguished' D

@[simps]
noncomputable def mapHomologicalFunctor (F : C ⥤ A) [F.PreservesZeroMorphisms]
    [F.IsHomological] [F.ShiftSequence ℤ] : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ n₀ n₁ h :=
    { app := fun D => F.homology_sequence_δ (X.ω₂.obj D) n₀ n₁ h
      naturality := fun _ _ φ => F.homology_sequence_δ_naturality (X.ω₂.map φ) _ _ h }
  zero₁ _ _ h D := F.homology_sequence_δ_comp _ (X.distinguished D) _ _ h
  zero₂ _ D := F.homology_sequence_comp _ (X.distinguished D) _
  zero₃ _ _ h D := F.comp_homology_sequence_δ _ (X.distinguished D) _ _ h
  exact₁ _ _ h D := F.homology_sequence_exact₁ _ (X.distinguished D) _ _ h
  exact₂ _ D := F.homology_sequence_exact₂ _ (X.distinguished D) _
  exact₃ _ _ h D := F.homology_sequence_exact₃ _ (X.distinguished D) _ _ h

def mapTriangulatedFunctor (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ := whiskerRight X.δ F ≫ whiskerLeft (Arrow₂.δ₂ ⋙ X.ω₁) (F.commShiftIso (1 : ℤ)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished D)

end SpectralObject

end Triangulated

end CategoryTheory

-/
