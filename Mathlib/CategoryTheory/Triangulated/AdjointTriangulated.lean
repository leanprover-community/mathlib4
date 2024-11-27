import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.AdjointCommShift

noncomputable section

namespace CategoryTheory

open Category Functor CategoryTheory Opposite Pretriangulated

namespace Adjunction

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} {D : Type u₂} [Category.{v₁,u₁} C] [Category.{v₂,u₂} D]
  [HasShift C ℤ] [HasShift D ℤ] [Limits.HasZeroObject C]
  [Limits.HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ]

def isTriangulated_of_adjunction (adj : F ⊣ G) [CommShift.adjunction_compat ℤ adj]
    [F.IsTriangulated] : G.IsTriangulated := by
  apply Functor.IsTriangulated.mk
  intro T dT
  obtain ⟨Z, g', h', dT'⟩ := distinguished_cocone_triangle (G.map T.mor₁)
  obtain ⟨θ, hθ₁, hθ₂⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj (Triangle.mk (G.map T.mor₁) g' h')) T (F.map_distinguished _ dT') dT
    (adj.counit.app _) (adj.counit.app _) (adj.counit.naturality _)
  simp at hθ₁ hθ₂
  set φ : Z ⟶ G.obj T.obj₃ := adj.homEquiv _ _ θ with φdef
  have hφ₁ : g' ≫ φ = G.map T.mor₂ := by
    rw [φdef, ← homEquiv_naturality_left, hθ₁]
    simp [homEquiv_apply]
  have hφ₂ : h' = φ ≫ G.map T.mor₃ ≫ (G.commShiftIso 1).hom.app T.obj₁ := by
    rw [φdef, ← assoc, ← homEquiv_naturality_right, ← hθ₂]
    simp only [comp_obj, homEquiv_apply, map_comp, unit_naturality_assoc, assoc,
      commShiftIso_hom_naturality]
    sorry
  have hφ : IsIso φ := sorry
  exact isomorphic_distinguished _ dT' _ (Triangle.isoMk (Triangle.mk (G.map T.mor₁) g' h')
    (G.mapTriangle.obj T) (Iso.refl _) (Iso.refl _) (asIso φ) (by simp) (by simp [hφ₁])
    (by simp [hφ₂])).symm




end Adjunction

end CategoryTheory
