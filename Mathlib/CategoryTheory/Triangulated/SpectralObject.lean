import Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

namespace CategoryTheory

open Category Limits Pretriangulated ComposableArrows

variable (C ι : Type _) [Category C] [Category ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type _} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {A : Type _} [Category A] [Abelian A]

namespace Triangulated

structure SpectralObject where
  ω₁ : ComposableArrows ι 1 ⥤ C
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

def δ : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧ :=
  X.δ'.app (mk₂ f g)

@[reassoc]
lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0):
    X.ω₁.map β ≫ X.δ f' g' = X.δ f g ≫ (X.ω₁.map α)⟦(1 : ℤ)⟧' := by
  let φ : mk₂ f g ⟶ mk₂ f' g' := homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
    (by simpa only [hαβ] using naturality' β 0 1)
  have h := X.δ'.naturality φ
  dsimp at h
  simp only [hαβ] at h
  convert h <;> aesop_cat

section

@[simps!]
def triangle : Triangle C :=
  Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

lemma triangle_distinguished : X.triangle f g ∈ distTriang C :=
  X.distinguished' (mk₂ f g)

section

variable {f g}
variable {i' j' k' : ι} {f' : i' ⟶ j'} {g' : j' ⟶ k'}

noncomputable def mapTriangle (φ : mk₂ f g ⟶ mk₂ f' g') :
    X.triangle f g ⟶ X.triangle f' g' where
  hom₁ := X.ω₁.map ((functorArrows ι 0 1 2).map φ)
  hom₂ := X.ω₁.map ((functorArrows ι 0 2 2).map φ)
  hom₃ := X.ω₁.map ((functorArrows ι 1 2 2).map φ)
  comm₁ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · dsimp
      erw [id_comp, comp_id]
    · exact naturality' φ 1 2
  comm₂ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · exact naturality' φ 0 1
    · dsimp
      erw [id_comp, comp_id]
  comm₃ := by
    symm
    apply X.δ_naturality
    rfl

end

end

end

section

variable (F : C ⥤ A) [F.PreservesZeroMorphisms] [F.IsHomological] [F.ShiftSequence ℤ]

@[simps]
noncomputable def mapHomologicalFunctor : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app := fun D => F.homology_sequence_δ (X.triangle (D.map' 0 1) (D.map' 1 2)) n₀ n₁ h
      naturality := fun D₁ D₂ φ => by
        obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D₁
        obtain ⟨_, _, _, f', g', rfl⟩ := mk₂_surjective D₂
        exact F.homology_sequence_δ_naturality (X.mapTriangle φ) n₀ n₁ h }
  exact₁' n₀ n₁ h D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homology_sequence_exact₁ _ (X.triangle_distinguished f g) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homology_sequence_exact₂ _ (X.triangle_distinguished f g) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homology_sequence_exact₃ _ (X.triangle_distinguished f g) n₀ n₁ h).exact_toComposableArrows

@[simp]
lemma mapHomologicalFunctor_δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    (X.mapHomologicalFunctor F).δ n₀ n₁ h f g =
      F.homology_sequence_δ (X.triangle f g) n₀ n₁ h := by
  rfl

end

noncomputable def mapTriangulatedFunctor (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ' := whiskerRight X.δ' F ≫
      whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : ℤ)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

end SpectralObject

end Triangulated
