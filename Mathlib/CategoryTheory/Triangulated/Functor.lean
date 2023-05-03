import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Shift.CommShift

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D E : Type _} [Category C] [Category D] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (F : C ⥤ D) [F.HasCommShift ℤ] (G : D ⥤ E) [G.HasCommShift ℤ]

@[simps]
def mapTriangle : Pretriangulated.Triangle C ⥤ Pretriangulated.Triangle D where
  obj T := Pretriangulated.Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp ; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp ; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [Functor.comp]
        simp only [Category.assoc, ← NatTrans.naturality,
          ← F.map_comp_assoc, f.comm₃] }
