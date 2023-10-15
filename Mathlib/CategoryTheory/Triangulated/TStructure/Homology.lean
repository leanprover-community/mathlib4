import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C) [t.HasHeart] [IsTriangulated C]

class HasHomology₀ where
  homology₀ : C ⥤ t.Heart
  iso : homology₀ ⋙ t.ιHeart ≅ t.truncGELE 0 0

variable [IsTriangulated C]

lemma truncLE₀GE₀_mem_heart (X : C) :
    (t.truncLEGE 0 0).obj X ∈ t.heart := by
  rw [t.mem_heart_iff]
  dsimp [truncLEGE]
  constructor
  · infer_instance
  · infer_instance

lemma truncGE₀LE₀_mem_heart (X : C) :
    (t.truncGELE 0 0).obj X ∈ t.heart := by
  rw [t.mem_heart_iff]
  constructor <;> infer_instance

noncomputable def hasHomology₀ : t.HasHomology₀ where
  homology₀ := t.liftHeart (t.truncGELE 0 0) t.truncGE₀LE₀_mem_heart
  iso := t.liftHeartιHeart _ _

variable [ht : t.HasHomology₀]

def homology₀ : C ⥤ t.Heart := ht.homology₀

def homology₀ιHeart : t.homology₀ ⋙ t.ιHeart ≅ t.truncGELE 0 0 := ht.iso

end TStructure

end Triangulated

end CategoryTheory
