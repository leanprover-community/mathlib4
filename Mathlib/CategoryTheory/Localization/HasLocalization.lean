import Mathlib.CategoryTheory.Localization.Predicate

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (W : MorphismProperty C)

namespace MorphismProperty

class HasLocalization where
  {D : Type u}
  [hD : Category.{w} D]
  L : C ⥤ D
  [hL : L.IsLocalization W]
  -- this is not really necessary (TODO: remove it)
  L_obj_surjective : Function.Surjective L.obj

variable [HasLocalization.{w} W]

def Localization' := HasLocalization.D W

instance : Category W.Localization' := HasLocalization.hD

def Q' : C ⥤ W.Localization' := HasLocalization.L

instance : W.Q'.IsLocalization W := HasLocalization.hL

lemma Q'_obj_surjective : Function.Surjective W.Q'.obj :=
  HasLocalization.L_obj_surjective

def HasLocalization.standard : HasLocalization.{max u v} W where
  L := W.Q
  L_obj_surjective := by
    rintro ⟨⟨X⟩⟩
    exact ⟨_, rfl⟩

end MorphismProperty

end CategoryTheory
