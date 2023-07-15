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

variable [HasLocalization.{w} W]

def Localization' := HasLocalization.D W

instance : Category W.Localization' := HasLocalization.hD

def Q' : C ⥤ W.Localization' := HasLocalization.L

instance : W.Q'.IsLocalization W := HasLocalization.hL

def HasLocalization.standard : HasLocalization.{max u v} W where
  L := W.Q

end MorphismProperty

end CategoryTheory
