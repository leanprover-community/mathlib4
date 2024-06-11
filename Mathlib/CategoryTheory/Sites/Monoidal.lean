import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Sites.Sheafification

noncomputable section

open CategoryTheory Monoidal MonoidalCategory

namespace CategoryTheory

namespace Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] (L : C ⥤ D) (R : D ⥤ C)
    [R.Full] [R.Faithful] (adj : L ⊣ R)

example : IsIso adj.counit := inferInstance

def monnoidalCategoryStructMap : MonoidalCategoryStruct D where
  tensorObj X Y := L.obj (R.obj X ⊗ R.obj Y)
  tensorHom α β := L.map (R.map α ⊗ R.map β)
  whiskerLeft X _ _ α := L.map (R.obj X ◁ R.map α)
  whiskerRight α X := L.map (R.map α ▷ R.obj X)
  tensorUnit := L.obj (𝟙_ _)
  associator X Y Z := by
    dsimp only
    -- refine L.mapIso (asIso (adj.counit.app _) ≪≫ ?_)
    let i := α_ (R.obj X) (R.obj Y) (R.obj Z)
    sorry
  leftUnitor := sorry
  rightUnitor := sorry


namespace Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
variable {D : Type*} [Category D] [MonoidalCategory D] [HasWeakSheafify J D]



/-- (An auxiliary definition for `sheafCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
def tensorObj (F G : Sheaf J D) : Sheaf J D :=
  (presheafToSheaf J D).obj (F.val ⊗ G.val)

variable {F G F' G' : Sheaf J D}
variable (α : F ⟶ G) (β : F' ⟶ G')

/-- (An auxiliary definition for `sheafCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
def tensorHom : tensorObj F F' ⟶ tensorObj G G' :=
  (presheafToSheaf J D).map (α.val ⊗ β.val)

/-- (An auxiliary definition for `sheafCategoryMonoidal`.) -/
def whiskerLeft (F) (β : F' ⟶ G') : tensorObj F F' ⟶ tensorObj F G' :=
  (presheafToSheaf J D).map (F.val ◁ β.val)

/-- (An auxiliary definition for `sheafCategoryMonoidal`.) -/
def whiskerRight (F') : tensorObj F F' ⟶ tensorObj G F' :=
  (presheafToSheaf J D).map (α.val ▷ F'.val)

instance : MonoidalCategoryStruct (Sheaf J D) where
  tensorObj F G := tensorObj F G
  whiskerLeft := sorry
  whiskerRight := sorry
  tensorHom := sorry
  tensorUnit := sorry
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry

-- instance : MonoidalCategory (Sheaf J D) where
--   tensorHom_def := sorry
--   pentagon F G H K := sorry

end CategoryTheory.Monoidal.Sheaf
