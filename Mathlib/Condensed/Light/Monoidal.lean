import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Condensed.Light.Module
import Mathlib.Condensed.Light.Small

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace CategoryTheory.MonoidalClosed -- TODO: move

instance {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed

namespace LightCondensed

attribute [local instance] monoidalCategory symmetricCategory

variable (R : Type (u + 1)) [CommRing R]

variable (R : Type u) [CommRing R]

instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

local instance : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

end LightCondensed
