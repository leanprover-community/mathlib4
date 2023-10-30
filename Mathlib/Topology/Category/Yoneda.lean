import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.Topology.Category.TopCat.Basic

universe w w' v u

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})
    (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

def yoneda : C ⥤ Type (max w w') where
  obj X := C(Y, F.obj X)
  map f g := ContinuousMap.comp (F.map f) g

def coyoneda : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)

end ContinuousMap

variable [Preregular C] (X : Type v) [TopologicalSpace X] (G : C ⥤ TopCat.{u})
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], QuotientMap (F.map π))

open ContinuousMap

theorem EqualizerConditionCoyoneda : EqualizerCondition (coyoneda G X) := by
  intro Z B π _ _
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · sorry
  · sorry
