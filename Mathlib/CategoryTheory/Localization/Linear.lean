import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.Center.Localization
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Localization

variable (R : Type w) [Ring R] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [L.Additive] [Linear R C]

noncomputable def linear : Linear R D := Linear.ofRingMorphism
  ((Center.localizationRingMorphism L W).comp (Linear.toCenter R C))

lemma functor_linear :
    letI := linear R L W
    Functor.Linear R L := by
  letI := linear R L W
  exact
    { map_smul := fun {X Y} f r => by
        change L.map (r • f) = ((Linear.toCenter R C r).localization L W).app (L.obj X) ≫ L.map f
        simp only [Center.localization_app, ← L.map_comp,
          Functor.id_obj, Linear.toCenter_apply_app, Linear.smul_comp, Category.id_comp] }

section

variable [Preadditive W.Localization] [W.Q.Additive]

noncomputable instance : Linear R W.Localization := Localization.linear R W.Q W

noncomputable instance : Functor.Linear R W.Q := Localization.functor_linear R W.Q W

end

section

variable [W.HasLocalization] [Preadditive W.Localization'] [W.Q'.Additive]

noncomputable instance : Linear R W.Localization' := Localization.linear R W.Q' W

noncomputable instance : Functor.Linear R W.Q' := Localization.functor_linear R W.Q' W

end

end Localization

end CategoryTheory
