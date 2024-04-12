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
  ((CatCenter.localizationRingMorphism L W).comp (Linear.toCatCenter R C))

lemma functor_linear :
    letI := linear R L W
    Functor.Linear R L := by
  letI := linear R L W
  exact
    { map_smul := fun {X Y} f r => by
        change L.map (r • f) = ((Linear.toCatCenter R C r).localization L W).app (L.obj X) ≫ L.map f
        simp only [CatCenter.localization_app, ← L.map_comp,
          Functor.id_obj, Linear.toCatCenter_apply_app, Linear.smul_comp, Category.id_comp] }

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

section

variable {E : Type _} [Category E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [L.Additive]
  (R : Type _) [Ring R]
  [Linear R C] [Linear R D] [Linear R E] [L.Linear R]

lemma functor_linear_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G]
    [F.Additive] [G.Additive] :
    F.Linear R ↔ G.Linear R := by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso R (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this, G.map_comp, G.map_comp, ← L.map_id, ← L.map_smul, ← Functor.comp_map,
      (L ⋙ G).map_smul, Functor.map_id, Linear.smul_comp, Linear.comp_smul]
    dsimp
    rw [Category.id_comp, ← G.map_comp, e.inv_hom_id, G.map_id]
  · intro
    exact Functor.linear_of_iso R (Lifting.iso L W F G)

end

end Localization

end CategoryTheory
