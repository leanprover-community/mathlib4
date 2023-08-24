import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Localization.Preadditive

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (r s : Center C) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace Center

noncomputable def localization : Center D :=
  Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (whiskerRight r L)

@[simp]
lemma localization_app (X : C) :
    (r.localization L W).app (L.obj X) = L.map (r.app X) := by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

lemma ext_of_localization (r s : Center D)
    (h : ∀ (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s :=
  Localization.natTrans_ext L W _ _ h

lemma localization_one :
    (1 : Center C).localization L W = 1 :=
  ext_of_localization L W _ _ (fun X => by simp)

lemma localization_mul :
    (r * s).localization L W = r.localization L W * s.localization L W :=
  ext_of_localization L W _ _ (fun X => by simp)

section Preadditive

variable [Preadditive C] [Preadditive D] [L.Additive]

lemma localization_zero :
    (0 : Center C).localization L W = 0 :=
  ext_of_localization L W _ _ (fun X => by simp)

lemma localization_add :
    (r + s).localization L W = r.localization L W + s.localization L W :=
  ext_of_localization L W _ _ (fun X => by
    rw [localization_app, NatTrans.app_add, NatTrans.app_add, L.map_add,
      localization_app, localization_app])

noncomputable def localizationRingMorphism : Center C →+* Center D where
  toFun r := r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

end Preadditive

end Center

end CategoryTheory
