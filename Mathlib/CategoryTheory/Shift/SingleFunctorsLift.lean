import Mathlib.CategoryTheory.Shift.SingleFunctors
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace CategoryTheory

open Category

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {A : Type*} [AddMonoid A] [HasShift D A] [HasShift E A]
  (F : SingleFunctors C E A) (G : D ⥤ E) [G.CommShift A]
  [G.Full] [G.Faithful]
  (Φ : A → C ⥤ D)
  (hΦ : ∀ a, Φ a ⋙ G ≅ F.functor a)

namespace SingleFunctors

namespace Lift

variable {F G Φ}

def shiftIso (n a a' : A) (h : n + a = a') :
    Φ a' ⋙ shiftFunctor D n ≅ Φ a :=
  natIsoOfCompFullyFaithful G (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

lemma map_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) :
    G.map ((Lift.shiftIso hΦ n a a' h).hom.app X) =
      (G.commShiftIso n).hom.app _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫
        (F.shiftIso n a a' h).hom.app X ≫ (hΦ a).inv.app X := by
  simp [shiftIso]

end Lift

def lift : SingleFunctors C D A where
  functor := Φ
  shiftIso := Lift.shiftIso hΦ
  shiftIso_zero a := by
    ext X
    apply G.map_injective
    simp [Lift.map_shiftIso_hom_app, Functor.commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    apply G.map_injective
    dsimp
    rw [Lift.map_shiftIso_hom_app, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, assoc, assoc, assoc,
      id_comp, Functor.map_comp, Functor.map_comp, Lift.map_shiftIso_hom_app,
      Functor.commShiftIso_hom_naturality_assoc,
      Lift.map_shiftIso_hom_app, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, F.shiftIso_add n m a a' a'' ha' ha'', assoc, assoc, assoc]
    dsimp
    rw [id_comp, assoc, assoc, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc,
      ← (shiftFunctor E n).map_comp_assoc ((hΦ a').inv.app X),
      Iso.inv_hom_id_app, Functor.map_id, id_comp]
    rfl

def liftFunctorCompIso (a : A) :
    (lift F G Φ hΦ).functor a ⋙ G ≅ F.functor a :=
  hΦ a

instance [Preadditive C] [Preadditive D] [Preadditive E] [G.Additive] (a : A)
    [(F.functor a).Additive] : ((lift F G Φ hΦ).functor a).Additive := by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    rw [Functor.additive_iff_of_iso (liftFunctorCompIso F G Φ hΦ a)]
    infer_instance
  exact Functor.additive_of_comp_faithful _ G

-- TODO after postcomposition with `G`, `lift` becomes isomorphic to `F`

end SingleFunctors

end CategoryTheory
