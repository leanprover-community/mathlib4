/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Lift of a "single functor" to a full subcategory

Let `C`, `D` and `E` be categories. Let `A` be an additive monoid.
Assume that `D` and `E` have shifts by `A` and that we have
a fully faithful functor `G : D ⥤ A` which commutes with shifts.
Given `F : SingleFunctors C E A`, and a family of functors
`Φ a : C ⥤ D` with isomorphisms `Φ a ⋙ G ≅ F.functor a` for all `a : A`,
we lift `F` in `SingleFunctor C D A`.

-/

@[expose] public section

namespace CategoryTheory

open Category Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {A : Type*} [AddMonoid A] [HasShift D A] [HasShift E A]
  (F : SingleFunctors C E A) (G : D ⥤ E) [G.CommShift A]
  [G.Full] [G.Faithful] (Φ : A → C ⥤ D) (hΦ : ∀ a, Φ a ⋙ G ≅ F.functor a)

namespace SingleFunctors

namespace lift

variable {F G Φ}

/-- Auxiliary definition for `SingleFunctors.lift`. -/
@[irreducible]
noncomputable def shiftIso (n a a' : A) (h : n + a = a') :
    Φ a' ⋙ shiftFunctor D n ≅ Φ a :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

private lemma map_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) :
    dsimp% G.map ((lift.shiftIso hΦ n a a' h).hom.app X) =
      (G.commShiftIso n).hom.app _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫
        (F.shiftIso n a a' h).hom.app X ≫ (hΦ a).inv.app X := by
  simp [shiftIso]

end lift

/-- Let `C`, `D` and `E` be categories. Let `A` be an additive monoid.
Assume that `D` and `E` have shifts by `A` and that we have
a fully faithful functor `G : D ⥤ A` which commutes with shifts.
Given `F : SingleFunctors C E A`, and a family of functors
`Φ a : C ⥤ D` with isomorphisms `Φ a ⋙ G ≅ F.functor a` for all `a : A`,
this is a term in `SingleFunctors C D A` which is given by the functors `Φ a`
for all `a`. -/
@[simps functor]
noncomputable def lift : SingleFunctors C D A where
  functor := Φ
  shiftIso := lift.shiftIso hΦ
  shiftIso_zero a := by
    ext X
    apply G.map_injective
    dsimp
    rw [lift.map_shiftIso_hom_app, Functor.commShiftIso_zero,
      CommShift.isoZero_hom_app, shiftIso_zero_hom_app, assoc,
      dsimp% NatIso.naturality_1_assoc (shiftFunctorZero E A) ((hΦ a).hom.app X),
      dsimp% (hΦ a).hom_inv_id_app X, comp_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    apply G.map_injective
    dsimp
    rw [lift.map_shiftIso_hom_app, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, assoc, assoc, assoc,
      id_comp, Functor.map_comp, Functor.map_comp, lift.map_shiftIso_hom_app,
      Functor.commShiftIso_hom_naturality_assoc,
      lift.map_shiftIso_hom_app, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, F.shiftIso_add n m a a' a'' ha' ha'', assoc, assoc, assoc]
    dsimp
    rw [id_comp, assoc, assoc,
      dsimp% NatIso.naturality_1_assoc (shiftFunctorAdd E m n) ((hΦ a'').hom.app X)]
    rw [← dsimp% (shiftFunctor E n).map_comp_assoc ((hΦ a').inv.app X),
      dsimp% (hΦ a').inv_hom_id_app X]
    simp

@[reassoc]
lemma map_lift_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) :
    dsimp% G.map (((lift F G Φ hΦ).shiftIso n a a' h).hom.app X) =
      (G.commShiftIso n).hom.app _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫
        (F.shiftIso n a a' h).hom.app X ≫ (hΦ a).inv.app X :=
  lift.map_shiftIso_hom_app ..

/-- After postcomposition with the fully faithful functor `G`,
`lift F G Φ hΦ` becomes isomorphic to `F`. -/
@[simps!]
noncomputable def liftPostcompIso : (lift F G Φ hΦ).postcomp G ≅ F :=
  isoMk (hΦ) (fun n a a' ha' ↦ by
    ext X
    have := (hΦ a).inv_hom_id_app X
    dsimp at this
    simp [map_lift_shiftIso_hom_app, this])

instance [Preadditive C] [Preadditive D] [Preadditive E] [G.Additive] (a : A)
    [(F.functor a).Additive] : ((lift F G Φ hΦ).functor a).Additive := by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    dsimp
    rwa [Functor.additive_iff_of_iso (hΦ a)]
  exact Functor.additive_of_comp_faithful _ G

end SingleFunctors

end CategoryTheory
