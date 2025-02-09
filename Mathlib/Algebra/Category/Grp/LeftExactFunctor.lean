/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
import Mathlib.CategoryTheory.Preadditive.CommGrp_
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence
-/

open CategoryTheory Limits

universe v v' u u'


section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

@[simps!]
noncomputable def inverseAux : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrp.{v} :=
  Functor.mapCommGrpFunctor ⋙ (whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
    (whiskeringRight _ _ _).obj
      (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

instance (F : C ⥤ₗ Type v) : PreservesFiniteLimits (inverseAux.obj F) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (inverseAux.obj F ⋙ forget AddCommGrp) :=
      inferInstanceAs (PreservesLimitsOfShape J F.1)
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrp)

@[simps!]
noncomputable def inverse : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrp.{v}) :=
  FullSubcategory.lift _ inverseAux inferInstance

noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrp) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse := by
  refine NatIso.ofComponents
    (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X => ?_) ?_)) ?_
  · dsimp [inverse, inverseAux]
    
    refine AddEquiv.toAddCommGrpIso { Equiv.refl _ with map_add' := ?_ }
    simp
    intro x y
    sorry
  · sorry
  · sorry




noncomputable def forgetEquivalence : (C ⥤ₗ AddCommGrp.{v}) ≌ (C ⥤ₗ Type v) where
  functor := (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := inverse
  unitIso := unitIso
  counitIso := Iso.refl _
  functor_unitIso_comp := by aesop_cat

end
