/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.ChosenFiniteProducts
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.CommGrp_

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence

We construct a quasi-inverse for the 
-/

open CategoryTheory MonoidalCategory Limits

universe v v' u u'

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts

private noncomputable local instance : ChosenFiniteProducts C :=
  ChosenFiniteProducts.ofFiniteProducts _

/-- Implementation, see `forgetEquivalence`. -/
noncomputable def inverseAux : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrp.{v} :=
  Functor.mapCommGrpFunctor ⋙ (whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
    (whiskeringRight _ _ _).obj
      (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

instance (F : C ⥤ₗ Type v) : PreservesFiniteLimits (inverseAux.obj F) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (inverseAux.obj F ⋙ forget AddCommGrp) :=
      inferInstanceAs (PreservesLimitsOfShape J F.1)
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrp)

/-- Implementation, see `forgetEquivalence`. -/
noncomputable def inverse : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrp.{v}) :=
  FullSubcategory.lift _ inverseAux inferInstance

/-- Implementation, see `forgetEquivalence`.
This is the complicated bit, where we show that forgetting the group structure in the image of
`F` and then reconstructing it recovers the group structure we started with. -/
noncomputable def unitIsoAux (F : C ⥤ AddCommGrp.{v}) [PreservesFiniteLimits F] (X : C) :
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrp.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrp).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  refine CommGrp_.mkIso Multiplicative.toAdd.toIso (by aesop_cat) ?_
  dsimp [-Functor.comp_map]
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  rw [Functor.comp_map, F.map_add,
    Functor.Monoidal.μ_comp F (forget AddCommGrp.{v}) (X := X) (Y := X),
    Category.assoc, ← Functor.map_comp, Preadditive.comp_add, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd]
  aesop_cat

/-- Implementation, see `forgetEquivalence`. -/
noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrp) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse :=
  NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrp.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrp.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrp.toAddCommGrp.mapIso
        (CommGrpTypeEquivalenceCommGrp.functor.mapIso (unitIsoAux F.obj X)))))

/-- To construct a functor from `C ⥤ₗ Type v` to `C ⥤ₗ AddCommGrp.{v}`, notice that a left-exact
functor `F : C ⥤ Type v` induces a functor `CommGrp_ C ⥤ CommGrp_ (Type v)`. But `CommGrp_ C` is
equivalent to `C`, and `CommGrp_ (Type v)` is equivalent to `AddCommGrp.{v}`, so we turn this
into a functor `C ⥤ AddCommGrp.{v}`. By construction, composing with with the forgetful
functor recovers the functor we started with, so since the forgetful functor reflects finite
limits and `F` preserves finite limits, our constructed functor also preserves finite limits. It
can be shown that this construction gives a quasi-inverse to the whiskering operation
`(C ⥤ₗ AddCommGrp.{v}) ⥤ (C ⥤ₗ Type v)`. -/
noncomputable def forgetEquivalence : (C ⥤ₗ AddCommGrp.{v}) ≌ (C ⥤ₗ Type v) where
  functor := (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := inverse
  unitIso := unitIso
  counitIso := Iso.refl _

end
