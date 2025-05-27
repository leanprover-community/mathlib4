/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.CommGrp_

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence

This is true as long as `C` is additive.

Here, `C ⥤ₗ D` is the category of finite-limits-preserving functors from `C` to `D`.

To construct a functor from `C ⥤ₗ Type v` to `C ⥤ₗ AddCommGrp.{v}`, notice that a left-exact
functor `F : C ⥤ Type v` induces a functor `CommGrp_ C ⥤ CommGrp_ (Type v)`. But `CommGrp_ C` is
equivalent to `C`, and `CommGrp_ (Type v)` is equivalent to `AddCommGrp.{v}`, so we turn this
into a functor `C ⥤ AddCommGrp.{v}`. By construction, composing with with the forgetful
functor recovers the functor we started with, so since the forgetful functor reflects finite
limits and `F` preserves finite limits, our constructed functor also preserves finite limits. It
can be shown that this construction gives a quasi-inverse to the whiskering operation
`(C ⥤ₗ AddCommGrp.{v}) ⥤ (C ⥤ₗ Type v)`.
-/

open CategoryTheory MonoidalCategory Limits


universe v v' u u'

namespace AddCommGrp

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

namespace leftExactFunctorForgetEquivalence

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts
attribute [local instance] AddCommGrp.cartesianMonoidalCategoryAddCommGrp

private noncomputable local instance : CartesianMonoidalCategory C := .ofHasFiniteProducts

private noncomputable local instance : BraidedCategory C := .ofCartesianMonoidalCategory

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def inverseAux : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrp.{v} :=
  Functor.mapCommGrpFunctor ⋙ (whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
    (whiskeringRight _ _ _).obj
      (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

instance (F : C ⥤ₗ Type v) : PreservesFiniteLimits (inverseAux.obj F) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (inverseAux.obj F ⋙ forget AddCommGrp) :=
      inferInstanceAs (PreservesLimitsOfShape J F.1)
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrp)

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def inverse : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrp.{v}) :=
  ObjectProperty.lift _ inverseAux inferInstance

open scoped Mon_Class

attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
/-- Implementation, see `leftExactFunctorForgetEquivalence`.
This is the complicated bit, where we show that forgetting the group structure in the image of
`F` and then reconstructing it recovers the group structure we started with. -/
noncomputable def unitIsoAux (F : C ⥤ AddCommGrp.{v}) [PreservesFiniteLimits F] (X : C) :
    letI : (F ⋙ forget AddCommGrp).Braided := .ofChosenFiniteProducts _
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrp.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrp).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  letI : (F ⋙ forget AddCommGrp).Braided := .ofChosenFiniteProducts _
  letI : F.Monoidal := .ofChosenFiniteProducts _
  refine CommGrp_.mkIso Multiplicative.toAdd.toIso (by
    erw [Functor.mapCommGrp_obj_grp_one]
    aesop_cat) ?_
  dsimp [-Functor.comp_map, -ConcreteCategory.forget_map_eq_coe, -forget_map]
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  simp only [Category.id_comp]
  erw [Functor.mapCommGrp_obj_grp_mul]
  erw [Functor.comp_map, F.map_add, Functor.Monoidal.μ_comp F (forget AddCommGrp) X X,
    Category.assoc, ← Functor.map_comp, Preadditive.comp_add, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd]
  aesop_cat

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrp) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse :=
  NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrp.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrp.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrp.toAddCommGrp.mapIso
        (CommGrpTypeEquivalenceCommGrp.functor.mapIso (unitIsoAux F.obj X)))))

end leftExactFunctorForgetEquivalence

variable (C) in
/-- If `C` is an additive category, the forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is
an equivalence. -/
noncomputable def leftExactFunctorForgetEquivalence : (C ⥤ₗ AddCommGrp.{v}) ≌ (C ⥤ₗ Type v) where
  functor := (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := leftExactFunctorForgetEquivalence.inverse
  unitIso := leftExactFunctorForgetEquivalence.unitIso
  counitIso := Iso.refl _

end

end AddCommGrp
