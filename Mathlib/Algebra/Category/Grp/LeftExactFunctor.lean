/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
import Mathlib.CategoryTheory.Preadditive.CommGrp_
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.Grp.ChosenFiniteProducts

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence
-/

open CategoryTheory MonoidalCategory Limits

universe v v' u u'

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts

noncomputable local instance : ChosenFiniteProducts C :=
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

/-- Implementation, see `forgetEquivalence`. -/
noncomputable def preIso (F : C ⥤ AddCommGrp.{v}) [PreservesFiniteLimits F] (X : C) :
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrp.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrp).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  refine CommGrp_.mkIso ?_ ?_ ?_
  · dsimp
    exact Multiplicative.toAdd.toIso
  · dsimp
    ext x
    simp
    erw [toAdd_one]
  · dsimp [-ConcreteCategory.forget_map_eq_coe, -AddCommGrp.forget_map, -Functor.comp_map]
    have : HasZeroObject AddCommGrp.{v} := hasZeroObject_of_hasTerminal_object
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    rw [Functor.comp_map, F.map_add,
      Functor.Monoidal.μ_comp F (forget AddCommGrp.{v}) (X := X) (Y := X),
      Category.assoc, ← Functor.map_comp, Preadditive.comp_add, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd]
    ext ⟨p, q⟩
    simp
    erw [toAdd_mul]
    simp only [AddCommGrp.μ_forget_apply]
    rfl

/-- Implementation, see `forgetEquivalence`. -/
noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrp) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse := by
  refine NatIso.ofComponents
    (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X => ?_) ?_)) ?_
  · dsimp [inverse, inverseAux]
    let q :=
      CommGrp.toAddCommGrp.mapIso (CommGrpTypeEquivalenceCommGrp.functor.mapIso (preIso F.obj X))
    refine ?_ ≪≫ q
    refine ?_ ≪≫ (CommGrp.toAddCommGrp.mapIso
      (commGrpTypeEquivalenceCommGrp.counitIso.app (AddCommGrp.toCommGrp.obj (F.obj.obj X)))).symm
    exact commGroupAddCommGroupEquivalence.counitIso.app _
  · aesop_cat
  · aesop_cat

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
