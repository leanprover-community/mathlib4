/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.WidePullbackOfTerminal

/-!
# Extradegeneracy for the Cech object

Let `U : FormalCoproduct C`. Let `T` be a terminal object in `C`.
In this file, we construct an isomorphism from the Cech object `U.cech` that is
defined for objects in `FormalCoproduct` to the general Cech nerve construction
applied to the morphism from `U` to the terminal object.
This isomorphism is used in order to show that, as an augmented object (over `T`),
the Cech object `U.cech` has an extra degeneracy when there is a
morphism `T ⟶ U.obj i₀` for some `i₀`.

-/

@[expose] public section

universe w t v u

open Simplicial

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  (U : FormalCoproduct.{w} C) {T : C} (hT : IsTerminal T)

instance (n : ℕ) :
    HasWidePullback (Arrow.mk ((isTerminalIncl T hT).from U)).right
      (fun (_ : Fin (n + 1)) ↦ (Arrow.mk ((isTerminalIncl T hT).from U)).left)
      fun _ ↦ (Arrow.mk ((isTerminalIncl T hT).from U)).hom := by
  dsimp
  have : HasProduct fun (x : Fin (n + 1)) ↦ U := ⟨⟨_, U.isLimitPowerFan (Fin (n + 1))⟩⟩
  exact hasWidePullback_of_isTerminal _ (isTerminalIncl _ hT)

instance (n : SimplexCategory) :
    HasLimit (WidePullbackShape.wideCospan ((incl C).obj T) _
      fun (_ : ToType n) ↦ (isTerminalIncl T hT).from U) :=
  ⟨⟨_, WidePullbackCone.isLimitOfFan  _ (U.isLimitPowerFan _)
    (isTerminalIncl T hT)⟩⟩

/-- Auxiliary definition for `cechIsoCechNerve`. -/
noncomputable def cechIsoCechNerveApp (n : SimplexCategoryᵒᵖ) :
    U.cech.obj n ≅ (Arrow.cechNerve (Arrow.mk ((isTerminalIncl _ hT).from U))).obj n :=
  IsLimit.conePointUniqueUpToIso (WidePullbackCone.isLimitOfFan
    (arrows := fun _ ↦ (isTerminalIncl _ hT).from U)
    (U.isLimitPowerFan (ToType n.unop)) (isTerminalIncl _ hT)) (limit.isLimit _)

@[reassoc (attr := simp)]
lemma cechIsoCechNerveApp_hom_π (n : SimplexCategoryᵒᵖ) (i : ToType n.unop) :
    (U.cechIsoCechNerveApp hT n).hom ≫
      WidePullback.π (fun _ ↦ (isTerminalIncl T hT).from U) i = U.powerπ i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
lemma cechIsoCechNerveApp_inv_π (n : SimplexCategoryᵒᵖ) (i : ToType n.unop) :
    (U.cechIsoCechNerveApp hT n).inv ≫ U.powerπ i =
      WidePullback.π (fun _ ↦ (isTerminalIncl T hT).from U) i := by
  rw [← U.cechIsoCechNerveApp_hom_π hT, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The Cech construction for `FormalCoproduct` is isomorphic
to the general `Arrow.cechNerve` construction applied to the morphism
to the terminal object. -/
@[simps! hom_app inv_app]
noncomputable def cechIsoCechNerve :
    U.cech ≅ Arrow.cechNerve (Arrow.mk ((isTerminalIncl _ hT).from U)) :=
  NatIso.ofComponents (fun _ ↦ cechIsoCechNerveApp _ _ _)
    (fun f ↦ WidePullback.hom_ext _ _ _ (by simp) ((isTerminalIncl _ hT).hom_ext _ _))

/-- The Cech construction for `FormalCoproduct` is isomorphic
to the general `Arrow.augmentedCechNerve` construction applied to the morphism
to the terminal object. -/
@[simps! hom_left inv_left hom_right inv_left]
noncomputable def cechIsoAugmentedCechNerve :
    U.cech.augmentOfIsTerminal (isTerminalIncl _ hT) ≅
      Arrow.augmentedCechNerve (Arrow.mk ((isTerminalIncl _ hT).from U)) :=
  Comma.isoMk (U.cechIsoCechNerve hT) (Iso.refl _) (by
    ext : 1
    apply (isTerminalIncl _ hT).hom_ext)

/-- The Cech object of `U : FormalCoproduct C` has an extra degeneracy
when there is a morphism `T ⟶ U.obj i₀` from the terminal object. -/
noncomputable def extraDegeneracyCech {i₀ : U.I} (d : T ⟶ U.obj i₀) :
    (U.cech.augmentOfIsTerminal (isTerminalIncl _ hT)).ExtraDegeneracy :=
  .ofIso (U.cechIsoAugmentedCechNerve hT).symm
    (Arrow.AugmentedCechNerve.extraDegeneracy _
      { section_ := Hom.fromIncl i₀ d })

end CategoryTheory.Limits.FormalCoproduct
