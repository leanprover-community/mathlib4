/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory Functor Opposite Limits Function GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  [∀ X : Sheaf J (Type v), PreservesFiniteProducts X.val]
  [HasWeakSheafify J (Type v)]

instance {n : ℕ} (S : Fin n → C) :
    PreservesColimit (Discrete.functor S) J.yoneda where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    let i : (J.yoneda.op ⋙ coyoneda ⋙
        ((evaluation (Sheaf J (Type v)) (Type (max u v))).obj X)) ≅ X.val ⋙ uliftFunctor :=
      Iso.trans
        (isoWhiskerRight (J.largeCurriedYonedaLemma) ((evaluation _ _ ).obj X))
        (NatIso.ofComponents
          (fun X ↦ Equiv.toIso (Equiv.trans Equiv.ulift Equiv.ulift.symm))
          (fun _ ↦  rfl))
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv i.symm this
    have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
    exact isLimitOfPreserves _ hc.op⟩

public instance Subcanonical.preservesFiniteCoproductsYoneda :
    PreservesFiniteCoproducts J.yoneda where
  preserves _ := { preservesColimit {S} :=
    let i : S ≅ Discrete.functor (fun i ↦ S.obj ⟨i⟩) := Discrete.natIso (fun _ ↦ Iso.refl _)
    preservesColimit_of_iso_diagram J.yoneda i.symm }
