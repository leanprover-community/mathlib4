/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.ExactCategory.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The Grothendieck group of an exact category

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

namespace ExactCategory

namespace GrothendieckGroup

inductive relations : FreeAbelianGroup C → Prop
  | ofShortExact (S : ShortComplex C) (hS : shortExact C S) :
      relations (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃ -
        FreeAbelianGroup.of S.X₂)

end GrothendieckGroup

def GrothendieckGroup :=
  FreeAbelianGroup C ⧸ AddSubgroup.closure (.ofPred (GrothendieckGroup.relations C))

instance : AddCommGroup (GrothendieckGroup C) := by
  dsimp [GrothendieckGroup]
  infer_instance

variable {C}

namespace GrothendieckGroup

def of (X : C) : GrothendieckGroup C :=
  QuotientAddGroup.mk' _ (FreeAbelianGroup.of X)

lemma additivity (S : ShortComplex C) (hS : shortExact C S) :
    of S.X₂ = of S.X₁ + of S.X₃ := by
  symm
  rw [← sub_eq_zero]
  apply (QuotientAddGroup.eq_zero_iff _).2
  apply AddSubgroup.subset_closure
  exact relations.ofShortExact S hS

@[simp]
lemma of_biprod (X₁ X₂ : C) :
    of (X₁ ⊞ X₂) = of X₁ + of X₂ :=
  additivity _ (binaryBiproduct_shortExact X₁ X₂)

lemma of_eq_zero_of_isZero (X : C) (hX : IsZero X) :
    of X = 0 := by
  simpa using additivity (ShortComplex.mk (𝟙 X) (𝟙 X) (hX.eq_of_src _ _))
    (shortExact_of_isZero _ hX hX hX)

variable (C)

@[simp]
lemma of_zero : of (0 : C) = 0 :=
  of_eq_zero_of_isZero _ (isZero_zero C)

variable {C}

lemma of_eq_of_iso {X Y : C} (e : X ≅ Y) :
    of X = of Y := by
  simpa using additivity (ShortComplex.mk (0 : 0 ⟶ X) e.hom zero_comp)
    (shortExact_of_isZero_of_isIso _ (isZero_zero C) (by dsimp; infer_instance))

end GrothendieckGroup

end ExactCategory

end CategoryTheory
