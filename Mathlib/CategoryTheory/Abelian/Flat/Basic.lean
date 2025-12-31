/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Homology.LeftResolutions.Basic

/-!
# Flat objects

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

variable {A : Type*} [Category A]
  [MonoidalCategory A]

namespace ObjectProperty

def flat : ObjectProperty A := fun X ↦
  exactFunctor _ _ (tensorLeft X) ∧
    exactFunctor _ _ (tensorRight X)

namespace flat

variable {X : A}

protected lemma tensorLeft (hX : flat X) :
    exactFunctor _ _ (tensorLeft X) := hX.1

protected lemma tensorRight (hX : flat X) :
    exactFunctor _ _ (tensorRight X) := hX.2

instance : (flat (A := A)).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨(exactFunctor _ _).prop_of_iso
      ((curriedTensor A).mapIso e) h.1,
      (exactFunctor _ _).prop_of_iso
        ((curriedTensor A).flip.mapIso e) h.2⟩

attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits

instance : (flat (A := A)).IsMonoidal where
  prop_unit := by
    constructor <;> constructor
    · exact preservesFiniteLimits_of_natIso (leftUnitorNatIso A).symm
    · exact preservesFiniteColimits_of_natIso (leftUnitorNatIso A).symm
    · exact preservesFiniteLimits_of_natIso (rightUnitorNatIso A).symm
    · exact preservesFiniteColimits_of_natIso (rightUnitorNatIso A).symm
  prop_tensor := by
    rintro X Y hX hY
    have := hX.tensorLeft.preservesFiniteColimits
    have := hX.tensorLeft.preservesFiniteLimits
    have := hX.tensorRight.preservesFiniteColimits
    have := hX.tensorRight.preservesFiniteLimits
    have := hY.tensorLeft.preservesFiniteColimits
    have := hY.tensorLeft.preservesFiniteLimits
    have := hY.tensorRight.preservesFiniteColimits
    have := hY.tensorRight.preservesFiniteLimits
    constructor <;> constructor
    · exact preservesFiniteLimits_of_natIso (tensorLeftTensor X Y).symm
    · exact preservesFiniteColimits_of_natIso (tensorLeftTensor X Y).symm
    · exact preservesFiniteLimits_of_natIso (tensorRightTensor X Y).symm
    · exact preservesFiniteColimits_of_natIso (tensorRightTensor X Y).symm

end flat

end ObjectProperty

namespace Abelian

variable (A) in
abbrev HasFunctorialFlatResolutions : Prop :=
  Nonempty (LeftResolutions (ObjectProperty.flat.ι : _ ⥤ A))

lemma HasFunctorialFlatResolutions.mk {C : Type*} [Category C] {ι : C ⥤ A}
    [ι.Full] [ι.Faithful] (Λ : LeftResolutions ι) (hι : ι.essImage ≤ ObjectProperty.flat) :
    HasFunctorialFlatResolutions A := ⟨{
        F := ObjectProperty.lift _ (Λ.F ⋙ ι) (fun _ ↦ hι _ (ι.obj_mem_essImage _))
        π := Λ.π
        hπ := Λ.hπ
    }⟩

end Abelian

end CategoryTheory
