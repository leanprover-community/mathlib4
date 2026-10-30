/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Flat objects

If `A` is a monoidal category, we introduce a property of objects
`ObjectProperty.flat : ObjectProperty A` which is satisfied by
objects `X : A` such that both functors `tensorLeft X : A ⥤ A` and
`tensorRight X : A ⥤ A` are exact (i.e. preserve both finite limits
and finite colimits).

Moreover, if `A` is an abelian category, we introduce a typeclass
`Abelian.HasFunctorialFlatResolution A` which says that objects in `A`
admit a functorial epimorphism from a flat object.

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

variable {A : Type*} [Category* A] [MonoidalCategory A]

namespace ObjectProperty

/-- In a monoidal category `A`, this is the property of objects `X` such that
both functors `tensorLeft X : A ⥤ A` and `tensorRight X : A ⥤ A` preserve
both finite limits and finite colimits. -/
def flat : ObjectProperty A :=
  fun X ↦ exactFunctor _ _ (tensorLeft X) ∧ exactFunctor _ _ (tensorRight X)

lemma flat_eq_min :
    flat (A := A) =
      (exactFunctor A A).inverseImage (curriedTensor A) ⊓
      (exactFunctor A A).inverseImage (curriedTensor A).flip := rfl

namespace flat

protected lemma tensorLeft {X : A} (hX : flat X) :
    exactFunctor _ _ (tensorLeft X) := hX.1

protected lemma tensorRight {X : A} (hX : flat X) :
    exactFunctor _ _ (tensorRight X) := hX.2

instance : (flat (A := A)).IsClosedUnderIsomorphisms := by
  rw [flat_eq_min]
  infer_instance

instance : (flat (A := A)).IsStableUnderRetracts := by
  rw [flat_eq_min]
  infer_instance

instance : (flat (A := A)).IsMonoidal where
  prop_unit := by
    constructor <;> constructor
    · exact preservesFiniteLimits_of_natIso (leftUnitorNatIso A).symm
    · exact preservesFiniteColimits_of_natIso (leftUnitorNatIso A).symm
    · exact preservesFiniteLimits_of_natIso (rightUnitorNatIso A).symm
    · exact preservesFiniteColimits_of_natIso (rightUnitorNatIso A).symm
  prop_tensor := fun X Y ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ ↦ by
    constructor <;> constructor
    · exact preservesFiniteLimits_of_natIso (tensorLeftTensor X Y).symm
    · exact preservesFiniteColimits_of_natIso (tensorLeftTensor X Y).symm
    · exact preservesFiniteLimits_of_natIso (tensorRightTensor X Y).symm
    · exact preservesFiniteColimits_of_natIso (tensorRightTensor X Y).symm

end flat

end ObjectProperty

namespace Abelian

variable (A) in
/-- A monoidal abelian category has functorial flat resolutions if all objects
admit a functorial epimorphism from a flat object. -/
abbrev HasFunctorialFlatResolution : Prop :=
  Nonempty (LeftResolution (ObjectProperty.flat.ι : _ ⥤ A))

lemma HasFunctorialFlatResolution.mk {C : Type*} [Category* C] {ι : C ⥤ A}
    (Λ : LeftResolution ι) (hι : ι.essImage ≤ ObjectProperty.flat) :
    HasFunctorialFlatResolution A :=
  ⟨{F := ObjectProperty.lift _ (Λ.F ⋙ ι) (fun _ ↦ hι _ (ι.obj_mem_essImage _))
    π := Λ.π }⟩

end Abelian

end CategoryTheory
