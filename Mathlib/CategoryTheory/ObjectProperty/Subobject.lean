/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Subobjects satisfying a property of objects

Let `P` be a property of objects in a well-powered category with coproducts and images, so that
`Subobject X` has arbitrary suprema, and with equalizers, so that the map onto the image of a
morphism is an epimorphism. If `P` is closed under quotients and coproducts, then the supremum of
any set of subobjects satisfying `P` again satisfies `P`. In particular, every object `X` has a
greatest subobject satisfying `P`, namely `Subobject.sSup {A | P A}`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

section Sup

variable (P : ObjectProperty C)
  [P.IsClosedUnderQuotients] [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
  [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] [HasImages C] [HasEqualizers C]

/-- If `P` is closed under quotients and coproducts, then the supremum of a set of subobjects
satisfying `P` again satisfies `P`. In particular, together with `Subobject.le_sSup`, the
subobject `Subobject.sSup {A | P A}` is the greatest subobject of `X` satisfying `P`. -/
lemma prop_sSup {X : C} (s : Set (Subobject X)) (hs : ∀ A ∈ s, P (A : C)) :
    P (Subobject.sSup s) := by
  -- `Subobject.sSup s` is the image of the canonical map out of the coproduct of the
  -- members of `s`, so it is a quotient of a coproduct of objects satisfying `P`.
  apply P.prop_of_iso (Subobject.underlyingIso (image.ι (Subobject.smallCoproductDesc _))).symm
  apply P.prop_of_epi (factorThruImage _)
  apply prop_colimit
  rintro ⟨⟨_, S, hS, rfl⟩⟩
  simpa using hs S hS

end Sup

end ObjectProperty

end CategoryTheory
