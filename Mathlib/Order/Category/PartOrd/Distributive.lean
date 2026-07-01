/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd.CartesianClosed
public import Mathlib.Data.Sum.Order
public import Mathlib.CategoryTheory.Distributive.Cartesian

/-!
# `PartOrd` is a distributive category

`PartOrd` has finite coproducts given by the sum order, and since it is Cartesian closed the tensor
product preserves them, so `PartOrd` is a Cartesian distributive category.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace PartOrd

/-- The empty partial order is initial in `PartOrd`. -/
def isInitialPEmpty : IsInitial (of PEmpty.{u + 1}) :=
  .ofUniqueHom (fun _ => ofHom ⟨fun x => x.elim, nofun⟩) fun _ _ => ext nofun

instance : HasInitial PartOrd.{u} := isInitialPEmpty.hasInitial

/-- The binary coproduct of partial orders is their sum order. -/
def binaryCoproductColimitCocone (A B : PartOrd.{u}) : ColimitCocone (pair A B) where
  cocone := BinaryCofan.mk (P := of (A ⊕ B))
    (ofHom ⟨Sum.inl, fun _ _ => Sum.LiftRel.inl⟩) (ofHom ⟨Sum.inr, fun _ _ => Sum.LiftRel.inr⟩)
  isColimit := BinaryCofan.isColimitMk
    (fun s => ofHom ⟨Sum.elim s.inl s.inr, by
      rintro (_ | _) (_ | _) (h | h)
      · exact s.inl.hom.monotone h
      · exact s.inr.hom.monotone h⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h₁ h₂ => by
      ext (a | b)
      · exact congrArg (·.hom a) h₁
      · exact congrArg (·.hom b) h₂)

instance (A B : PartOrd.{u}) : HasColimit (pair A B) :=
  HasColimit.mk (binaryCoproductColimitCocone A B)

instance : HasBinaryCoproducts PartOrd.{u} := hasBinaryCoproducts_of_hasColimit_pair _

instance : IsMonoidalLeftDistrib PartOrd.{u} where
  preservesBinaryCoproducts_tensorLeft A :=
    inferInstanceAs (PreservesColimitsOfShape _ (tensorLeft A))

instance : IsCartesianDistributive PartOrd.{u} :=
  .of_isMonoidalLeftDistrib _

end PartOrd
