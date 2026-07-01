/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.Preord.CartesianClosed
public import Mathlib.Data.Sum.Order
public import Mathlib.CategoryTheory.Distributive.Cartesian

/-!
# `Preord` is a distributive category

`Preord` has finite coproducts given by the sum order, and since it is Cartesian closed the tensor
product preserves them, so `Preord` is a Cartesian distributive category.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace Preord

/-- The empty preorder is initial in `Preord`. -/
def isInitialPEmpty : IsInitial (of PEmpty.{u + 1}) :=
  .ofUniqueHom (fun _ => ofHom ⟨fun x => x.elim, nofun⟩) fun _ _ => ext nofun

instance : HasInitial Preord.{u} := isInitialPEmpty.hasInitial

/-- The binary coproduct of preorders is their sum order. -/
def binaryCoproductColimitCocone (A B : Preord.{u}) : ColimitCocone (pair A B) where
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

instance (A B : Preord.{u}) : HasColimit (pair A B) :=
  HasColimit.mk (binaryCoproductColimitCocone A B)

instance : HasBinaryCoproducts Preord.{u} := hasBinaryCoproducts_of_hasColimit_pair _

instance : IsMonoidalLeftDistrib Preord.{u} where
  preservesBinaryCoproducts_tensorLeft A :=
    inferInstanceAs (PreservesColimitsOfShape _ (tensorLeft A))

instance : IsCartesianDistributive Preord.{u} :=
  .of_isMonoidalLeftDistrib _

end Preord
