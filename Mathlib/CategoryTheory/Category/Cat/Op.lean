/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Opposites

/-!
# The dualizing functor on `Cat`

We define a (strict) functor `opFunctor` and an equivalence assigning opposite categories to
categories. We then show that this functor is strictly involutive and that it induces an
equivalence on `Cat`.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Cat

/-- The endofunctor `Cat ⥤ Cat` assigning to each category its opposite category. -/
@[simps]
def opFunctor : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where
  obj C := .of Cᵒᵖ
  map := Functor.op

/-- The natural isomorphism between the double application of `Cat.opFunctor` and the
identity functor on `Cat`. -/
@[simps!]
def opFunctorInvolutive : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _ :=
  NatIso.ofComponents (fun C => .mk (unopUnop C) (opOp C))

/-- The equivalence `Cat ≌ Cat` associating each category with its opposite category. -/
@[simps]
def opEquivalence : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.mk (opOp _) (unopUnop _))
  counitIso := NatIso.ofComponents (fun _ => Iso.mk (unopUnop _) (opOp _))

end Cat

end CategoryTheory
