/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite
import Mathlib.Order.Category.FinPartOrd
import Mathlib.Order.Category.LinOrd
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono


/-!
# Finite linear orders

This defines `FinLinOrd`, the category of  finite linear
orders with monotone maps.

The skelton of `FinLinOrd` is `AugmentedSimplexCategory`.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

/-- A typeclass for  finite linear orders. -/
class FiniteLinearOrder (α : Type*) extends Fintype α, LinearOrder α

instance Fin.FiniteLinearOrder (n : ℕ) : FiniteLinearOrder (Fin n) where

/-- The category of  finte linear orders. -/
def FinLinOrd :=
  Bundled FiniteLinearOrder


namespace FinLinOrd
instance : BundledHom.ParentProjection @FiniteLinearOrder.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory for FinLinOrd

instance : ConcreteCategory FinLinOrd :=
  BundledHom.concreteCategory _

instance : CoeSort FinLinOrd Type* :=
  Bundled.coeSort

/-- Construct a bundled `FinLinOrd` from the underlying type and typeclass. -/
def of (α : Type*) [FiniteLinearOrder α] : FinLinOrd :=
  Bundled.of α


theorem coe_of (α : Type*) [FiniteLinearOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinLinOrd :=
  ⟨of (Fin (0))⟩

instance hasForgetToLinOrd : HasForget₂ FinLinOrd LinOrd :=
  BundledHom.forget₂ _ _

instance (α : FinLinOrd) : FiniteLinearOrder α :=
  α.str

instance {A B : FinLinOrd.{u}} : OrderHomClass (A ⟶ B) A B where
  coe f := ⇑(show OrderHom A B from f)
  coe_injective' _ _ h := by
    ext x
    exact congr_fun h x
  map_rel f _ _ h := f.monotone h

instance (X : FinLinOrd): Inhabited (Fin 0 ⟶ X) :=
   ⟨(@OrderEmbedding.ofIsEmpty (Fin 0) (X)).toOrderHom⟩


instance (X : FinLinOrd) : Unique ((of (Fin 0)) ⟶ X) where
  default := (@OrderEmbedding.ofIsEmpty (Fin 0) (X)).toOrderHom
  uniq := by {
    intro a
    apply OrderHom.ext
    exact List.ofFn_inj.mp rfl
  }
/-- The object `Fin 0` is initial in `FinLinOrd`-/
def finZeroIsInitial  : IsInitial (of (Fin 0)) := by
    refine (@IsInitial.ofUnique FinLinOrd (?_) (of (Fin 0)) (?_))
    intro Y
    infer_instance



end FinLinOrd
