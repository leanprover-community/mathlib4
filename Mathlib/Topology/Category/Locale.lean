/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Category.CompHaus.Frm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

@[expose] public section


universe u

open CategoryTheory Opposite Order TopologicalSpace


/-- The category of locales. -/
def Locale :=
  Frmᵒᵖ deriving LargeCategory

namespace Locale

instance : CoeSort Locale Type* :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `Frame`. -/
def of (α : Type*) [Frame α] : Locale :=
  op <| Frm.of α

@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl

instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps!]
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp

-- Note, `CompHaus` is too strong. We only need `T0Space`.
instance CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful :=
  ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩
