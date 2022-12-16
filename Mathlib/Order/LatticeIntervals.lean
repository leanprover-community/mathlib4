/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
! This file was ported from Lean 3 source module order.lattice_intervals
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Bounds.Basic

/-!
# Intervals in Lattices
In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.
## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.order_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.order_top`
  * `set.I*c.semillatice_inf`
  * `set.I**.lattice`
  * `set.Iic.bounded_order`, within an `order_bot`
  * `set.Ici.bounded_order`, within an `order_top`
-/


variable {α : Type _}

namespace Set

namespace IcoCat

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible]
protected def orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (ico a b) :=
  (is_least_Ico h).OrderBot
#align set.Ico.order_bot Set.ico.orderBot

end IcoCat

namespace IioCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_lt inf_le_left hx

end IioCat

namespace IocCat

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible]
protected def orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (ioc a b) :=
  (is_greatest_Ioc h).OrderTop
#align set.Ioc.order_top Set.ioc.orderTop

end IocCat

namespace IoiCat

instance [SemilatticeSup α] {a : α} : SemilatticeSup (ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_le hx le_sup_left

end IoiCat

namespace IicCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (iic a) :=
  Subtype.semilatticeInf fun x y hx hy => le_trans inf_le_left hx

instance [SemilatticeSup α] {a : α} : SemilatticeSup (iic a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance [Lattice α] {a : α} : Lattice (iic a) :=
  { iic.semilatticeInf, iic.semilatticeSup with }

instance [Preorder α] {a : α} :
    OrderTop (iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.Prop

@[simp]
theorem coe_top [Preorder α] {a : α} : ↑(⊤ : iic a) = a :=
  rfl
#align set.Iic.coe_top Set.iic.coe_top

instance [Preorder α] [OrderBot α] {a : α} :
    OrderBot (iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp]
theorem coe_bot [Preorder α] [OrderBot α] {a : α} : ↑(⊥ : iic a) = (⊥ : α) :=
  rfl
#align set.Iic.coe_bot Set.iic.coe_bot

instance [Preorder α] [OrderBot α] {a : α} : BoundedOrder (iic a) :=
  { iic.orderTop, iic.orderBot with }

end IicCat

namespace IciCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (ici a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance [SemilatticeSup α] {a : α} : SemilatticeSup (ici a) :=
  Subtype.semilatticeSup fun x y hx hy => le_trans hx le_sup_left

instance [Lattice α] {a : α} : Lattice (ici a) :=
  { ici.semilatticeInf, ici.semilatticeSup with }

instance [DistribLattice α] {a : α} : DistribLattice (ici a) :=
  { ici.lattice with le_sup_inf := fun a b c => le_sup_inf }

instance [Preorder α] {a : α} :
    OrderBot (ici a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.Prop

@[simp]
theorem coe_bot [Preorder α] {a : α} : ↑(⊥ : ici a) = a :=
  rfl
#align set.Ici.coe_bot Set.ici.coe_bot

instance [Preorder α] [OrderTop α] {a : α} :
    OrderTop (ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp]
theorem coe_top [Preorder α] [OrderTop α] {a : α} : ↑(⊤ : ici a) = (⊤ : α) :=
  rfl
#align set.Ici.coe_top Set.ici.coe_top

instance [Preorder α] [OrderTop α] {a : α} : BoundedOrder (ici a) :=
  { ici.orderTop, ici.orderBot with }

end IciCat

namespace IccCat

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (icc a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (icc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance [Lattice α] {a b : α} : Lattice (icc a b) :=
  { icc.semilatticeInf, icc.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[reducible]
protected def orderBot [Preorder α] {a b : α} (h : a ≤ b) : OrderBot (icc a b) :=
  (is_least_Icc h).OrderBot
#align set.Icc.order_bot Set.icc.orderBot

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
@[reducible]
protected def orderTop [Preorder α] {a b : α} (h : a ≤ b) : OrderTop (icc a b) :=
  (is_greatest_Icc h).OrderTop
#align set.Icc.order_top Set.icc.orderTop

/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
@[reducible]
protected def boundedOrder [Preorder α] {a b : α} (h : a ≤ b) : BoundedOrder (icc a b) :=
  { icc.orderTop h, icc.orderBot h with }
#align set.Icc.bounded_order Set.icc.boundedOrder

end IccCat

end Set
