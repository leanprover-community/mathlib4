/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Order.Bounds.Basic

#align_import order.lattice_intervals from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions

In the following, `*` can represent either `c`, `o`, or `i`.
  * `Set.Ic*.orderBot`
  * `Set.Ii*.semillaticeInf`
  * `Set.I*c.orderTop`
  * `Set.I*c.semillaticeInf`
  * `Set.I**.lattice`
  * `Set.Iic.boundedOrder`, within an `OrderBot`
  * `Set.Ici.boundedOrder`, within an `OrderTop`
-/


variable {α : Type*}

namespace Set

namespace Ico

instance semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
protected abbrev orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (Ico a b) :=
  (isLeast_Ico h).orderBot
#align set.Ico.order_bot Set.Ico.orderBot

end Ico

namespace Iio

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

end Iio

namespace Ioc

instance semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
protected abbrev orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (Ioc a b) :=
  (isGreatest_Ioc h).orderTop
#align set.Ioc.order_top Set.Ioc.orderTop

end Ioc

namespace Ioi

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

end Ioi

namespace Iic

variable {a : α}

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {x y : Iic a} :
    (↑(x ⊓ y) : α) = (x : α) ⊓ (y : α) :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {x y : Iic a} :
    (↑(x ⊔ y) : α) = (x : α) ⊔ (y : α) :=
  rfl

instance [Lattice α] : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

instance orderTop [Preorder α] :
    OrderTop (Iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp]
theorem coe_top [Preorder α] : (⊤ : Iic a) = a :=
  rfl
#align set.Iic.coe_top Set.Iic.coe_top

protected lemma eq_top_iff [Preorder α] {x : Iic a} :
    x = ⊤ ↔ (x : α) = a := by
  simp [Subtype.ext_iff]

instance orderBot [Preorder α] [OrderBot α] :
    OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp]
theorem coe_bot [Preorder α] [OrderBot α] : (⊥ : Iic a) = (⊥ : α) :=
  rfl
#align set.Iic.coe_bot Set.Iic.coe_bot

instance [Preorder α] [OrderBot α] : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

protected lemma disjoint_iff [SemilatticeInf α] [OrderBot α] {x y : Iic a} :
    Disjoint x y ↔ Disjoint (x : α) (y : α) := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

protected lemma codisjoint_iff [SemilatticeSup α] {x y : Iic a} :
    Codisjoint x y ↔ (x : α) ⊔ (y : α) = a := by
  simpa only [_root_.codisjoint_iff] using Iic.eq_top_iff

protected lemma isCompl_iff [Lattice α] [BoundedOrder α] {x y : Iic a} :
    IsCompl x y ↔ Disjoint (x : α) (y : α) ∧ (x : α) ⊔ (y : α) = a := by
  rw [_root_.isCompl_iff, Iic.disjoint_iff, Iic.codisjoint_iff]

end Iic

namespace Ici

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

instance lattice [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }

instance distribLattice [DistribLattice α] {a : α} : DistribLattice (Ici a) :=
  { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }

instance orderBot [Preorder α] {a : α} :
    OrderBot (Ici a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp]
theorem coe_bot [Preorder α] {a : α} : ↑(⊥ : Ici a) = a :=
  rfl
#align set.Ici.coe_bot Set.Ici.coe_bot

instance orderTop [Preorder α] [OrderTop α] {a : α} :
    OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp]
theorem coe_top [Preorder α] [OrderTop α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) :=
  rfl
#align set.Ici.coe_top Set.Ici.coe_top

instance boundedOrder [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

end Ici

namespace Icc

instance semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

instance semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance lattice [Lattice α] {a b : α} : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
protected abbrev orderBot [Preorder α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) :=
  (isLeast_Icc h).orderBot
#align set.Icc.order_bot Set.Icc.orderBot

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
protected abbrev orderTop [Preorder α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) :=
  (isGreatest_Icc h).orderTop
#align set.Icc.order_top Set.Icc.orderTop

/-- `Icc a b` is a `BoundedOrder` whenever `a ≤ b`. -/
protected abbrev boundedOrder [Preorder α] {a b : α} (h : a ≤ b) : BoundedOrder (Icc a b) :=
  { Icc.orderTop h, Icc.orderBot h with }
#align set.Icc.bounded_order Set.Icc.boundedOrder

end Icc

end Set
