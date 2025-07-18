/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
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

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {a b : α} {x y : Ico a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/-- `Ico a b` has a bottom element whenever `a < b`. -/
instance orderBot [PartialOrder α] {a b : α} [Fact (a < b)] : OrderBot (Ico a b) :=
  (isLeast_Ico Fact.out).orderBot

@[simp, norm_cast]
protected lemma coe_bot [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊥ : Ico a b) = a := rfl

protected lemma disjoint_iff [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : Ico a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

end Ico

namespace Iio

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Iio a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

end Iio

namespace Ioc

instance semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {a b : α} {x y : Ioc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/-- `Ioc a b` has a top element whenever `a < b`. -/
instance orderTop [PartialOrder α] {a b : α} [Fact (a < b)] : OrderTop (Ioc a b) :=
  (isGreatest_Ioc Fact.out).orderTop

@[simp, norm_cast]
protected lemma coe_top [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊤ : Ioc a b) = b := rfl

protected lemma codisjoint_iff [SemilatticeSup α] {a b : α} [Fact (a < b)] {x y : Ioc a b} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

end Ioc

namespace Ioi

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ioi a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

end Ioi

namespace Iic

variable {a : α}

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {x y : Iic a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {x y : Iic a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

instance [Lattice α] : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

instance orderTop [Preorder α] :
    OrderTop (Iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp, norm_cast]
protected lemma coe_top [Preorder α] (a : α) : (⊤ : Iic a) = a := rfl

protected lemma eq_top_iff [Preorder α] {x : Iic a} :
    x = ⊤ ↔ (x : α) = a := by
  simp [Subtype.ext_iff]

instance orderBot [Preorder α] [OrderBot α] :
    OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp, norm_cast]
protected lemma coe_bot [Preorder α] [OrderBot α] (a : α) : (⊥ : Iic a) = (⊥ : α) := rfl

instance [Preorder α] [OrderBot α] : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

protected lemma disjoint_iff [SemilatticeInf α] [OrderBot α] {x y : Iic a} :
    Disjoint x y ↔ Disjoint (x : α) (y : α) := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

protected lemma codisjoint_iff [SemilatticeSup α] {x y : Iic a} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = a := by
  simpa only [_root_.codisjoint_iff] using Iic.eq_top_iff

protected lemma isCompl_iff [Lattice α] [OrderBot α] {x y : Iic a} :
    IsCompl x y ↔ Disjoint (x : α) (y : α) ∧ ↑x ⊔ ↑y = a := by
  rw [_root_.isCompl_iff, Iic.disjoint_iff, Iic.codisjoint_iff]

protected lemma complementedLattice_iff [Lattice α] [OrderBot α] :
    ComplementedLattice (Iic a) ↔ ∀ b, b ≤ a → ∃ c ≤ a, b ⊓ c = ⊥ ∧ b ⊔ c = a := by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]

end Iic

namespace Ici

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Ici a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ici a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

instance lattice [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }

instance distribLattice [DistribLattice α] {a : α} : DistribLattice (Ici a) :=
  { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }

instance orderBot [Preorder α] {a : α} :
    OrderBot (Ici a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp, norm_cast]
protected lemma coe_bot [Preorder α] (a : α) : ↑(⊥ : Ici a) = a := rfl

instance orderTop [Preorder α] [OrderTop α] {a : α} :
    OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp, norm_cast]
protected lemma coe_top [Preorder α] [OrderTop α] (a : α) : ↑(⊤ : Ici a) = (⊤ : α) := rfl

instance boundedOrder [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

protected lemma disjoint_iff [SemilatticeInf α] {a : α} {x y : Ici a} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

protected lemma codisjoint_iff [SemilatticeSup α] [OrderTop α] {a : α} {x y : Ici a} :
    Codisjoint x y ↔ Codisjoint (x : α) (y : α) := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

protected lemma isCompl_iff [Lattice α] [OrderTop α] {a : α} {x y : Ici a} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ Codisjoint (x : α) (y : α) := by
  rw [_root_.isCompl_iff, Ici.disjoint_iff, Ici.codisjoint_iff]

end Ici

namespace Icc

variable {a b : α}

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[simp, norm_cast]
protected lemma coe_inf [SemilatticeInf α] {x y : Icc a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
protected lemma coe_sup [SemilatticeSup α] {x y : Icc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

instance lattice [Lattice α] : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
instance [Preorder α] [Fact (a ≤ b)] : OrderBot (Icc a b) :=
  (isLeast_Icc Fact.out).orderBot

@[simp, norm_cast]
protected lemma coe_bot [Preorder α] (a b : α) [Fact (a ≤ b)] : ↑(⊥ : Icc a b) = a := rfl

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
instance [Preorder α] [Fact (a ≤ b)] : OrderTop (Icc a b) :=
  (isGreatest_Icc Fact.out).orderTop

@[simp, norm_cast]
protected lemma coe_top [Preorder α] (a b : α) [Fact (a ≤ b)] : ↑(⊤ : Icc a b) = b := rfl

/-- `Icc a b` is a `BoundedOrder` whenever `a ≤ b`. -/
instance [Preorder α] [Fact (a ≤ b)] : BoundedOrder (Icc a b) where

protected lemma disjoint_iff [SemilatticeInf α] [Fact (a ≤ b)] {x y : Icc a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

protected lemma codisjoint_iff [SemilatticeSup α] [Fact (a ≤ b)] {x y : Icc a b} :
    Codisjoint x y ↔ ↑x ⊔ (y : α) = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

protected lemma isCompl_iff [Lattice α] [Fact (a ≤ b)] {x y : Icc a b} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ ↑x ⊔ ↑y = b := by
  rw [_root_.isCompl_iff, Icc.disjoint_iff, Icc.codisjoint_iff]

end Icc

end Set
