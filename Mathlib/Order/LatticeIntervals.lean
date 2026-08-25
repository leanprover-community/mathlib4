/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Order.Bounds.Basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions

In the following, `*` can represent either `c`, `o`, or `i`.
  * `Set.Ic*.orderBot`
  * `Set.Ii*.semilatticeInf`
  * `Set.I*c.orderTop`
  * `Set.I*c.semilatticeInf`
  * `Set.I**.lattice`
  * `Set.Iic.boundedOrder`, within an `OrderBot`
  * `Set.Ici.boundedOrder`, within an `OrderTop`
-/

public section


variable {α : Type*}

namespace Set

namespace Ico

@[to_dual]
instance semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy ↦ by
    rw [mem_Ico] at hx hy
    exact ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_inf [SemilatticeInf α] {a b : α} {x y : Ico a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[to_dual
/-- `Ioc a b` has a top element whenever `a < b`. -/]
instance orderBot [PartialOrder α] {a b : α} [Fact (a < b)] : OrderBot (Ico a b) :=
  (isLeast_Ico Fact.out).orderBot

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_bot [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊥ : Ico a b) = a := rfl

@[to_dual]
protected lemma disjoint_iff [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : Ico a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

end Ico

namespace Iio

@[to_dual]
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Iio a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

end Iio

namespace Iic

variable {a : α}

@[to_dual]
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_inf [SemilatticeInf α] {x y : Iic a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

@[to_dual]
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_sup [SemilatticeSup α] {x y : Iic a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

@[to_dual]
instance [Lattice α] : Lattice (Iic a) where

@[to_dual]
instance [DistribLattice α] : DistribLattice (Iic a) where
  le_sup_inf _ _ _ := le_sup_inf

@[to_dual]
instance orderTop [Preorder α] : OrderTop (Iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.prop

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_top [Preorder α] (a : α) : (⊤ : Iic a) = a := rfl

@[to_dual]
protected lemma eq_top_iff [Preorder α] {x : Iic a} :
    x = ⊤ ↔ (x : α) = a := by
  simp [Subtype.ext_iff]

@[to_dual]
instance orderBot [Preorder α] [OrderBot α] : OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_bot [Preorder α] [OrderBot α] (a : α) : (⊥ : Iic a) = (⊥ : α) := rfl

@[to_dual]
instance [Preorder α] [OrderBot α] : BoundedOrder (Iic a) where

@[to_dual]
protected lemma disjoint_iff [SemilatticeInf α] [OrderBot α] {x y : Iic a} :
    Disjoint x y ↔ Disjoint (x : α) (y : α) := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

@[to_dual]
protected lemma codisjoint_iff [SemilatticeSup α] {x y : Iic a} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = a := by
  simpa only [_root_.codisjoint_iff] using! Iic.eq_top_iff

@[to_dual]
protected lemma isCompl_iff [Lattice α] [OrderBot α] {x y : Iic a} :
    IsCompl x y ↔ Disjoint (x : α) (y : α) ∧ ↑x ⊔ ↑y = a := by
  rw [_root_.isCompl_iff, Iic.disjoint_iff, Iic.codisjoint_iff]

@[to_dual]
protected lemma complementedLattice_iff [Lattice α] [OrderBot α] :
    ComplementedLattice (Iic a) ↔ ∀ b, b ≤ a → ∃ c ≤ a, b ⊓ c = ⊥ ∧ b ⊔ c = a := by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]

end Iic

namespace Icc

variable {a b : α}

@[to_dual]
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun x y hx hy ↦ by
    rw [mem_Icc] at hx hy
    exact ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_inf [SemilatticeInf α] {x y : Icc a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

@[to_dual self]
instance lattice [Lattice α] : Lattice (Icc a b) where

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[to_dual
/-- `Icc a b` has a top element whenever `a ≤ b`. -/]
instance [Preorder α] [Fact (a ≤ b)] : OrderBot (Icc a b) :=
  (isLeast_Icc Fact.out).orderBot

@[to_dual (attr := simp, norm_cast)]
protected lemma coe_bot [Preorder α] (a b : α) [Fact (a ≤ b)] : ↑(⊥ : Icc a b) = a := rfl

/-- `Icc a b` is a `BoundedOrder` whenever `a ≤ b`. -/
@[to_dual self]
instance [Preorder α] [Fact (a ≤ b)] : BoundedOrder (Icc a b) where

@[to_dual]
protected lemma disjoint_iff [SemilatticeInf α] [Fact (a ≤ b)] {x y : Icc a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

@[to_dual none]
protected lemma isCompl_iff [Lattice α] [Fact (a ≤ b)] {x y : Icc a b} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ ↑x ⊔ ↑y = b := by
  rw [_root_.isCompl_iff, Icc.disjoint_iff, Icc.codisjoint_iff]

end Icc

end Set
