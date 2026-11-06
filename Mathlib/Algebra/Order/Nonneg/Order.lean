/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Nonneg.Defs
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Lift

/-!
# Order structure on the type of nonnegative elements

This file endows `Nonneg M` with the order inherited from `M`.
-/

public section

variable {M : Type*}

namespace Nonneg

section Preorder
variable [Zero M] [Preorder M] {a b : Nonneg M} {x y : M}

instance instPreorder : Preorder (Nonneg M) := fast_instance% Preorder.lift val

@[simp, norm_cast, gcongr] lemma coe_le_coe : (a : M) ≤ b ↔ a ≤ b := .rfl

@[simp, norm_cast, gcongr] lemma coe_lt_coe : (a : M) < b ↔ a < b := .rfl

@[simp, gcongr] lemma mk_le_mk {hx : 0 ≤ x} {hy : 0 ≤ y} :
    (⟨x, hx⟩ : Nonneg M) ≤ ⟨y, hy⟩ ↔ x ≤ y := .rfl

@[simp, gcongr] lemma mk_lt_mk {hx : 0 ≤ x} {hy : 0 ≤ y} :
    (⟨x, hx⟩ : Nonneg M) < ⟨y, hy⟩ ↔ x < y := .rfl

instance inhabited : Inhabited (Nonneg M) := ⟨⟨0, le_rfl⟩⟩

instance decidableLE [h : DecidableLE M] : DecidableLE (Nonneg M) := fun a b ↦ h a b

instance decidableLT [h : DecidableLT M] : DecidableLT (Nonneg M) := fun a b ↦ h a b

end Preorder

section LE
variable [Zero M] [LE M]

instance canLift : CanLift M (Nonneg M) val (0 ≤ ·) where prf x hx := ⟨⟨x, hx⟩, rfl⟩

end LE

variable [Zero M]

instance instPartialOrder [PartialOrder M] : PartialOrder (Nonneg M) :=
  fast_instance% PartialOrder.lift val val_injective

/-- A type of nonnegative elements of a linear order is a linear order. We explicitly give the
proofs of decidable equality and decidable order in order to ensure the decidability instances are
all definitionally equal. -/
instance instLinearOrder [LinearOrder M] : LinearOrder (Nonneg M) :=
  fast_instance% @LinearOrder.lift (Nonneg M) _ _
    ⟨fun x y ↦ ⟨max x.val y.val, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y ↦ ⟨min x.val y.val, min_rec' _ x.2 y.2⟩⟩ val val_injective (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

end Nonneg
