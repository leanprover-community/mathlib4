/-
Copyright (c) 2021 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Data.SetLike.Pointwise
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! # Pointwise instances on `AffineSubspace`

This file provides:

* `AffineSubspace.pointwiseNeg`

-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {k : Type*} {V : Type*}

open Affine
open scoped Pointwise

namespace AffineSubspace

variable [Ring k] [AddCommGroup V] [Module k V] -- [AffineSpace V A]

/-- The affine subspace with every element negated.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
protected def pointwiseNeg : Neg (AffineSubspace k V) := ⟨fun p => {
    carrier := -p
    smul_vsub_vadd_mem c x y z hx hy hz := by
      simp only [Set.mem_neg, SetLike.mem_coe, vsub_eq_sub,
        vadd_eq_add, neg_add] at ⊢ hx hy hz
      simpa [neg_add_eq_sub] using p.smul_vsub_vadd_mem (-c) hy hx hz
  }⟩

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseNeg

instance : IsConcreteNeg (AffineSubspace k V) V := ⟨fun _ => rfl⟩

variable (p q : AffineSubspace k V)

@[simp] theorem neg_inf : -(p ⊓ q) = -p ⊓ -q := rfl

@[simp] theorem neg_sup : -(p ⊔ q) = -p ⊔ -q :=
  (SetLike.negOrderIso : AffineSubspace k V ≃o AffineSubspace k V).map_sup p q

@[simp] theorem neg_bot : -(⊥ : AffineSubspace k V) = ⊥ :=
  SetLike.coe_injective <| Set.neg_empty.trans <| bot_coe k V V

@[simp] theorem neg_top : -(⊤ : AffineSubspace k V) = ⊤ :=
  SetLike.coe_injective Set.neg_univ

@[simp] theorem neg_iInf {ι : Sort*} (S : ι → AffineSubspace k V) : (-⨅ i, S i) = ⨅ i, -S i :=
  (SetLike.negOrderIso : AffineSubspace k V ≃o AffineSubspace k V).map_iInf _

@[simp]
theorem neg_iSup {ι : Sort*} (S : ι → AffineSubspace k V) : (-⨆ i, S i) = ⨆ i, -S i :=
  (SetLike.negOrderIso : AffineSubspace k V ≃o AffineSubspace k V).map_iSup _

end AffineSubspace
