/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.units from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-! # Group actions on and by `Mˣ`

This file provides the action of a unit on a type `α`, `SMul Mˣ α`, in the presence of
`SMul M α`, with the obvious definition stated in `Units.smul_def`. This definition preserves
`MulAction` and `DistribMulAction` structures too.

Additionally, a `MulAction G M` for some group `G` satisfying some additional properties admits a
`MulAction G Mˣ` structure, again with the obvious definition stated in `Units.coe_smul`.
These instances use a primed name.

The results are repeated for `AddUnits` and `VAdd` where relevant.
-/


variable {G H M N : Type*} {α : Type*}

namespace Units

/-! ### Action of the units of `M` on a type `α` -/


@[to_additive]
instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a

@[to_additive]
theorem smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a :=
  rfl
#align units.smul_def Units.smul_def
#align add_units.vadd_def AddUnits.vadd_def

@[simp]
theorem smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) :
    hm.unit • a = m • a :=
  rfl
#align units.smul_is_unit Units.smul_isUnit

theorem _root_.IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.unit⁻¹ • a = 1 :=
  h.val_inv_mul
#align is_unit.inv_smul IsUnit.inv_smul

@[to_additive]
instance [Monoid M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α where
  eq_of_smul_eq_smul h := Units.ext <| eq_of_smul_eq_smul h

@[to_additive]
instance [Monoid M] [MulAction M α] :
    MulAction Mˣ α where
  one_smul := (one_smul M : _)
  mul_smul m n := mul_smul (m : M) n

instance [Monoid M] [Zero α] [SMulZeroClass M α] :
    SMulZeroClass Mˣ α where
  smul := (· • ·)
  smul_zero m := smul_zero (m : M)

instance instDistribSMulUnits [Monoid M] [AddZeroClass α] [DistribSMul M α] :
    DistribSMul Mˣ α where smul_add m := smul_add (m : M)

instance [Monoid M] [AddMonoid α] [DistribMulAction M α] : DistribMulAction Mˣ α :=
  { instDistribSMulUnits with
    one_smul := fun b => one_smul M b
    mul_smul := fun x y b => mul_smul (x : M) y b }

instance [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction Mˣ α where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one (m : M)

instance smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mˣ N α where smul_comm m n := (smul_comm (m : M) n : _)
#align units.smul_comm_class_left Units.smulCommClass_left

instance smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nˣ α where smul_comm m n := (smul_comm m (n : N) : _)
#align units.smul_comm_class_right Units.smulCommClass_right

instance [Monoid M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mˣ N α where smul_assoc m n := (smul_assoc (m : M) n : _)

/-! ### Action of a group `G` on units of `M` -/


/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `MulAction Mˣ Nˣ` under suitable
conditions.
-/
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] :
    MulAction G Mˣ where
  smul g m :=
    ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul, Units.mul_inv, mul_right_inv, one_smul],
         -- 🎉 no goals
      by rw [smul_mul_smul, Units.inv_mul, mul_left_inv, one_smul]⟩
         -- 🎉 no goals
  one_smul m := Units.ext <| one_smul _ _
  mul_smul g₁ g₂ m := Units.ext <| mul_smul _ _ _
#align units.mul_action' Units.mulAction'

@[simp]
theorem val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) :=
  rfl
#align units.coe_smul Units.val_smul

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[simp]
theorem smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ :=
  ext rfl
#align units.smul_inv Units.smul_inv

/-- Transfer `SMulCommClass G H M` to `SMulCommClass G H Mˣ` -/
instance smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SMulCommClass G H M] :
    SMulCommClass G H Mˣ where smul_comm g h m := Units.ext <| smul_comm g h (m : M)
#align units.smul_comm_class' Units.smulCommClass'

/-- Transfer `IsScalarTower G H M` to `IsScalarTower G H Mˣ` -/
instance isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] :
    IsScalarTower G H Mˣ where smul_assoc g h m := Units.ext <| smul_assoc g h (m : M)
#align units.is_scalar_tower' Units.isScalarTower'

/-- Transfer `IsScalarTower G M α` to `IsScalarTower G Mˣ α` -/
instance isScalarTower'_left [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
    [SMulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] :
    IsScalarTower G Mˣ α where smul_assoc g m := (smul_assoc g (m : M) : _)
#align units.is_scalar_tower'_left Units.isScalarTower'_left

-- Just to prove this transfers a particularly useful instance.
example [Monoid M] [Monoid N] [MulAction M N] [SMulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ :=
  Units.mulAction'

/-- A stronger form of `Units.mul_action'`. -/
instance mulDistribMulAction' [Group G] [Monoid M] [MulDistribMulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulDistribMulAction G Mˣ :=
  { Units.mulAction' with
    smul := (· • ·),
    smul_one := fun _ => Units.ext <| smul_one _,
    smul_mul := fun _ _ _ => Units.ext <| smul_mul' _ _ _ }
#align units.mul_distrib_mul_action' Units.mulDistribMulAction'

end Units

theorem IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩
#align is_unit.smul IsUnit.smul
