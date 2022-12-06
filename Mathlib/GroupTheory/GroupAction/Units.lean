/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-! # Group actions on and by `Mˣ`

This file provides the action of a unit on a type `α`, `has_smul Mˣ α`, in the presence of
`has_smul M α`, with the obvious definition stated in `units.smul_def`. This definition preserves
`mul_action` and `distrib_mul_action` structures too.

Additionally, a `mul_action G M` for some group `G` satisfying some additional properties admits a
`mul_action G Mˣ` structure, again with the obvious definition stated in `units.coe_smul`.
These instances use a primed name.

The results are repeated for `add_units` and `has_vadd` where relevant.
-/


variable {G H M N : Type _} {α : Type _}

namespace Units

/-! ### Action of the units of `M` on a type `α` -/


@[to_additive]
instance [Monoid M] [HasSmul M α] : HasSmul Mˣ α where smul m a := (m : M) • a

@[to_additive]
theorem smul_def [Monoid M] [HasSmul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a :=
  rfl
#align units.smul_def Units.smul_def

@[simp]
theorem smul_is_unit [Monoid M] [HasSmul M α] {m : M} (hm : IsUnit m) (a : α) :
    hm.Unit • a = m • a :=
  rfl
#align units.smul_is_unit Units.smul_is_unit

theorem IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.Unit⁻¹ • a = 1 :=
  h.coe_inv_mul
#align is_unit.inv_smul IsUnit.inv_smul

@[to_additive]
instance [Monoid M] [HasSmul M α] [HasFaithfulSmul M α] :
    HasFaithfulSmul Mˣ α where eq_of_smul_eq_smul u₁ u₂ h := Units.ext <| eq_of_smul_eq_smul h

@[to_additive]
instance [Monoid M] [MulAction M α] :
    MulAction Mˣ α where
  one_smul := (one_smul M : _)
  mul_smul m n := mul_smul (m : M) n

instance [Monoid M] [Zero α] [SmulZeroClass M α] :
    SmulZeroClass Mˣ α where
  smul := (· • ·)
  smul_zero m := smul_zero m

instance [Monoid M] [AddZeroClass α] [DistribSmul M α] :
    DistribSmul Mˣ α where smul_add m := smul_add (m : M)

instance [Monoid M] [AddMonoid α] [DistribMulAction M α] : DistribMulAction Mˣ α :=
  { Units.distribSmul with }

instance [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction Mˣ α where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one m

instance smul_comm_class_left [Monoid M] [HasSmul M α] [HasSmul N α] [SmulCommClass M N α] :
    SmulCommClass Mˣ N α where smul_comm m n := (smul_comm (m : M) n : _)
#align units.smul_comm_class_left Units.smul_comm_class_left

instance smul_comm_class_right [Monoid N] [HasSmul M α] [HasSmul N α] [SmulCommClass M N α] :
    SmulCommClass M Nˣ α where smul_comm m n := (smul_comm m (n : N) : _)
#align units.smul_comm_class_right Units.smul_comm_class_right

instance [Monoid M] [HasSmul M N] [HasSmul M α] [HasSmul N α] [IsScalarTower M N α] :
    IsScalarTower Mˣ N α where smul_assoc m n := (smul_assoc (m : M) n : _)

/-! ### Action of a group `G` on units of `M` -/


/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `mul_action Mˣ Nˣ` under suitable
conditions.
-/
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SmulCommClass G M M]
    [IsScalarTower G M M] :
    MulAction G
      Mˣ where
  smul g m :=
    ⟨g • (m : M), g⁻¹ • ↑m⁻¹, by rw [smul_mul_smul, Units.mul_inv, mul_right_inv, one_smul], by
      rw [smul_mul_smul, Units.inv_mul, mul_left_inv, one_smul]⟩
  one_smul m := Units.ext <| one_smul _ _
  mul_smul g₁ g₂ m := Units.ext <| mul_smul _ _ _
#align units.mul_action' Units.mulAction'

@[simp]
theorem coe_smul [Group G] [Monoid M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) :=
  rfl
#align units.coe_smul Units.coe_smul

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[simp]
theorem smul_inv [Group G] [Monoid M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ :=
  ext rfl
#align units.smul_inv Units.smul_inv

/-- Transfer `smul_comm_class G H M` to `smul_comm_class G H Mˣ` -/
instance smul_comm_class' [Group G] [Group H] [Monoid M] [MulAction G M] [SmulCommClass G M M]
    [MulAction H M] [SmulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SmulCommClass G H M] :
    SmulCommClass G H Mˣ where smul_comm g h m := Units.ext <| smul_comm g h (m : M)
#align units.smul_comm_class' Units.smul_comm_class'

/-- Transfer `is_scalar_tower G H M` to `is_scalar_tower G H Mˣ` -/
instance is_scalar_tower' [HasSmul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SmulCommClass G M M] [MulAction H M] [SmulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] :
    IsScalarTower G H Mˣ where smul_assoc g h m := Units.ext <| smul_assoc g h (m : M)
#align units.is_scalar_tower' Units.is_scalar_tower'

/-- Transfer `is_scalar_tower G M α` to `is_scalar_tower G Mˣ α` -/
instance is_scalar_tower'_left [Group G] [Monoid M] [MulAction G M] [HasSmul M α] [HasSmul G α]
    [SmulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] :
    IsScalarTower G Mˣ α where smul_assoc g m := (smul_assoc g (m : M) : _)
#align units.is_scalar_tower'_left Units.is_scalar_tower'_left

-- Just to prove this transfers a particularly useful instance.
example [Monoid M] [Monoid N] [MulAction M N] [SmulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ :=
  Units.mulAction'

/-- A stronger form of `units.mul_action'`. -/
instance mulDistribMulAction' [Group G] [Monoid M] [MulDistribMulAction G M] [SmulCommClass G M M]
    [IsScalarTower G M M] : MulDistribMulAction G Mˣ :=
  { Units.mulAction' with smul := (· • ·), smul_one := fun m => Units.ext <| smul_one _,
    smul_mul := fun g m₁ m₂ => Units.ext <| smul_mul' _ _ _ }
#align units.mul_distrib_mul_action' Units.mulDistribMulAction'

end Units

theorem IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.coe_smul _ _⟩
#align is_unit.smul IsUnit.smul
