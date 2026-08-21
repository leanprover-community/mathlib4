/-
Copyright (c) 2026 Edison Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xu
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Ordered structures on submonoids and subgroups with zero

A submonoid with zero of a `LinearOrderedCommMonoidWithZero` is one, and a subgroup with zero of
a `LinearOrderedCommGroupWithZero` is one.

## Implementation notes

The order on the subtype is `Subtype.instLinearOrder`, so `≤`, `<`, `⊔` and `⊓` all agree with
the ambient ones on the nose. In particular `↑(a ⊔ b) = ↑a ⊔ ↑b` holds by `rfl`, which is what
makes statements such as `Valuation.map_add_le_max` transport for free.

## Tags
submonoid with zero, subgroup with zero, ordered
-/

@[expose] public section

assert_not_exists Ring

variable {M₀ S : Type*} [SetLike S M₀]

namespace SubmonoidWithZeroClass

variable [LinearOrderedCommMonoidWithZero M₀] [SubmonoidWithZeroClass S M₀] (s : S)

instance isBotZeroClass : IsBotZeroClass s :=
  ⟨fun a ↦ Subtype.coe_le_coe.1 (by simp)⟩

instance orderBot : OrderBot s where
  bot := 0
  bot_le := IsBotZeroClass.isBot_zero

@[simp] lemma bot_eq_zero' : (⊥ : s) = 0 := rfl

instance posMulStrictMono : PosMulStrictMono s where
  mul_lt_mul_of_pos_left _ ha _ _ hbc :=
    Subtype.coe_lt_coe.1
      (mul_lt_mul_of_pos_left (Subtype.coe_lt_coe.2 hbc) (Subtype.coe_lt_coe.2 ha))

-- See note [lower instance priority]
/-- A submonoid with zero of a linearly ordered commutative monoid with zero is one. -/
instance (priority := 75) toLinearOrderedCommMonoidWithZero :
    LinearOrderedCommMonoidWithZero s where
  __ := SubmonoidWithZeroClass.toCommMonoidWithZero s
  __ := (inferInstance : LinearOrder s)
  __ := SubmonoidWithZeroClass.orderBot s
  __ := SubmonoidWithZeroClass.isBotZeroClass s
  __ := SubmonoidWithZeroClass.posMulStrictMono s

lemma subtype_strictMono : StrictMono (SubmonoidWithZeroClass.subtype s) :=
  fun _ _ h ↦ Subtype.coe_lt_coe.2 h

lemma subtype_monotone : Monotone (SubmonoidWithZeroClass.subtype s) :=
  (subtype_strictMono s).monotone

end SubmonoidWithZeroClass

namespace SubgroupWithZeroClass

variable {G₀ : Type*} [LinearOrderedCommGroupWithZero G₀] [SetLike S G₀]
  [SubgroupWithZeroClass S G₀] (s : S)

-- See note [lower instance priority]
/-- A subgroup with zero of a linearly ordered commutative group with zero is one. -/
instance (priority := 75) toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero s where
  __ := SubmonoidWithZeroClass.toLinearOrderedCommMonoidWithZero s
  __ := SubgroupWithZeroClass.toCommGroupWithZero s

end SubgroupWithZeroClass
