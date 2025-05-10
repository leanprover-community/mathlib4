/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.AddConstMap.Basic

open scoped AddConstMap

structure AddConstMonoMap (G H : Type*) [Add G] [Add H] [Preorder G] [Preorder H] (a : G) (b : H)
    extends G →+c[a, b] H, G →o H

notation:25 G " →o+c[" a ", " b "] " H => AddConstMonoMap G H a b

instance (G H : Type*) [Add G] [Add H] [Preorder G] [Preorder H] (a : G) (b : H) :
    FunLike (G →o+c[a, b] H) G H where
  coe f := f.toAddConstMap
  coe_injective' | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl

instance (G H : Type*) [Add G] [Add H] [Preorder G] [Preorder H] (a : G) (b : H) :
    AddConstMapClass (G →o+c[a, b] H) G H a b where
  map_add_const f := f.map_add_const'

instance (G H : Type*) [Add G] [Add H] [Preorder G] [Preorder H] (a : G) (b : H) :
    OrderHomClass (G →o+c[a, b] H) G H where
  map_rel f _ _ h := f.monotone h

namespace AddConstMonoMapClass

/-

theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
  calc
    f x ≤ f ⌈x⌉ := f.monotone <| le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _
#align circle_deg1_lift.map_le_of_map_zero CircleDeg1Lift.map_le_of_map_zero

theorem map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)
#align circle_deg1_lift.map_map_zero_le CircleDeg1Lift.map_map_zero_le

theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
    ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ := floor_mono <| f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_int _ _
#align circle_deg1_lift.floor_map_map_zero_le CircleDeg1Lift.floor_map_map_zero_le

theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
    ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono <| f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_int _ _
#align circle_deg1_lift.ceil_map_map_zero_le CircleDeg1Lift.ceil_map_map_zero_le

theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := (add_lt_add_left (ceil_lt_add_one _) _)
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm
#align circle_deg1_lift.map_map_zero_lt CircleDeg1Lift.map_map_zero_lt

theorem le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
    _ ≤ f x := f.monotone <| floor_le _
#align circle_deg1_lift.le_map_of_map_zero CircleDeg1Lift.le_map_of_map_zero

theorem le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)
#align circle_deg1_lift.le_map_map_zero CircleDeg1Lift.le_map_map_zero

theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_int _ _).symm
    _ ≤ ⌊f (g 0)⌋ := floor_mono <| f.le_map_map_zero g
#align circle_deg1_lift.le_floor_map_map_zero CircleDeg1Lift.le_floor_map_map_zero

theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_int _ _).symm
    _ ≤ ⌈f (g 0)⌉ := ceil_mono <| f.le_map_map_zero g
#align circle_deg1_lift.le_ceil_map_map_zero CircleDeg1Lift.le_ceil_map_map_zero

theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := (add_lt_add_left (sub_one_lt_floor _) _)
    _ ≤ f (g 0) := f.le_map_map_zero g
#align circle_deg1_lift.lt_map_map_zero CircleDeg1Lift.lt_map_map_zero

-/

end AddConstMonoMapClass
