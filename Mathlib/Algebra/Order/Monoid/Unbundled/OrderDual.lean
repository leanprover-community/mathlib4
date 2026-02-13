/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-! # Unbundled ordered monoid structures on the order dual. -/

@[expose] public section

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance mulLeftReflectLE [LE α] [Mul α] [c : MulLeftReflectLE α] : MulLeftReflectLE αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulLeftMono [LE α] [Mul α] [c : MulLeftMono α] : MulLeftMono αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulRightReflectLE [LE α] [Mul α] [c : MulRightReflectLE α] : MulRightReflectLE αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulRightMono [LE α] [Mul α] [c : MulRightMono α] : MulRightMono αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulLeftReflectLT [LT α] [Mul α] [c : MulLeftReflectLT α] : MulLeftReflectLT αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulLeftStrictMono [LT α] [Mul α] [c : MulLeftStrictMono α] : MulLeftStrictMono αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulRightReflectLT [LT α] [Mul α] [c : MulRightReflectLT α] : MulRightReflectLT αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

@[to_additive]
instance mulRightStrictMono [LT α] [Mul α] [c : MulRightStrictMono α] : MulRightStrictMono αᵒᵈ :=
  ⟨fun m _ _ h => c.1 (ofDual m) h⟩

end OrderDual
