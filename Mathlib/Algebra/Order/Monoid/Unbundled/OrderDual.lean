/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-! # Unbundled ordered monoid structures on the order dual. -/

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance mulLeftReflectLE [LE α] [Mul α] [c : MulLeftReflectLE α] : MulLeftReflectLE αᵒᵈ :=
  ⟨Contravariant.flip c.1⟩

@[to_additive]
instance mulLeftMono [LE α] [Mul α] [c : MulLeftMono α] : MulLeftMono αᵒᵈ :=
  ⟨Covariant.flip c.1⟩

@[to_additive]
instance mulRightReflectLE [LE α] [Mul α] [c : MulRightReflectLE α] : MulRightReflectLE αᵒᵈ :=
  ⟨Contravariant.flip c.1⟩

@[to_additive]
instance mulRightMono [LE α] [Mul α] [c : MulRightMono α] : MulRightMono αᵒᵈ :=
  ⟨Covariant.flip c.1⟩

@[to_additive]
instance mulLeftReflectLT [LT α] [Mul α] [c : MulLeftReflectLT α] : MulLeftReflectLT αᵒᵈ :=
  ⟨Contravariant.flip c.1⟩

@[to_additive]
instance mulLeftStrictMono [LT α] [Mul α] [c : MulLeftStrictMono α] : MulLeftStrictMono αᵒᵈ :=
  ⟨Covariant.flip c.1⟩

@[to_additive]
instance mulRightReflectLT [LT α] [Mul α] [c : MulRightReflectLT α] : MulRightReflectLT αᵒᵈ :=
  ⟨Contravariant.flip c.1⟩

@[to_additive]
instance mulRightStrictMono [LT α] [Mul α] [c : MulRightStrictMono α] : MulRightStrictMono αᵒᵈ :=
  ⟨Covariant.flip c.1⟩

end OrderDual
