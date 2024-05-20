/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Order.PiLex

/-!
# Lexicographic product of algebraic order structures

This file proves that the lexicographic order on pi types is compatible with the pointwise algebraic
operations.
-/

namespace Pi.Lex
variable {ι : Type*} {α : ι → Type*} [LinearOrder ι]

@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid (α i)] :
    OrderedCancelCommMonoid (Lex (∀ i, α i)) where
  mul_le_mul_left _ _ hxy z :=
    hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr_arg (z j * ·) (hi.1 j hji), mul_lt_mul_left' hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup (α i)] : OrderedCommGroup (Lex (∀ i, α i)) where
  mul_le_mul_left _ _ := mul_le_mul_left'
#align pi.lex.ordered_comm_group Pi.Lex.orderedCommGroup
#align pi.lex.ordered_add_comm_group Pi.Lex.orderedAddCommGroup

@[to_additive]
noncomputable instance linearOrderedCancelCommMonoid [IsWellOrder ι (· < ·)]
    [∀ i, LinearOrderedCancelCommMonoid (α i)] :
    LinearOrderedCancelCommMonoid (Lex (∀ i, α i)) where
  __ : LinearOrder (Lex (∀ i, α i)) := inferInstance
  __ : OrderedCancelCommMonoid (Lex (∀ i, α i)) := inferInstance

@[to_additive]
noncomputable instance linearOrderedCommGroup [IsWellOrder ι (· < ·)]
    [∀ i, LinearOrderedCommGroup (α i)] :
    LinearOrderedCommGroup (Lex (∀ i, α i)) where
  __ : LinearOrder (Lex (∀ i, α i)) := inferInstance
  mul_le_mul_left _ _ := mul_le_mul_left'

end Pi.Lex
