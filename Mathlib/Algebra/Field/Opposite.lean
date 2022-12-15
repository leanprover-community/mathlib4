/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.field.opposite
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.Ring.Opposite

/-!
# Field structure on the multiplicative/additive opposite
-/


variable (α : Type _)

instance [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.semiring α with }

instance [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.ring α with }

instance [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.commSemiring α with }

instance [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.divisionRing α, MulOpposite.commRing α with }

instance [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.semiring α with }

instance [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.ring α with }

instance [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring α, AddOpposite.commSemiring α with }

instance [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing α, AddOpposite.commRing α with }
