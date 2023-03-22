/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.field.opposite
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Opposite

/-!
# Field structure on the multiplicative/additive opposite
-/

namespace MulOpposite

variable (α : Type _)

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.semiring α with }

instance divisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.ring α with }

instance semifield [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.commSemiring α with }

instance field [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.divisionRing α, MulOpposite.commRing α with }

end MulOpposite

namespace AddOpposite

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.semiring α with }

instance divisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.ring α with }

instance semifield [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring, AddOpposite.commSemiring α with }

instance field [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing, AddOpposite.commRing α with }

end AddOpposite
