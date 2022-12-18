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

instance [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { instGroupWithZeroMulOpposite α, instSemiringMulOpposite α with }

instance [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { instGroupWithZeroMulOpposite α, instRingMulOpposite α with }

instance [Semifield α] : Semifield αᵐᵒᵖ :=
  { instDivisionSemiringMulOpposite α, MulOpposite.instCommSemiringMulOpposite α with }

instance [Field α] : Field αᵐᵒᵖ :=
  { instDivisionRingMulOpposite α, instCommRingMulOpposite α with }

end MulOpposite

namespace AddOpposite

instance [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { instGroupWithZeroAddOpposite α, instSemiringAddOpposite α with }

instance [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { instGroupWithZeroAddOpposite α, instRingAddOpposite α with }

instance [Semifield α] : Semifield αᵃᵒᵖ :=
  { instDivisionSemiringAddOpposite, instCommSemiringAddOpposite α with }

instance [Field α] : Field αᵃᵒᵖ :=
  { instDivisionRingAddOpposite, instCommRingAddOpposite α with }

end AddOpposite
