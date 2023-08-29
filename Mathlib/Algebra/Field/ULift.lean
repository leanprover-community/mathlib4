/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.ULift

#align_import algebra.field.ulift from "leanprover-community/mathlib"@"13e18cfa070ea337ea960176414f5ae3a1534aae"

/-!
# Field instances for `ULift`

This file defines instances for field, semifield and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

universe u v
variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance [RatCast α] : RatCast (ULift α) := ⟨λ a ↦ up a⟩

@[simp, norm_cast]
theorem up_ratCast [RatCast α] (q : ℚ) : up (q : α) = q :=
  rfl
#align ulift.up_rat_cast ULift.up_ratCast

@[simp, norm_cast]
theorem down_ratCast [RatCast α] (q : ℚ) : down (q : ULift α) = q :=
  rfl
#align ulift.down_rat_cast ULift.down_ratCast

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) := by
  refine' down_injective.divisionSemiring down .. <;> intros <;> rfl
                                                      -- ⊢ 0.down = 0
                                                      -- ⊢ 1.down = 1
                                                      -- ⊢ (x✝ + y✝).down = x✝.down + y✝.down
                                                      -- ⊢ (x✝ * y✝).down = x✝.down * y✝.down
                                                      -- ⊢ x✝⁻¹.down = x✝.down⁻¹
                                                      -- ⊢ (x✝ / y✝).down = x✝.down / y✝.down
                                                      -- ⊢ (n✝ • x✝).down = n✝ • x✝.down
                                                      -- ⊢ (x✝ ^ n✝).down = x✝.down ^ n✝
                                                      -- ⊢ (x✝ ^ n✝).down = x✝.down ^ n✝
                                                      -- ⊢ (↑n✝).down = ↑n✝
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align ulift.division_semiring ULift.divisionSemiring

instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }
#align ulift.semifield ULift.semifield

instance divisionRing [DivisionRing α] : DivisionRing (ULift α) := by
  refine' down_injective.divisionRing down .. <;> intros <;> rfl
                                                  -- ⊢ 0.down = 0
                                                  -- ⊢ 1.down = 1
                                                  -- ⊢ (x✝ + y✝).down = x✝.down + y✝.down
                                                  -- ⊢ (x✝ * y✝).down = x✝.down * y✝.down
                                                  -- ⊢ (-x✝).down = -x✝.down
                                                  -- ⊢ (x✝ - y✝).down = x✝.down - y✝.down
                                                  -- ⊢ x✝⁻¹.down = x✝.down⁻¹
                                                  -- ⊢ (x✝ / y✝).down = x✝.down / y✝.down
                                                  -- ⊢ (n✝ • x✝).down = n✝ • x✝.down
                                                  -- ⊢ (n✝ • x✝).down = n✝ • x✝.down
                                                  -- ⊢ (n✝ • x✝).down = n✝ • x✝.down
                                                  -- ⊢ (x✝ ^ n✝).down = x✝.down ^ n✝
                                                  -- ⊢ (x✝ ^ n✝).down = x✝.down ^ n✝
                                                  -- ⊢ (↑n✝).down = ↑n✝
                                                  -- ⊢ (↑n✝).down = ↑n✝
                                                  -- ⊢ (↑n✝).down = ↑n✝
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
#align ulift.division_ring ULift.divisionRing

instance field [Field α] : Field (ULift α) :=
  { ULift.semifield, ULift.divisionRing with }
#align ulift.field ULift.field

end ULift
