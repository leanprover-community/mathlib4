/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.LongElement

/-! # The right weak order and left weak order
Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

-/

namespace CoxeterSystem

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

/-! ## The right weak order on a Coxeter group -/
namespace RightWeakOrder

/-- The less than or equal to relation of the right weak order on `W`. This is not an instance
because there are several other interesting partial orders on `W` (including the left weak order
and the Bruhat order). To equip `W` with the right weak order, use this definition to create a local
instance of `LE W`. The poset and inf-semilattice structure on `W` will be inferred using typeclass
inference. -/
def rightWeakOrderLE : LE W where
  le u w := ℓ w = ℓ u + ℓ (w * u⁻¹)

local instance : LE W := cs.RightWeakOrder.le

variable [LE W]

instance : PartialOrder W := sorry

instance : SemilatticeInf W := sorry

theorem le_iff_length_eq (u w : W) : u ≤ w ↔ ℓ w = ℓ u + ℓ (w * u⁻¹) := rfl

theorem le_iff_exists_reducedWord (u w : W) :
    u ≤ w ↔ ∃ (ω : List B) (k : ℕ), cs.IsReduced ω ∧ π ω = w ∧ π (ω.drop k) = u := by sorry

theorem length_strictMono : StrictMono cs.length := by
  sorry

theorem length_mono : Monotone cs.length := by
  sorry

theorem isRightDescent_of_simple_le {w : W} {i : I} (h : s i ≤ w) : cs.IsRightDescent w i := by
  sorry

theorem simple_le_of_isRightDescent {w : W} {i : I} (h : cs.IsRightDescent w i) : s i ≤ w := by
  sorry

theorem simple_le_iff (w : W) (i : I) : s i ≤ w ↔ cs.IsRightDescent w i := by sorry

theorem mul_inv_le_mul_inv_right_iff {u v w : W} (huv : u ≤ v) (huw : u ≤ w) :
    v * u⁻¹ ≤ w * u⁻¹ ↔ v ≤ w := by sorry

theorem mul_inv_le_mul_inv_right_of_le {u v w : W} (huv : u ≤ v) (hvw : v ≤ w) :
    v * u⁻¹ ≤ w * u⁻¹ := by sorry

section Finite

variable [Finite W]

local notation "w₀" => cs.longElement

theorem le_longElement (w : W) : w ≤ w₀ := by sorry

theorem longElement_mul_antitone : Antitone (fun w ↦ w₀ * w) := by sorry

instance : Lattice W := sorry

theorem top_eq_longElement : ⊤ = w₀ := rfl

end Finite

end RightWeakOrder

/-! ## The left weak order on a Coxeter group -/
namespace LeftWeakOrder

/-- The less than or equal to relation of the left weak order on `W`. This is not an instance
because there are several other interesting partial orders on `W` (including the right weak order
and the Bruhat order). To equip `W` with the left weak order, use this definition to create a local
instance of `LE W`. The poset and inf-semilattice structure on `W` will be inferred using typeclass
inference. -/
def leftWeakOrderLE : LE W where
  le u w := ℓ w = ℓ u + ℓ (u⁻¹ * w)

local instance : LE W := cs.LeftWeakOrder.le

variable [LE W]

instance : PartialOrder W := sorry

instance : SemilatticeInf W := sorry

theorem le_iff (u w : W) : u ≤ w ↔ ℓ w = ℓ u + ℓ (u⁻¹ * w) := rfl

theorem le_iff_exists_reducedWord (u w : W) :
    u ≤ w ↔ ∃ (ω : List B) (k : ℕ), cs.IsReduced ω ∧ π ω = w ∧ π (ω.take k) = u := by sorry

theorem length_strictMono : StrictMono cs.length := by
  sorry

theorem length_mono : Monotone cs.length := by
  sorry

theorem isRightDescent_of_simple_le {w : W} {i : I} (h : s i ≤ w) : cs.IsLeftDescent w i := by
  sorry

theorem simple_le_of_isRightDescent {w : W} {i : I} (h : cs.IsLeftDescent w i) : s i ≤ w := by
  sorry

theorem simple_le_iff (w : W) (i : I) : s i ≤ w ↔ cs.IsLeftDescent w i := by sorry

theorem mul_inv_le_mul_inv_right_iff {u v w : W} (huv : u ≤ v) (huw : u ≤ w) :
    u⁻¹ * v ≤ u⁻¹ * w ↔ v ≤ w := by sorry

theorem mul_inv_le_mul_inv_right_of_le {u v w : W} (huv : u ≤ v) (hvw : v ≤ w) :
    u⁻¹ * v ≤ u⁻¹ * w := by sorry

section Finite

variable [Finite W]

local notation "w₀" => cs.longElement

theorem le_longElement (w : W) : w ≤ w₀ := by sorry

theorem longElement_mul_antitone : Antitone (fun w ↦ w * w₀) := by sorry

instance : Lattice W := sorry

theorem top_eq_longElement : ⊤ = w₀ := rfl

end Finite

end LeftWeakOrder

end CoxeterSystem
