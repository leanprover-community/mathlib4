/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Polynomial.Cardinal
import Mathlib.RingTheory.Algebraic

#align_import algebra.algebraic_card from "leanprover-community/mathlib"@"40494fe75ecbd6d2ec61711baa630cf0a7b7d064"

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `# R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `Liouville.is_transcendental`.
-/


universe u v

open Cardinal Polynomial Set

open Cardinal Polynomial

namespace Algebraic

theorem infinite_of_charZero (R A : Type*) [CommRing R] [IsDomain R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite :=
  infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_nat
#align algebraic.infinite_of_char_zero Algebraic.infinite_of_charZero

theorem aleph0_le_cardinal_mk_of_charZero (R A : Type*) [CommRing R] [IsDomain R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } :=
  infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)
#align algebraic.aleph_0_le_cardinal_mk_of_char_zero Algebraic.aleph0_le_cardinal_mk_of_charZero

section lift

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
  [NoZeroSMulDivisors R A]

theorem cardinal_mk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ Cardinal.lift.{v} #(R[X]) * ℵ₀ := by
  rw [← mk_uLift, ← mk_uLift]
  -- ⊢ #(ULift { x // IsAlgebraic R x }) ≤ #(ULift R[X]) * ℵ₀
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  -- ⊢ #(ULift { x // IsAlgebraic R x }) ≤ #(ULift R[X]) * ℵ₀
  refine' lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => _
  -- ⊢ lift.{u, v} #↑(g ⁻¹' {f}) ≤ ℵ₀
  rw [lift_le_aleph0, le_aleph0_iff_set_countable]
  -- ⊢ Set.Countable (g ⁻¹' {f})
  suffices : MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A)
  -- ⊢ Set.Countable (g ⁻¹' {f})
  exact this.countable_of_injOn (Subtype.coe_injective.injOn _) (f.rootSet_finite A).countable
  -- ⊢ MapsTo Subtype.val (g ⁻¹' {f}) (rootSet f A)
  rintro x (rfl : g x = f)
  -- ⊢ ↑x ∈ rootSet (g x) A
  exact mem_rootSet.2 ⟨hg₁ x, hg₂ x⟩
  -- 🎉 no goals
#align algebraic.cardinal_mk_lift_le_mul Algebraic.cardinal_mk_lift_le_mul

theorem cardinal_mk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ :=
  (cardinal_mk_lift_le_mul R A).trans <|
    (mul_le_mul_right' (lift_le.2 cardinal_mk_le_max) _).trans <| by simp
                                                                     -- 🎉 no goals
#align algebraic.cardinal_mk_lift_le_max Algebraic.cardinal_mk_lift_le_max

@[simp]
theorem cardinal_mk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R :=
  ((cardinal_mk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm <|
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      NoZeroSMulDivisors.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩
#align algebraic.cardinal_mk_lift_of_infinite Algebraic.cardinal_mk_lift_of_infinite

variable [Countable R]

@[simp]
protected theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le]
  -- ⊢ lift.{?u.44998, v} #↑{x | IsAlgebraic R x} ≤ lift.{?u.44998, v} ℵ₀
  apply (cardinal_mk_lift_le_max R A).trans
  -- ⊢ max (lift.{v, u} #R) ℵ₀ ≤ lift.{u, v} ℵ₀
  simp
  -- 🎉 no goals
#align algebraic.countable Algebraic.countable

@[simp]
theorem cardinal_mk_of_countable_of_charZero [CharZero A] [IsDomain R] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ :=
  (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinal_mk_of_charZero R A)
#align algebraic.cardinal_mk_of_countble_of_char_zero Algebraic.cardinal_mk_of_countable_of_charZero

end lift

section NonLift

variable (R A : Type u) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
  [NoZeroSMulDivisors R A]

theorem cardinal_mk_le_mul : #{ x : A // IsAlgebraic R x } ≤ #(R[X]) * ℵ₀ := by
  rw [← lift_id #_, ← lift_id #(R[X])]
  -- ⊢ lift.{u, u} #{ x // IsAlgebraic R x } ≤ lift.{u, u} #R[X] * ℵ₀
  exact cardinal_mk_lift_le_mul R A
  -- 🎉 no goals
#align algebraic.cardinal_mk_le_mul Algebraic.cardinal_mk_le_mul

theorem cardinal_mk_le_max : #{ x : A // IsAlgebraic R x } ≤ max #R ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R]
  -- ⊢ lift.{u, u} #{ x // IsAlgebraic R x } ≤ max (lift.{u, u} #R) ℵ₀
  exact cardinal_mk_lift_le_max R A
  -- 🎉 no goals
#align algebraic.cardinal_mk_le_max Algebraic.cardinal_mk_le_max

@[simp]
theorem cardinal_mk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R :=
  lift_inj.1 <| cardinal_mk_lift_of_infinite R A
#align algebraic.cardinal_mk_of_infinite Algebraic.cardinal_mk_of_infinite

end NonLift

end Algebraic
