/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of algebraic structures

We introduce all kinds of algebraic instances on `DirectLimit`, and specialize to the cases
of modules and rings, showing that they are indeed colimits in the respective categories.

## Implementation notes

The first 400 lines are boilerplate code that defines algebraic instances on `DirectLimit`
from magma (`Mul`) to `Field`. To make everything "hom-polymorphic", we work with `DirectedSystem`s
of `FunLike`s rather than plain unbundled functions, and we use algebraic hom typeclasses
(e.g. `LinearMapClass`, `RingHomClass`) everywhere.

In `Mathlib/Algebra/Colimit/Module.lean` and `Mathlib/Algebra/Colimit/Ring.lean`,
`Module.DirectLimit`, `AddCommGroup.DirectLimit` and `Ring.DirectLimit`
are defined as quotients of the universal objects (`DirectSum` and `FreeCommRing`).
These definitions are more general and suitable for arbitrary colimits, but do not
immediately provide criteria to determine when two elements in a component are equal
in the direct limit.

On the other hand, the `DirectLimit` in this file is only defined for directed systems
and does not work for general colimits, but the equivalence relation defining `DirectLimit`
is very explicit. For colimits of directed systems there is no need to construct the
universal object for each type of algebraic structure; the same type `DirectLimit` simply
works for all of them. This file is therefore more general than the `Module` and `Ring`
files in terms of the variety of algebraic structures supported.

So far we only show that `DirectLimit` is the colimit in the categories of modules and rings,
but for the other algebraic structures the constructions and proofs will be easy following
the same pattern. Since any two colimits are isomorphic, this allows us to golf proofs of
equality criteria for `Module/AddCommGroup/Ring.DirectLimit`.
-/

suppress_compilation

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirected ι (· ≤ ·)]

namespace DirectLimit

section ZeroOne
variable [Nonempty ι] [∀ i, One (G i)]

@[to_additive] instance : One (DirectLimit G f) where
  one := map₀ f fun _ ↦ 1

variable [∀ i j h, OneHomClass (T h) (G i) (G j)]

@[to_additive] theorem one_def (i) : (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_one _) _

@[to_additive] theorem exists_eq_one (x) :
    ⟦x⟧ = (1 : DirectLimit G f) ↔ ∃ i h, f x.1 i h x.2 = 1 := by
  rw [one_def x.1, Quotient.eq]
  exact ⟨fun ⟨i, h, _, eq⟩ ↦ ⟨i, h, eq.trans (map_one _)⟩,
    fun ⟨i, h, eq⟩ ↦ ⟨i, h, h, eq.trans (map_one _).symm⟩⟩

end ZeroOne

section AddMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]

@[to_additive] instance : Mul (DirectLimit G f) where
  mul := map₂ f f f (fun _ ↦ (· * ·)) fun _ _ _ ↦ map_mul _

@[to_additive] theorem mul_def (i) (x y : G i) :
    ⟦⟨i, x⟩⟧ * ⟦⟨i, y⟩⟧ = (⟦⟨i, x * y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

end AddMul

@[to_additive] instance [∀ i, CommMagma (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    CommMagma (DirectLimit G f) where
  mul_comm := DirectLimit.induction₂ _ fun i _ _ ↦ by simp_rw [mul_def, mul_comm]

@[to_additive] instance [∀ i, Semigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    Semigroup (DirectLimit G f) where
  mul_assoc := DirectLimit.induction₃ _ fun i _ _ _ ↦ by simp_rw [mul_def, mul_assoc]

@[to_additive] instance [∀ i, CommSemigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    CommSemigroup (DirectLimit G f) where
  mul_comm := mul_comm

section SMul
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]

@[to_additive] instance : SMul R (DirectLimit G f) where
  smul r := map _ _ (fun _ ↦ (r • ·)) fun _ _ _ ↦ map_smul _ r

@[to_additive] theorem smul_def (i x) (r : R) : r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f) :=
  rfl

end SMul

@[to_additive] instance [Monoid R] [∀ i, MulAction R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulAction R (DirectLimit G f) where
  one_smul := DirectLimit.induction _ fun i _ ↦ by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, mul_smul]

variable [Nonempty ι]

@[to_additive] instance [∀ i, MulOneClass (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    MulOneClass (DirectLimit G f) where
  one_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, mul_one]

section Monoid
variable [∀ i, Monoid (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

@[to_additive] instance : Monoid (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  npow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ ↦ by simp_rw [map_def, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ ↦ by simp_rw [map_def, pow_succ, mul_def]

@[to_additive] theorem npow_def (i x) (n : ℕ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

end Monoid

@[to_additive] instance [∀ i, CommMonoid (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommMonoid (DirectLimit G f) where
  mul_comm := mul_comm

section Group
variable [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

@[to_additive] instance : Group (DirectLimit G f) where
  inv := map _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv _
  div := map₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div _
  zpow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by simp_rw [map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_mul_cancel := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [map_def, mul_def, inv_mul_cancel, one_def i]

@[to_additive] theorem inv_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

@[to_additive] theorem div_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

@[to_additive] theorem zpow_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

end Group

@[to_additive] instance [∀ i, CommGroup (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommGroup (DirectLimit G f) where
  mul_comm := mul_comm

instance [∀ i, MulZeroClass (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    MulZeroClass (DirectLimit G f) where
  zero_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, mul_zero]

section MulZeroOneClass

variable [∀ i, MulZeroOneClass (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

instance : MulZeroOneClass (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  exists_pair_ne := ⟨0, 1, fun h ↦ have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

end MulZeroOneClass

instance [∀ i, SemigroupWithZero (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SemigroupWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, MonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    MonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, CommMonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommMonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

section GroupWithZero

variable [∀ i, GroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

instance : GroupWithZero (DirectLimit G f) where
  inv := map _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv₀ _
  div := map₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div₀ _
  zpow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by simp_rw [map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [inv_zero]
  mul_inv_cancel := DirectLimit.induction _ fun i x ne ↦ by
    have : x ≠ 0 := by rintro rfl; exact ne (zero_def i).symm
    simp_rw [map_def, mul_def, mul_inv_cancel₀ this, one_def i]

theorem inv₀_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

theorem div₀_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

theorem zpow₀_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) := rfl

end GroupWithZero

instance [∀ i, CommGroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommGroupWithZero (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  mul_comm := mul_comm

section AddMonoidWithOne

variable [∀ i, AddMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : AddMonoidWithOne (DirectLimit G f) where
  natCast n := map₀ _ fun _ ↦ n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]

theorem natCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℕ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_natCast' _ (map_one _) _) _

end AddMonoidWithOne

section AddGroupWithOne

variable [∀ i, AddGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : AddGroupWithOne (DirectLimit G f) where
  __ : AddGroup _ := inferInstance
  intCast n := map₀ _ fun _ ↦ n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

theorem intCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℤ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_intCast' _ (map_one _) _) _

end AddGroupWithOne

instance [∀ i, AddCommMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommMonoidWithOne (DirectLimit G f) where
  add_comm := add_comm

instance [∀ i, AddCommGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommGroupWithOne (DirectLimit G f) where
  __ : AddGroupWithOne _ := inferInstance
  add_comm := add_comm

instance [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocSemiring (DirectLimit G f) where
  left_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, NonUnitalNonAssocCommSemiring (G i)]
    [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocCommSemiring (DirectLimit G f) where
  mul_comm := mul_comm

instance [∀ i, NonUnitalSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalSemiring (DirectLimit G f) where
  mul_assoc := mul_assoc

instance [∀ i, NonUnitalCommSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalCommSemiring (DirectLimit G f) where
  mul_comm := mul_comm

instance [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocSemiring (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

-- There is no NonAssocCommSemiring

instance [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Semiring (DirectLimit G f) where
  __ : NonAssocSemiring _ := inferInstance
  __ : Monoid _ := inferInstance

instance [∀ i, CommSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    CommSemiring (DirectLimit G f) where
  mul_comm := mul_comm

instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where
  __ : Semiring _ := inferInstance
  __ : AddCommGroupWithOne _ := inferInstance

instance [∀ i, CommRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    CommRing (DirectLimit G f) where
  mul_comm := mul_comm

section Action

instance [∀ i, Zero (G i)] [∀ i, SMulZeroClass R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulZeroClass R (DirectLimit G f) where
  smul_zero r := (smul_def _ _ _).trans <| by rw [smul_zero]; rfl

instance [Zero R] [∀ i, Zero (G i)] [∀ i, SMulWithZero R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SMulWithZero R (DirectLimit G f) where
  zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i]

instance [∀ i, AddZeroClass (G i)] [∀ i, DistribSMul R (G i)]
    [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    DistribSMul R (DirectLimit G f) where
  smul_add r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [add_def, smul_def, smul_add, add_def]

instance [Monoid R] [∀ i, AddMonoid (G i)] [∀ i, DistribMulAction R (G i)]
    [∀ i j h, DistribMulActionHomClass (T h) R (G i) (G j)] :
    DistribMulAction R (DirectLimit G f) :=
  have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

instance [Monoid R] [∀ i, Monoid (G i)] [∀ i, MulDistribMulAction R (G i)]
    [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulDistribMulAction R (DirectLimit G f) where
  smul_mul r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
  smul_one r := (smul_def _ _ _).trans <| by rw [smul_one]; rfl

instance [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G i) (G j)] :
    Module R (DirectLimit G f) :=
  have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i] }

end Action

section DivisionSemiring
variable [∀ i, DivisionSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

instance : DivisionSemiring (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := map₀ _ fun _ ↦ q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := map _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ ↦ map_nnratCast _ _) i, mul_def, NNRat.smul_def]

theorem nnratCast_def (q : ℚ≥0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_nnratCast _ _) _

end DivisionSemiring

instance [∀ i, Semifield (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Semifield (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  mul_comm := mul_comm

section DivisionRing
variable [∀ i, DivisionRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

instance : DivisionRing (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  __ : Ring _ := inferInstance
  ratCast q := map₀ _ fun _ ↦ q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := map _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ ↦ map_ratCast _ _) i, mul_def, Rat.smul_def]

theorem ratCast_def (q : ℚ) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_ratCast _ _) _

end DivisionRing

instance [∀ i, Field (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Field (DirectLimit G f) where
  __ : DivisionRing _ := inferInstance
  mul_comm := mul_comm

end DirectLimit

namespace DirectLimit

namespace Module

variable [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable [∀ i j h, LinearMapClass (T h) R (G i) (G j)]
variable (R ι G f) [Nonempty ι]

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_add' _ _ := (add_def ..).symm
  map_smul' _ _ := (smul_def ..).symm

variable {R ι G f}

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x := .symm <| eq_of_le ..

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
@[simps -isSimp]
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, lift_def, map_add]
  map_smul' r := DirectLimit.induction _ fun i x ↦ by
    simp_rw [smul_def, lift_def, map_smul, RingHom.id_apply]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x := rfl

@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Module

namespace Ring

variable [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i →+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm
  map_mul' _ _ := (mul_def ..).symm
  map_zero' := (zero_def i).symm
  map_add' _ _ := (add_def ..).symm

@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (P : Type*) [NonAssocSemiring P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_one' := by rw [one_def (Classical.arbitrary ι), lift_def, map_one]
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [mul_def, lift_def, map_mul]
  map_zero' := by simp_rw [zero_def (Classical.arbitrary ι), lift_def, map_zero]
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, lift_def, map_add]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Ring

end DirectLimit
