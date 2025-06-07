/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.GroupWithZero.Subgroup
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.NormNum.Eq

/-!
# Divisible Group and rootable group

In this file, we define a divisible add monoid and a rootable monoid with some basic properties.

## Main definition

* `DivisibleBy A α`: An additive monoid `A` is said to be divisible by `α` iff for all `n ≠ 0 ∈ α`
  and `y ∈ A`, there is an `x ∈ A` such that `n • x = y`. In this file, we adopt a constructive
  approach, i.e. we ask for an explicit `div : A → α → A` function such that `div a 0 = 0` and
  `n • div a n = a` for all `n ≠ 0 ∈ α`.
* `RootableBy A α`: A monoid `A` is said to be rootable by `α` iff for all `n ≠ 0 ∈ α` and `y ∈ A`,
  there is an `x ∈ A` such that `x^n = y`. In this file, we adopt a constructive approach, i.e. we
  ask for an explicit `root : A → α → A` function such that `root a 0 = 1` and `(root a n)ⁿ = a` for
  all `n ≠ 0 ∈ α`.

## Main results

For additive monoids and groups:

* `divisibleByOfSMulRightSurj` : the constructive definition of divisiblity is implied by
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `smul_right_surj_of_divisibleBy` : the constructive definition of divisiblity implies
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `Prod.divisibleBy` : `A × B` is divisible for any two divisible additive monoids.
* `Pi.divisibleBy` : any product of divisible additive monoids is divisible.
* `AddGroup.divisibleByIntOfDivisibleByNat` : for additive groups, int divisiblity is implied
  by nat divisiblity.
* `AddGroup.divisibleByNatOfDivisibleByInt` : for additive groups, nat divisiblity is implied
  by int divisiblity.
* `AddCommGroup.divisibleByIntOfSMulTopEqTop`: the constructive definition of divisiblity
  is implied by the condition that `n • A = A` for all `n ≠ 0`.
* `AddCommGroup.smul_top_eq_top_of_divisibleBy_int`: the constructive definition of divisiblity
  implies the condition that `n • A = A` for all `n ≠ 0`.
* `divisibleByIntOfCharZero` : any field of characteristic zero is divisible.
* `QuotientAddGroup.divisibleBy` : quotient group of divisible group is divisible.
* `Function.Surjective.divisibleBy` : if `A` is divisible and `A →+ B` is surjective, then `B`
  is divisible.
* `DivisibleBy.instModule` : a torsion-free ℕ-divisible commutative group is a ℚ-module.

and their multiplicative counterparts:

* `rootableByOfPowLeftSurj` : the constructive definition of rootablity is implied by the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `pow_left_surj_of_rootableBy` : the constructive definition of rootablity implies the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `Prod.rootableBy` : any product of two rootable monoids is rootable.
* `Pi.rootableBy` : any product of rootable monoids is rootable.
* `Group.rootableByIntOfRootableByNat` : in groups, int rootablity is implied by nat
  rootablity.
* `Group.rootableByNatOfRootableByInt` : in groups, nat rootablity is implied by int
  rootablity.
* `QuotientGroup.rootableBy` : quotient group of rootable group is rootable.
* `Function.Surjective.rootableBy` : if `A` is rootable and `A →* B` is surjective, then `B` is
  rootable.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/


open Pointwise

section AddMonoid

variable (A α : Type*) [AddMonoid A] [SMul α A] [Zero α]

/--
An `AddMonoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class DivisibleBy where
  /-- The division function -/
  div : A → α → A
  div_zero : ∀ a, div a 0 = 0
  div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • div a n = a

end AddMonoid

section Monoid

variable (A α : Type*) [Monoid A] [Pow A α] [Zero α]

/-- A `Monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive]
class RootableBy where
  /-- The root function -/
  root : A → α → A
  root_zero : ∀ a, root a 0 = 1
  root_cancel : ∀ {n : α} (a : A), n ≠ 0 → root a n ^ n = a

@[to_additive smul_right_surj_of_divisibleBy]
theorem pow_left_surj_of_rootableBy [RootableBy A α] {n : α} (hn : n ≠ 0) :
    Function.Surjective (fun a => a ^ n : A → A) := fun x =>
  ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

/--
A `Monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructive version
implies the textbook approach.
-/
@[to_additive divisibleByOfSMulRightSurj
      "An `AddMonoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the constructive
      version implies the textbook approach."]
noncomputable def rootableByOfPowLeftSurj
    (H : ∀ {n : α}, n ≠ 0 → Function.Surjective (fun a => a ^ n : A → A)) : RootableBy A α where
  root a n := @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by classical exact dif_pos rfl
  root_cancel a hn := by
    dsimp only
    rw [dif_neg hn]
    exact (H hn a).choose_spec

section Pi

variable {ι β : Type*} (B : ι → Type*) [∀ i : ι, Pow (B i) β]
variable [Zero β] [∀ i : ι, Monoid (B i)] [∀ i, RootableBy (B i) β]

@[to_additive]
instance Pi.rootableBy : RootableBy (∀ i, B i) β where
  root x n i := RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

end Pi

section Prod

variable {β B B' : Type*} [Pow B β] [Pow B' β]
variable [Zero β] [Monoid B] [Monoid B'] [RootableBy B β] [RootableBy B' β]

@[to_additive]
instance Prod.rootableBy : RootableBy (B × B') β where
  root p n := (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

end Prod

section ULift

@[to_additive]
instance ULift.instRootableBy [RootableBy A α] : RootableBy (ULift A) α where
  root x a := ULift.up <| RootableBy.root x.down a
  root_zero x := ULift.ext _ _ <| RootableBy.root_zero x.down
  root_cancel _ h := ULift.ext _ _ <| RootableBy.root_cancel _ h

end ULift

end Monoid

namespace AddCommGroup

variable (A : Type*) [AddCommGroup A]

theorem smul_top_eq_top_of_divisibleBy_int [DivisibleBy A ℤ] {n : ℤ} (hn : n ≠ 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

/-- If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
noncomputable def divisibleByIntOfSMulTopEqTop
    (H : ∀ {n : ℤ} (_hn : n ≠ 0), n • (⊤ : AddSubgroup A) = ⊤) : DivisibleBy A ℤ where
  div a n :=
    if hn : n = 0 then 0 else (show a ∈ n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dif_pos rfl
  div_cancel a hn := by
    simp_rw [dif_neg hn]
    generalize_proofs h1
    exact h1.choose_spec.2

end AddCommGroup

instance (priority := 100) divisibleByIntOfCharZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    DivisibleBy 𝕜 ℤ where
  div q n := q / n
  div_zero q := by norm_num
  div_cancel {n} q hn := by
    rw [zsmul_eq_mul, (Int.cast_commute n _).eq, div_mul_cancel₀ q (Int.cast_ne_zero.mpr hn)]

namespace Group

variable (A : Type*) [Group A]

open Int in
/-- A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive "An additive group is `ℤ`-divisible if it is `ℕ`-divisible."]
def rootableByIntOfRootableByNat [RootableBy A ℕ] : RootableBy A ℤ where
  root a z :=
    match z with
    | (n : ℕ) => RootableBy.root a n
    | -[n+1] => (RootableBy.root a (n + 1))⁻¹
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    cases n
    · rw [Int.ofNat_eq_coe, Nat.cast_ne_zero] at hn
      simp [RootableBy.root_cancel _ hn]
    · simp [RootableBy.root_cancel _ (Nat.add_one_ne_zero _)]

/-- A group is `ℕ`-rootable if it is `ℤ`-rootable
-/
@[to_additive "An additive group is `ℕ`-divisible if it `ℤ`-divisible."]
def rootableByNatOfRootableByInt [RootableBy A ℤ] : RootableBy A ℕ where
  root a n := RootableBy.root a (n : ℤ)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    -- Porting note: replaced `norm_num`
    simpa only [zpow_natCast] using RootableBy.root_cancel a (show (n : ℤ) ≠ 0 from mod_cast hn)

end Group

section Hom

variable {A B α : Type*}
variable [Zero α] [Monoid A] [Monoid B] [Pow A α] [Pow B α] [RootableBy A α]
variable (f : A → B)

/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive
      "If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also
      `α`-divisible."]
noncomputable def Function.Surjective.rootableBy (hf : Function.Surjective f)
    (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α :=
  rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
    ⟨f <| RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

@[to_additive DivisibleBy.surjective_smul]
theorem RootableBy.surjective_pow (A α : Type*) [Monoid A] [Pow A α] [Zero α] [RootableBy A α]
    {n : α} (hn : n ≠ 0) : Function.Surjective fun a : A => a ^ n := fun a =>
  ⟨RootableBy.root a n, RootableBy.root_cancel a hn⟩

end Hom

section Quotient

variable (α : Type*) {A : Type*} [CommGroup A] (B : Subgroup A)

/-- Any quotient group of a rootable group is rootable. -/
@[to_additive "Any quotient group of a divisible group is divisible"]
noncomputable instance QuotientGroup.rootableBy [RootableBy A ℕ] : RootableBy (A ⧸ B) ℕ :=
  QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

end Quotient

section Nat

@[to_additive div_one]
theorem RootableBy.root_one {M : Type*} [Monoid M] [RootableBy M ℕ] (a : M) :
    root a 1 = a := by
  rw [← pow_one (root a 1)]
  rw [root_cancel _ (by simp)]

@[to_additive zero_div]
theorem RootableBy.one_root {M : Type*} [Monoid M] [RootableBy M ℕ] [IsMulTorsionFree M] (n : ℕ) :
    root (1 : M) n = 1 := by
  obtain rfl | h := eq_or_ne n 0
  · rw [root_zero]
  · apply (pow_left_inj h).mp
    rw [root_cancel _ h]
    simp

@[to_additive div_neg]
theorem RootableBy.root_inv {M : Type*} [Group M] [RootableBy M ℕ] [IsMulTorsionFree M]
    (a : M) (n : ℕ) : root a⁻¹ n = (root a n)⁻¹ := by
  obtain rfl | h := eq_or_ne n 0
  · rw [root_zero, root_zero]
    simp
  · apply pow_left_injective h
    simp only
    rw [root_cancel _ h, inv_pow, root_cancel _ h]

instance (priority := 100) DivisibleBy.instSMul (M : Type*) [AddGroup M] [DivisibleBy M ℕ] :
    SMul ℚ M where
  smul (s : ℚ) (a : M) := div (s.num • a) s.den

@[to_additive existing DivisibleBy.instSMul]
instance (priority := 100) RootableBy.instPow (M : Type*) [Group M] [RootableBy M ℕ] :
    Pow M ℚ where
  pow (a : M) (s : ℚ) := root (a ^ s.num) s.den

@[to_additive (reorder := 4 5) DivisibleBy.qsmul_eq]
theorem RootableBy.qpow_eq {M : Type*} [Group M] [RootableBy M ℕ] (a : M) (s : ℚ) :
  a ^ s = root (a ^ s.num) s.den := rfl

@[to_additive DivisibleBy.one_qsmul]
theorem RootableBy.qpow_one {M : Type*} [Group M] [RootableBy M ℕ] (a : M) :
    a ^ (1 : ℚ) = a := by
  rw [qpow_eq, Rat.num_ofNat, zpow_one, Rat.den_ofNat, root_one]

@[to_additive DivisibleBy.zero_qsmul]
theorem RootableBy.qpow_zero {M : Type*} [Group M] [RootableBy M ℕ] (a : M) :
    a ^ (0 : ℚ) = 1 := by
  rw [qpow_eq, Rat.num_ofNat, zpow_zero, Rat.den_ofNat, root_one]

@[to_additive DivisibleBy.qsmul_zero]
theorem RootableBy.one_qpow {M : Type*} [Group M] [RootableBy M ℕ] [IsMulTorsionFree M] (s : ℚ) :
    (1 : M) ^ s = 1 := by
  rw [qpow_eq, one_zpow, one_root]

@[to_additive (reorder := 5 6 7, 5 6 7) DivisibleBy.mul_qsmul]
theorem RootableBy.qpow_mul {M : Type*} [Group M] [RootableBy M ℕ] [IsMulTorsionFree M]
    (a : M) (x : ℚ) (y : ℚ) : a ^ (x * y) = (a ^ y) ^ x := by

  rw [qpow_eq, qpow_eq, qpow_eq]
  apply (pow_left_inj (show (x.den * y.den) ≠ 0 by simp)).mp
  nth_rw 1 [Rat.den_mul_den_eq_den_mul_gcd]
  rw [mul_comm (x * y).den, pow_mul' (root _ _), root_cancel _ (by simp)]
  rw [mul_comm x.den, pow_mul' (root _ _), root_cancel _ (by simp)]
  rw [← zpow_natCast _ y.den]
  rw [zpow_comm _ x.num y.den, zpow_natCast _ y.den, root_cancel _ (by simp)]
  rw [← zpow_natCast (a ^ (x * y).num)]
  rw [← zpow_mul, ← zpow_mul, mul_comm y.den, mul_comm y.num]
  rw [← Rat.num_mul_num_eq_num_mul_gcd]

@[to_additive (reorder := 5 6 7, 5 6 7) DivisibleBy.add_qsmul]
theorem RootableBy.qpow_add {M : Type*} [CommGroup M] [RootableBy M ℕ] [IsMulTorsionFree M]
    (a : M) (x : ℚ) (y : ℚ) : a ^ (x + y) = a ^ x * a ^ y := by
  rw [qpow_eq, qpow_eq, qpow_eq]
  apply (pow_left_inj (show (x.den * y.den * (x + y).den) ≠ 0 by simp)).mp
  rw [pow_mul', root_cancel _ (by simp)]
  rw [mul_comm (x.den * y.den), mul_pow]
  nth_rw 2 [mul_comm x.den y.den]
  rw [← mul_assoc, ← mul_assoc, pow_mul' _ _ x.den, pow_mul' (root (a ^ y.num) y.den) _ y.den]
  rw [root_cancel _ (by simp), root_cancel _ (by simp)]

  rw [← zpow_natCast _ (x.den * y.den)]
  rw [← zpow_natCast _ ((x + y).den * y.den)]
  rw [← zpow_natCast _ ((x + y).den * x.den)]
  push_cast

  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add]
  rw [mul_comm ((x + y).den : ℤ), mul_comm ((x + y).den : ℤ)]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← add_mul]
  rw [Rat.add_num_den']

@[to_additive (reorder := 5 6 7) DivisibleBy.qsmul_add]
theorem RootableBy.mul_qpow {M : Type*} [CommGroup M] [RootableBy M ℕ] [IsMulTorsionFree M]
    (x : M) (y : M) (a : ℚ) : (x * y) ^ a = x ^ a * y ^ a := by
  rw [qpow_eq, qpow_eq, qpow_eq]
  apply (pow_left_inj (show a.den ≠ 0 by simp)).mp
  rw [mul_pow _ _ a.den]
  rw [root_cancel _ (by simp), root_cancel _ (by simp), root_cancel _ (by simp)]
  rw [mul_zpow]

instance (priority := 100) DivisibleBy.instMulAction (M : Type*) [AddGroup M] [DivisibleBy M ℕ]
    [IsAddTorsionFree M] : MulAction ℚ M where
  one_smul := one_qsmul
  mul_smul := mul_qsmul

instance (priority := 100) DivisibleBy.instModule (M : Type*) [AddCommGroup M] [DivisibleBy M ℕ]
    [IsAddTorsionFree M] : Module ℚ M where
  smul_zero := qsmul_zero
  zero_smul := zero_qsmul
  smul_add := qsmul_add
  add_smul := add_qsmul

end Nat
