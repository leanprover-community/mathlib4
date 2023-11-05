/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.GroupTheory.GroupAction.Opposite

#align_import algebra.hom.iterate from "leanprover-community/mathlib"@"792a2a264169d64986541c6f8f7e3bbb6acb6295"

/-!
# Iterates of monoid and ring homomorphisms

Iterate of a monoid/ring homomorphism is a monoid/ring homomorphism but it has a wrong type, so Lean
can't apply lemmas like `MonoidHom.map_one` to `f^[n] 1`. Though it is possible to define
a monoid structure on the endomorphisms, quite often we do not want to convert from
`M →* M` to `Monoid.End M` and from `f^[n]` to `f^n` just to apply a simple lemma.

So, we restate standard `*Hom.map_*` lemmas under names `*Hom.iterate_map_*`.

We also prove formulas for iterates of add/mul left/right.

## Tags

homomorphism, iterate
-/


open Function

variable {M : Type*} {N : Type*} {G : Type*} {H : Type*}

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`. -/
theorem hom_coe_pow {F : Type*} [Monoid F] (c : F → M → M) (h1 : c 1 = id)
    (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero, h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ', hmul, hom_coe_pow c h1 hmul f n]

@[to_additive (attr := simp)]
theorem iterate_map_mul {M F : Type*} [MulOneClass M]
    (f : F) (n : ℕ) (x y : M) [MulHomClass F M M] :
    f^[n] (x * y) = f^[n] x * f^[n] y :=
  Function.Semiconj₂.iterate (map_mul f) n x y

namespace MonoidHom

section

variable [MulOneClass M] [MulOneClass N]

@[to_additive (attr := simp)]
theorem iterate_map_one (f : M →* M) (n : ℕ) : f^[n] 1 = 1 :=
  iterate_fixed f.map_one n

end

variable [Monoid M] [Monoid N] [Group G] [Group H]

@[to_additive (attr := simp)]
theorem iterate_map_inv (f : G →* G) (n : ℕ) (x) : f^[n] x⁻¹ = (f^[n] x)⁻¹ :=
  Commute.iterate_left f.map_inv n x

@[to_additive (attr := simp)]
theorem iterate_map_div (f : G →* G) (n : ℕ) (x y) : f^[n] (x / y) = f^[n] x / f^[n] y :=
  Semiconj₂.iterate f.map_div n x y

theorem iterate_map_pow (f : M →* M) (n : ℕ) (a) (m : ℕ) : f^[n] (a ^ m) = f^[n] a ^ m :=
  Commute.iterate_left (fun x => f.map_pow x m) n a

theorem iterate_map_zpow (f : G →* G) (n : ℕ) (a) (m : ℤ) : f^[n] (a ^ m) = f^[n] a ^ m :=
  Commute.iterate_left (fun x => f.map_zpow x m) n a

theorem coe_pow {M} [CommMonoid M] (f : Monoid.End M) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

end MonoidHom

theorem Monoid.End.coe_pow {M} [Monoid M] (f : Monoid.End M) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

-- we define these manually so that we can pick a better argument order
namespace AddMonoidHom

variable [AddMonoid M] [AddGroup G]

theorem iterate_map_smul (f : M →+ M) (n m : ℕ) (x : M) : f^[n] (m • x) = m • f^[n] x :=
  f.toMultiplicative.iterate_map_pow n x m

attribute [to_additive (reorder := 5 6)] MonoidHom.iterate_map_pow

theorem iterate_map_zsmul (f : G →+ G) (n : ℕ) (m : ℤ) (x : G) : f^[n] (m • x) = m • f^[n] x :=
  f.toMultiplicative.iterate_map_zpow n x m

attribute [to_additive existing (reorder := 5 6)] MonoidHom.iterate_map_zpow

end AddMonoidHom

theorem AddMonoid.End.coe_pow {A} [AddMonoid A] (f : AddMonoid.End A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

namespace RingHom

section Semiring

variable {R : Type*} [Semiring R] (f : R →+* R) (n : ℕ) (x y : R)

theorem coe_pow (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) f n

theorem iterate_map_one : f^[n] 1 = 1 :=
  f.toMonoidHom.iterate_map_one n

theorem iterate_map_zero : f^[n] 0 = 0 :=
  f.toAddMonoidHom.iterate_map_zero n

theorem iterate_map_pow (a) (n m : ℕ) : f^[n] (a ^ m) = f^[n] a ^ m :=
  f.toMonoidHom.iterate_map_pow n a m

theorem iterate_map_smul (n m : ℕ) (x : R) : f^[n] (m • x) = m • f^[n] x :=
  f.toAddMonoidHom.iterate_map_smul n m x

end Semiring

variable {R : Type*} [Ring R] (f : R →+* R) (n : ℕ) (x y : R)

theorem iterate_map_sub : f^[n] (x - y) = f^[n] x - f^[n] y :=
  f.toAddMonoidHom.iterate_map_sub n x y

theorem iterate_map_neg : f^[n] (-x) = -f^[n] x :=
  f.toAddMonoidHom.iterate_map_neg n x

theorem iterate_map_zsmul (n : ℕ) (m : ℤ) (x : R) : f^[n] (m • x) = m • f^[n] x :=
  f.toAddMonoidHom.iterate_map_zsmul n m x

end RingHom

--what should be the namespace for this section?
section Monoid

variable [Monoid G] (a : G) (n : ℕ)

@[to_additive (attr := simp)]
theorem smul_iterate [MulAction G H] : (a • · : H → H)^[n] = (a ^ n • ·) :=
  funext fun b =>
    Nat.recOn n (by rw [iterate_zero, id.def, pow_zero, one_smul])
    fun n ih => by rw [iterate_succ', comp_apply, ih, pow_succ, mul_smul]

@[to_additive (attr := simp)]
theorem mul_left_iterate : (a * ·)^[n] = (a ^ n * ·) :=
  smul_iterate a n

@[to_additive (attr := simp)]
theorem mul_right_iterate : (· * a)^[n] = (· * a ^ n) :=
  smul_iterate (MulOpposite.op a) n

@[to_additive]
theorem mul_right_iterate_apply_one : (· * a)^[n] 1 = a ^ n := by simp [mul_right_iterate]

@[to_additive (attr := simp)]
theorem pow_iterate (n : ℕ) (j : ℕ) : (fun x : G => x ^ n)^[j] = fun x : G => x ^ n ^ j :=
  letI : MulAction ℕ G :=
    { smul := fun n g => g ^ n
      one_smul := pow_one
      mul_smul := fun m n g => pow_mul' g m n }
  smul_iterate n j

end Monoid

section Group

variable [Group G]

@[to_additive (attr := simp)]
theorem zpow_iterate (n : ℤ) (j : ℕ) : (fun x : G => x ^ n)^[j] = fun x => x ^ n ^ j :=
  letI : MulAction ℤ G :=
    { smul := fun n g => g ^ n
      one_smul := zpow_one
      mul_smul := fun m n g => zpow_mul' g m n }
  smul_iterate n j

end Group

section Semigroup

variable [Semigroup G] {a b c : G}

-- Porting note: need `dsimp only`, see https://leanprover.zulipchat.com/#narrow/stream/
-- 287929-mathlib4/topic/dsimp.20before.20rw/near/317063489
@[to_additive]
theorem SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Function.Semiconj (a * ·) (b * ·) (c * ·) := fun j => by
  dsimp only; rw [← mul_assoc, h.eq, mul_assoc]

@[to_additive]
theorem Commute.function_commute_mul_left (h : Commute a b) :
    Function.Commute (a * ·) (b * ·) :=
  SemiconjBy.function_semiconj_mul_left h

@[to_additive]
theorem SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j => by simp_rw [mul_assoc, ← h.eq]

@[to_additive]
theorem Commute.function_commute_mul_right (h : Commute a b) :
    Function.Commute (· * a) (· * b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroup
