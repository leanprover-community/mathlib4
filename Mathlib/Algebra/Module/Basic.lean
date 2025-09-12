/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Ring.Invertible

/-!
# Further basic results about modules.

-/

assert_not_exists Nonneg.inv Multiset

open Function Set

universe u v

variable {α R M M₂ : Type*}

@[simp]
theorem Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) :
    -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]

@[simp]
theorem invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Module R M]
    [Invertible (2 : R)] (x : M) :
    (⅟2 : R) • x + (⅟2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _

theorem map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [DivisionSemiring R] [DivisionSemiring S] [Module R M]
    [Module S M₂] (n : ℕ) (x : M) : f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices ∀ y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x), ← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices ∀ y, f y = 0 by simp [this]
    clear x
    intro x
    rw [← smul_inv_smul₀ hR x, map_natCast_smul f R S, hS, zero_smul]
  · rw [← inv_smul_smul₀ hS (f _), ← map_natCast_smul f R S, smul_inv_smul₀ hR]

theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : ℤ) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on inverses of natural numbers in `R` and `S`. -/
theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : ℕ) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_natCast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of integer numbers in `R` and `S`. -/
theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_intCast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over a division semiring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`. -/
theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℕ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_natCast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm

/-- If `E` is a vector space over a division ring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of integers in `R` -/
theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℤ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_intCast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm

namespace Function

lemma support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf ↦
  hfg <| by rw [Pi.smul_apply', hf, zero_smul]

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.
lemma support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support g :=
  fun x hbf hf ↦ hbf <| by rw [Pi.smul_apply', hf, smul_zero]

lemma support_const_smul_of_ne_zero [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M]
    (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun x ↦ by simp only [hc, mem_support, Pi.smul_apply, Ne, smul_eq_zero, false_or]

lemma support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun _ => smul_ne_zero_iff

lemma support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α → M) :
    support (a • f) ⊆ support f := support_smul_subset_right (fun _ ↦ a) f

end Function

namespace Set
section SMulZeroClass
variable [Zero M] [SMulZeroClass R M]

lemma indicator_smul_apply (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

lemma indicator_smul (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ r a • indicator s f a :=
  funext <| indicator_smul_apply s r f

lemma indicator_const_smul_apply (s : Set α) (r : R) (f : α → M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a :=
  indicator_smul_apply s (fun _ ↦ r) f a

lemma indicator_const_smul (s : Set α) (r : R) (f : α → M) :
    indicator s (r • f ·) = (r • indicator s f ·) :=
  funext <| indicator_const_smul_apply s r f

end SMulZeroClass

section SMulWithZero
variable [Zero R] [Zero M] [SMulWithZero R M]

lemma indicator_smul_apply_left (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = indicator s r a • f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

lemma indicator_smul_left (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ indicator s r a • f a :=
  funext <| indicator_smul_apply_left _ _ _

lemma indicator_smul_const_apply (s : Set α) (r : α → R) (m : M) (a : α) :
    indicator s (r · • m) a = indicator s r a • m := indicator_smul_apply_left _ _ _ _

lemma indicator_smul_const (s : Set α) (r : α → R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) :=
  funext <| indicator_smul_const_apply _ _ _

end SMulWithZero

section MulZeroOneClass

variable [MulZeroOneClass R]

lemma smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α → R) a = s.indicator (fun _ ↦ r) a := by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end MulZeroOneClass
end Set
