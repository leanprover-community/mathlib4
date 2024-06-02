/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.GroupTheory.GroupAction.Pi

#align_import algebra.module.basic from "leanprover-community/mathlib"@"30413fc89f202a090a54d78e540963ed3de0056e"

/-!
# Further basic results about modules.

-/

open Function Set

universe u v

variable {α R M M₂ : Type*}

@[deprecated (since := "2024-04-17")]
alias map_nat_cast_smul := map_natCast_smul

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
#align map_inv_nat_cast_smul map_inv_natCast_smul

@[deprecated (since := "2024-04-17")]
alias map_inv_nat_cast_smul := map_inv_natCast_smul

theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : ℤ) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]
#align map_inv_int_cast_smul map_inv_intCast_smul

@[deprecated (since := "2024-04-17")]
alias map_inv_int_cast_smul := map_inv_intCast_smul

theorem map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (c : ℚ) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_intCast_smul f R S, map_inv_natCast_smul f R S]
#align map_rat_cast_smul map_ratCast_smul

@[deprecated (since := "2024-04-17")]
alias map_rat_cast_smul := map_ratCast_smul

theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂]
    [_instM : Module ℚ M] [_instM₂ : Module ℚ M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x :=
  map_ratCast_smul f ℚ ℚ c x
#align map_rat_smul map_rat_smul

/-- There can be at most one `Module ℚ E` structure on an additive commutative group. -/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩
#align subsingleton_rat_module subsingleton_rat_module

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on inverses of natural numbers in `R` and `S`. -/
theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : ℕ) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_natCast_smul (AddMonoidHom.id E) R S n x
#align inv_nat_cast_smul_eq inv_natCast_smul_eq

@[deprecated (since := "2024-04-17")]
alias inv_nat_cast_smul_eq := inv_natCast_smul_eq

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of integer numbers in `R` and `S`. -/
theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_intCast_smul (AddMonoidHom.id E) R S n x
#align inv_int_cast_smul_eq inv_intCast_smul_eq

@[deprecated (since := "2024-04-17")]
alias inv_int_cast_smul_eq := inv_intCast_smul_eq

/-- If `E` is a vector space over a division semiring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`. -/
theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℕ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_natCast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm
#align inv_nat_cast_smul_comm inv_natCast_smul_comm

@[deprecated (since := "2024-04-17")]
alias inv_nat_cast_smul_comm := inv_natCast_smul_comm

/-- If `E` is a vector space over a division ring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of integers in `R` -/
theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Monoid α] [Module R E] [DistribMulAction α E] (n : ℤ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_intCast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm
#align inv_int_cast_smul_comm inv_intCast_smul_comm

@[deprecated (since := "2024-04-17")]
alias inv_int_cast_smul_comm := inv_intCast_smul_comm

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on rational numbers in `R` and `S`. -/
theorem ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x :=
  map_ratCast_smul (AddMonoidHom.id E) R S r x
#align rat_cast_smul_eq ratCast_smul_eq

@[deprecated (since := "2024-04-17")]
alias rat_cast_smul_eq := ratCast_smul_eq

instance IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [Module ℚ R] [Module ℚ M] : IsScalarTower ℚ R M where
  smul_assoc r x y := map_rat_smul ((smulAddHom R M).flip y) r x
#align is_scalar_tower.rat IsScalarTower.rat

instance SMulCommClass.rat {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]
    [Module ℚ M] : SMulCommClass ℚ R M where
  smul_comm r x y := (map_rat_smul (smulAddHom R M x) r y).symm
#align smul_comm_class.rat SMulCommClass.rat

instance SMulCommClass.rat' {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]
    [Module ℚ M] : SMulCommClass R ℚ M :=
  SMulCommClass.symm _ _ _
#align smul_comm_class.rat' SMulCommClass.rat'

section NoZeroSMulDivisors

section Module

variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

instance [NoZeroSMulDivisors ℤ M] : NoZeroSMulDivisors ℕ M :=
  ⟨fun {c x} hcx ↦ by rwa [nsmul_eq_smul_cast ℤ c x, smul_eq_zero, Nat.cast_eq_zero] at hcx⟩

end Module

section GroupWithZero

variable [GroupWithZero R] [AddMonoid M] [DistribMulAction R M]

-- see note [lower instance priority]
/-- This instance applies to `DivisionSemiring`s, in particular `NNReal` and `NNRat`. -/
instance (priority := 100) GroupWithZero.toNoZeroSMulDivisors : NoZeroSMulDivisors R M :=
  ⟨fun {a _} h ↦ or_iff_not_imp_left.2 fun ha ↦ (smul_eq_zero_iff_eq <| Units.mk0 a ha).1 h⟩
#align group_with_zero.to_no_zero_smul_divisors GroupWithZero.toNoZeroSMulDivisors

end GroupWithZero

-- see note [lower instance priority]
instance (priority := 100) RatModule.noZeroSMulDivisors [AddCommGroup M] [Module ℚ M] :
    NoZeroSMulDivisors ℤ M :=
  ⟨fun {k} {x : M} h => by
    simpa only [zsmul_eq_smul_cast ℚ k x, smul_eq_zero, Rat.zero_iff_num_zero] using h⟩
  -- Porting note: old proof was:
  --⟨fun {k x} h => by simpa [zsmul_eq_smul_cast ℚ k x] using h⟩
#align rat_module.no_zero_smul_divisors RatModule.noZeroSMulDivisors

end NoZeroSMulDivisors

namespace Function

lemma support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf ↦
  hfg <| by rw [Pi.smul_apply', hf, zero_smul]
#align function.support_smul_subset_left Function.support_smul_subset_left

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.
lemma support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support g :=
  fun x hbf hf ↦ hbf <| by rw [Pi.smul_apply', hf, smul_zero]

lemma support_const_smul_of_ne_zero [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M]
    (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun x ↦ by simp only [hc, mem_support, Pi.smul_apply, Ne, smul_eq_zero, false_or_iff]
#align function.support_const_smul_of_ne_zero Function.support_const_smul_of_ne_zero

lemma support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun _ => smul_ne_zero_iff
#align function.support_smul Function.support_smul

lemma support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α → M) :
    support (a • f) ⊆ support f := support_smul_subset_right (fun _ ↦ a) f
#align function.support_smul_subset_right Function.support_const_smul_subset

end Function

namespace Set
section SMulZeroClass
variable [Zero R] [Zero M] [SMulZeroClass R M]

lemma indicator_smul_apply (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]
#align set.indicator_smul_apply Set.indicator_smul_apply

lemma indicator_smul (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ r a • indicator s f a :=
  funext <| indicator_smul_apply s r f
#align set.indicator_smul Set.indicator_smul

lemma indicator_const_smul_apply (s : Set α) (r : R) (f : α → M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a :=
  indicator_smul_apply s (fun _ ↦ r) f a
#align set.indicator_const_smul_apply Set.indicator_const_smul_apply

lemma indicator_const_smul (s : Set α) (r : R) (f : α → M) :
    indicator s (r • f ·) = (r • indicator s f ·) :=
  funext <| indicator_const_smul_apply s r f
#align set.indicator_const_smul Set.indicator_const_smul

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
end Set

assert_not_exists Multiset
