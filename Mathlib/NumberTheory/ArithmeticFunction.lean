/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Module.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

#align_import number_theory.arithmetic_function from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
 * An arithmetic function `f` `IsMultiplicative` when `x.coprime y → f (x * y) = f x * f y`.
 * The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `ArithmeticFunction R`, which use Dirichlet multiplication.
 * `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
 * `σ k` is the arithmetic function such that `σ k x = ∑ y in divisors x, y ^ k` for `0 < x`.
 * `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
 * `id` is the identity arithmetic function on `ℕ`.
 * `ω n` is the number of distinct prime factors of `n`.
 * `Ω n` is the number of prime factors of `n` counted with multiplicity.
 * `μ` is the Möbius function (spelled `moebius` in code).

## Main Results
 * Several forms of Möbius inversion:
 * `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
 * `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
 * `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
 * `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
 * And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
 * `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
 * `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
 * `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
 * `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Notation
The arithmetic functions `ζ` and `σ` have Greek letter names, which are localized notation in
the namespace `ArithmeticFunction`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/

open Finset

open BigOperators

namespace Nat

variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `ArithmeticFunctions` is by
  Dirichlet convolution. -/
def ArithmeticFunction [Zero R] :=
  ZeroHom ℕ R
#align nat.arithmetic_function Nat.ArithmeticFunction

instance ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R) :=
  inferInstanceAs (Zero (ZeroHom ℕ R))

instance [Zero R] : Inhabited (ArithmeticFunction R) := inferInstanceAs (Inhabited (ZeroHom ℕ R))

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

--  porting note: used to be `CoeFun`
instance : FunLike (ArithmeticFunction R) ℕ fun _ ↦ R :=
  inferInstanceAs (FunLike (ZeroHom ℕ R) ℕ fun _ ↦ R)

@[simp]
theorem toFun_eq (f : ArithmeticFunction R) : f.toFun = f := rfl
#align nat.arithmetic_function.to_fun_eq Nat.ArithmeticFunction.toFun_eq

@[simp]
theorem coe_mk (f : ℕ → R) (hf) : @FunLike.coe (ArithmeticFunction R) _ _ _
    (ZeroHom.mk f hf) = f := rfl

@[simp]
theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
  ZeroHom.map_zero' f
#align nat.arithmetic_function.map_zero Nat.ArithmeticFunction.map_zero

theorem coe_inj {f g : ArithmeticFunction R} : (f : ℕ → R) = g ↔ f = g :=
  FunLike.coe_fn_eq
#align nat.arithmetic_function.coe_inj Nat.ArithmeticFunction.coe_inj

@[simp]
theorem zero_apply {x : ℕ} : (0 : ArithmeticFunction R) x = 0 :=
  ZeroHom.zero_apply x
#align nat.arithmetic_function.zero_apply Nat.ArithmeticFunction.zero_apply

@[ext]
theorem ext ⦃f g : ArithmeticFunction R⦄ (h : ∀ x, f x = g x) : f = g :=
  ZeroHom.ext h
#align nat.arithmetic_function.ext Nat.ArithmeticFunction.ext

theorem ext_iff {f g : ArithmeticFunction R} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align nat.arithmetic_function.ext_iff Nat.ArithmeticFunction.ext_iff

section One

variable [One R]

instance one : One (ArithmeticFunction R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
  rfl
#align nat.arithmetic_function.one_apply Nat.ArithmeticFunction.one_apply

@[simp]
theorem one_one : (1 : ArithmeticFunction R) 1 = 1 :=
  rfl
#align nat.arithmetic_function.one_one Nat.ArithmeticFunction.one_one

@[simp]
theorem one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : ArithmeticFunction R) x = 0 :=
  if_neg h
#align nat.arithmetic_function.one_apply_ne Nat.ArithmeticFunction.one_apply_ne

end One

end Zero

/-- Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We cannot inline
this in `natCoe` because it gets unfolded too much. -/
@[coe]  -- porting note: added `coe` tag.
def natToArithmeticFunction [AddMonoidWithOne R] :
    (ArithmeticFunction ℕ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction ℕ) (ArithmeticFunction R) :=
  ⟨natToArithmeticFunction⟩
#align nat.arithmetic_function.nat_coe Nat.ArithmeticFunction.natCoe

@[simp]
theorem natCoe_nat (f : ArithmeticFunction ℕ) : natToArithmeticFunction f = f :=
  ext fun _ => cast_id _
#align nat.arithmetic_function.nat_coe_nat Nat.ArithmeticFunction.natCoe_nat

@[simp]
theorem natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x :=
  rfl
#align nat.arithmetic_function.nat_coe_apply Nat.ArithmeticFunction.natCoe_apply

/-- Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We cannot inline
this in `intCoe` because it gets unfolded too much. -/
@[coe]
def ofInt [AddGroupWithOne R] :
    (ArithmeticFunction ℤ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction ℤ) (ArithmeticFunction R) :=
  ⟨ofInt⟩
#align nat.arithmetic_function.int_coe Nat.ArithmeticFunction.intCoe

@[simp]
theorem intCoe_int (f : ArithmeticFunction ℤ) : ofInt f = f :=
  ext fun _ => Int.cast_id
#align nat.arithmetic_function.int_coe_int Nat.ArithmeticFunction.intCoe_int

@[simp]
theorem intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction ℤ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x := rfl
#align nat.arithmetic_function.int_coe_apply Nat.ArithmeticFunction.intCoe_apply

@[simp]
theorem coe_coe [AddGroupWithOne R] {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℤ) : ArithmeticFunction R) = (f : ArithmeticFunction R) := by
  ext
  simp
#align nat.arithmetic_function.coe_coe Nat.ArithmeticFunction.coe_coe

@[simp]
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction ℕ) : ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]
#align nat.arithmetic_function.nat_coe_one Nat.ArithmeticFunction.natCoe_one

@[simp]
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction ℤ) :
    ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]
#align nat.arithmetic_function.int_coe_one Nat.ArithmeticFunction.intCoe_one

section AddMonoid

variable [AddMonoid R]

instance add : Add (ArithmeticFunction R) :=
  ⟨fun f g => ⟨fun n => f n + g n, by simp⟩⟩

@[simp]
theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
  rfl
#align nat.arithmetic_function.add_apply Nat.ArithmeticFunction.add_apply

instance instAddMonoid : AddMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.zero R,
    ArithmeticFunction.add with
    add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
    zero_add := fun _ => ext fun _ => zero_add _
    add_zero := fun _ => ext fun _ => add_zero _ }
#align nat.arithmetic_function.add_monoid Nat.ArithmeticFunction.instAddMonoid

end AddMonoid

instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid,
    ArithmeticFunction.one with
    natCast := fun n => ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
    natCast_zero := by ext; simp
    natCast_succ := fun n => by ext x; by_cases h : x = 1 <;> simp [h] }
#align nat.arithmetic_function.add_monoid_with_one Nat.ArithmeticFunction.instAddMonoidWithOne

instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _ }

instance [AddGroup R] : AddGroup (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with
    neg := fun f => ⟨fun n => -f n, by simp⟩
    add_left_neg := fun _ => ext fun _ => add_left_neg _ }

instance [AddCommGroup R] : AddCommGroup (ArithmeticFunction R) :=
  { show AddGroup (ArithmeticFunction R) by infer_instance with
    add_comm := fun _ _ ↦ add_comm _ _ }

section SMul

variable {M : Type*} [Zero R] [AddCommMonoid M] [SMul R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : SMul (ArithmeticFunction R) (ArithmeticFunction M) :=
  ⟨fun f g => ⟨fun n => ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩⟩

@[simp]
theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
    (f • g) n = ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd :=
  rfl
#align nat.arithmetic_function.smul_apply Nat.ArithmeticFunction.smul_apply

end SMul

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance [Semiring R] : Mul (ArithmeticFunction R) :=
  ⟨(· • ·)⟩

@[simp]
theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f * g) n = ∑ x in divisorsAntidiagonal n, f x.fst * g x.snd :=
  rfl
#align nat.arithmetic_function.mul_apply Nat.ArithmeticFunction.mul_apply

theorem mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 * g 1 := by simp
#align nat.arithmetic_function.mul_apply_one Nat.ArithmeticFunction.mul_apply_one

@[simp, norm_cast]
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  simp
#align nat.arithmetic_function.nat_coe_mul Nat.ArithmeticFunction.natCoe_mul

@[simp, norm_cast]
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  simp
#align nat.arithmetic_function.int_coe_mul Nat.ArithmeticFunction.intCoe_mul

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, Finset.sum_sigma']
  apply Finset.sum_bij
  pick_goal 5
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _H
    exact ⟨(k, l * j), (l, j)⟩
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H
    simp only [Finset.mem_sigma, mem_divisorsAntidiagonal] at H ⊢
    rcases H with ⟨⟨rfl, n0⟩, rfl, i0⟩
    refine' ⟨⟨(mul_assoc _ _ _).symm, n0⟩, trivial, _⟩
    rw [mul_ne_zero_iff] at *
    exact ⟨i0.2, n0.2⟩
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _H
    simp only [mul_assoc]
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩ H₁ H₂
    simp only [Finset.mem_sigma, mem_divisorsAntidiagonal, and_imp, Prod.mk.inj_iff, add_comm,
      heq_iff_eq] at H₁ H₂ ⊢
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq, and_imp] -- porting note: added
    rintro h h2 rfl rfl
    subst h -- porting note: added.  The `rintro h ...` above was `rintro rfl ...`
    exact ⟨⟨Eq.trans H₁.2.1.symm H₂.2.1, rfl⟩, rfl, rfl⟩
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H
    refine' ⟨⟨(i * k, l), (i, k)⟩, _, _⟩
    · simp only [Finset.mem_sigma, mem_divisorsAntidiagonal] at H ⊢
      rcases H with ⟨⟨rfl, n0⟩, rfl, j0⟩
      refine' ⟨⟨mul_assoc _ _ _, n0⟩, trivial, _⟩
      rw [mul_ne_zero_iff] at *
      exact ⟨n0.1, j0.1⟩
    · simp only [true_and_iff, mem_divisorsAntidiagonal, and_true_iff, Prod.mk.inj_iff,
        eq_self_iff_true, Ne.def, mem_sigma, heq_iff_eq] at H ⊢
      rw [H.2.1]
#align nat.arithmetic_function.mul_smul' Nat.ArithmeticFunction.mul_smul'

theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
  ext x
  rw [smul_apply]
  by_cases x0 : x = 0
  · simp [x0]
  have h : {(1, x)} ⊆ divisorsAntidiagonal x := by simp [x0]
  rw [← sum_subset h]
  · simp
  intro y ymem ynmem
  have y1ne : y.fst ≠ 1 := by
    intro con
    simp only [Con, mem_divisorsAntidiagonal, one_mul, Ne.def] at ymem
    simp only [mem_singleton, Prod.ext_iff] at ynmem
    -- porting note: `tauto` worked from here.
    cases y
    subst con
    simp only [true_and, one_mul, x0, not_false_eq_true, and_true] at ynmem ymem
    tauto

  simp [y1ne]
#align nat.arithmetic_function.one_smul' Nat.ArithmeticFunction.one_smul'

end Module

section Semiring

variable [Semiring R]

instance instMonoid : Monoid (ArithmeticFunction R) :=
  { one := One.one
    mul := Mul.mul
    one_mul := one_smul'
    mul_one := fun f => by
      ext x
      rw [mul_apply]
      by_cases x0 : x = 0
      · simp [x0]
      have h : {(x, 1)} ⊆ divisorsAntidiagonal x := by simp [x0]
      rw [← sum_subset h]
      · simp
      intro y ymem ynmem
      have y2ne : y.snd ≠ 1 := by
        intro con
        cases y; subst con -- porting note: added
        simp only [Con, mem_divisorsAntidiagonal, mul_one, Ne.def] at ymem
        simp only [mem_singleton, Prod.ext_iff] at ynmem
        tauto
      simp [y2ne]
    mul_assoc := mul_smul' }
#align nat.arithmetic_function.monoid Nat.ArithmeticFunction.instMonoid

instance instSemiring : Semiring (ArithmeticFunction R) :=
  -- porting note: I reorganized this instance
  { ArithmeticFunction.instAddMonoidWithOne,
    ArithmeticFunction.instMonoid,
    ArithmeticFunction.instAddCommMonoid with
    zero_mul := fun f => by
      ext
      simp only [mul_apply, zero_mul, sum_const_zero, zero_apply]
    mul_zero := fun f => by
      ext
      simp only [mul_apply, sum_const_zero, mul_zero, zero_apply]
    left_distrib := fun a b c => by
      ext
      simp only [← sum_add_distrib, mul_add, mul_apply, add_apply]
    right_distrib := fun a b c => by
      ext
      simp only [← sum_add_distrib, add_mul, mul_apply, add_apply] }
#align nat.arithmetic_function.semiring Nat.ArithmeticFunction.instSemiring

end Semiring

instance [CommSemiring R] : CommSemiring (ArithmeticFunction R) :=
  { ArithmeticFunction.instSemiring with
    mul_comm := fun f g => by
      ext
      rw [mul_apply, ← map_swap_divisorsAntidiagonal, sum_map]
      simp [mul_comm] }

instance [CommRing R] : CommRing (ArithmeticFunction R) :=
  { ArithmeticFunction.instSemiring with
    add_left_neg := add_left_neg
    mul_comm := mul_comm }

instance {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (ArithmeticFunction R) (ArithmeticFunction M) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_add r x y := by
    ext
    simp only [sum_add_distrib, smul_add, smul_apply, add_apply]
  smul_zero r := by
    ext
    simp only [smul_apply, sum_const_zero, smul_zero, zero_apply]
  add_smul r s x := by
    ext
    simp only [add_smul, sum_add_distrib, smul_apply, add_apply]
  zero_smul r := by
    ext
    simp only [smul_apply, sum_const_zero, zero_smul, zero_apply]

section Zeta

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann `ζ`.  -/
def zeta : ArithmeticFunction ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩
#align nat.arithmetic_function.zeta Nat.ArithmeticFunction.zeta

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "ζ" => Nat.ArithmeticFunction.zeta

@[simp]
theorem zeta_apply {x : ℕ} : ζ x = if x = 0 then 0 else 1 :=
  rfl
#align nat.arithmetic_function.zeta_apply Nat.ArithmeticFunction.zeta_apply

theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 :=
  if_neg h
#align nat.arithmetic_function.zeta_apply_ne Nat.ArithmeticFunction.zeta_apply_ne

-- Porting note: removed `@[simp]`, LHS not in normal form
theorem coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [Module R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    ((↑ζ : ArithmeticFunction R) • f) x = ∑ i in divisors x, f i := by
  rw [smul_apply]
  trans ∑ i in divisorsAntidiagonal x, f i.snd
  · refine' sum_congr rfl fun i hi => _
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]
#align nat.arithmetic_function.coe_zeta_smul_apply Nat.ArithmeticFunction.coe_zeta_smul_apply

-- Porting note: removed `@[simp]` to make the linter happy.
theorem coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (↑ζ * f) x = ∑ i in divisors x, f i :=
  coe_zeta_smul_apply
#align nat.arithmetic_function.coe_zeta_mul_apply Nat.ArithmeticFunction.coe_zeta_mul_apply

-- Porting note: removed `@[simp]` to make the linter happy.
theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (f * ζ) x = ∑ i in divisors x, f i := by
  rw [mul_apply]
  trans ∑ i in divisorsAntidiagonal x, f i.1
  · refine' sum_congr rfl fun i hi => _
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one]
  · rw [← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
#align nat.arithmetic_function.coe_mul_zeta_apply Nat.ArithmeticFunction.coe_mul_zeta_apply

theorem zeta_mul_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (ζ * f) x = ∑ i in divisors x, f i :=
  coe_zeta_mul_apply
  --porting note: was `by rw [← nat_coe_nat ζ, coe_zeta_mul_apply]`.  Is this `theorem` obsolete?
#align nat.arithmetic_function.zeta_mul_apply Nat.ArithmeticFunction.zeta_mul_apply

theorem mul_zeta_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (f * ζ) x = ∑ i in divisors x, f i :=
  coe_mul_zeta_apply
  --porting note: was `by rw [← natCoe_nat ζ, coe_mul_zeta_apply]`.  Is this `theorem` obsolete=
#align nat.arithmetic_function.mul_zeta_apply Nat.ArithmeticFunction.mul_zeta_apply

end Zeta

open ArithmeticFunction

section Pmul

/-- This is the pointwise product of `ArithmeticFunction`s. -/
def pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun x => f x * g x, by simp⟩
#align nat.arithmetic_function.pmul Nat.ArithmeticFunction.pmul

@[simp]
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : ℕ} : f.pmul g x = f x * g x :=
  rfl
#align nat.arithmetic_function.pmul_apply Nat.ArithmeticFunction.pmul_apply

theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  simp [mul_comm]
#align nat.arithmetic_function.pmul_comm Nat.ArithmeticFunction.pmul_comm

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  cases x <;> simp [Nat.succ_ne_zero]
#align nat.arithmetic_function.pmul_zeta Nat.ArithmeticFunction.pmul_zeta

@[simp]
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  cases x <;> simp [Nat.succ_ne_zero]
#align nat.arithmetic_function.zeta_pmul Nat.ArithmeticFunction.zeta_pmul

end NonAssocSemiring

variable [Semiring R]

/-- This is the pointwise power of `ArithmeticFunction`s. -/
def ppow (f : ArithmeticFunction R) (k : ℕ) : ArithmeticFunction R :=
  if h0 : k = 0 then ζ
  else
    ⟨fun x => f x ^ k, by
      -- porting note: added next line
      dsimp only
      rw [map_zero]
      exact zero_pow (Nat.pos_of_ne_zero h0)⟩
#align nat.arithmetic_function.ppow Nat.ArithmeticFunction.ppow

@[simp]
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]
#align nat.arithmetic_function.ppow_zero Nat.ArithmeticFunction.ppow_zero

@[simp]
theorem ppow_apply {f : ArithmeticFunction R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow, dif_neg (ne_of_gt kpos)]
  rfl
#align nat.arithmetic_function.ppow_apply Nat.ArithmeticFunction.ppow_apply

theorem ppow_succ {f : ArithmeticFunction R} {k : ℕ} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ]
  induction k <;> simp
#align nat.arithmetic_function.ppow_succ Nat.ArithmeticFunction.ppow_succ

theorem ppow_succ' {f : ArithmeticFunction R} {k : ℕ} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ']
  induction k <;> simp
#align nat.arithmetic_function.ppow_succ' Nat.ArithmeticFunction.ppow_succ'

end Pmul

section Pdiv

/-- This is the pointwise division of `ArithmeticFunction`s. -/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, ne_eq, not_true, div_zero]⟩

@[simp]
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coersion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  cases n <;> simp [succ_ne_zero]

end Pdiv

/-- Multiplicative functions -/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n
#align nat.arithmetic_function.is_multiplicative Nat.ArithmeticFunction.IsMultiplicative

namespace IsMultiplicative

section MonoidWithZero

variable [MonoidWithZero R]

@[simp]
theorem map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1 :=
  h.1
#align nat.arithmetic_function.is_multiplicative.map_one Nat.ArithmeticFunction.IsMultiplicative.map_one

@[simp]
theorem map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : ℕ}
    (h : m.Coprime n) : f (m * n) = f m * f n :=
  hf.2 h
#align nat.arithmetic_function.is_multiplicative.map_mul_of_coprime Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime

end MonoidWithZero

theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι → ℕ) {f : Nat.ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (Coprime on g)) :
    f (∏ i in s, g i) = ∏ i in s, f (g i) := by
  classical
    induction' s using Finset.induction_on with a s has ih hs
    · simp [hf]
    rw [coe_insert, Set.pairwise_insert_of_symmetric (Coprime.symmetric.comap g)] at hs
    rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.coprime_prod_right fun i hi => hs.2 _ hi (hi.ne_of_not_mem has).symm
#align nat.arithmetic_function.is_multiplicative.map_prod Nat.ArithmeticFunction.IsMultiplicative.map_prod

theorem nat_cast {f : ArithmeticFunction ℕ} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
#align nat.arithmetic_function.is_multiplicative.nat_cast Nat.ArithmeticFunction.IsMultiplicative.nat_cast

theorem int_cast {f : ArithmeticFunction ℤ} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
#align nat.arithmetic_function.is_multiplicative.int_cast Nat.ArithmeticFunction.IsMultiplicative.int_cast

theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f * g) :=
  ⟨by
    -- porting note was `simp [hf, hg]`.
    simp [hf.1, hg.1],
  by
    simp only [mul_apply]
    intro m n cop
    rw [sum_mul_sum]
    symm
    apply sum_bij fun (x : (ℕ × ℕ) × ℕ × ℕ) _h => (x.1.1 * x.2.1, x.1.2 * x.2.2)
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      simp only [mem_divisorsAntidiagonal, Nat.mul_eq_zero, Ne.def]
      constructor
      · ring
      rw [Nat.mul_eq_zero] at *
      apply not_or_of_not ha hb
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      dsimp only
      rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
        hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
      ring
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at hab
      rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at hcd
      simp only [Prod.mk.inj_iff] at h
      ext <;> dsimp only
      · trans Nat.gcd (a1 * a2) (a1 * b1)
        · rw [Nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          rw [← hcd.1.1, h.1, Nat.gcd_mul_left,
            cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · trans Nat.gcd (a1 * a2) (a2 * b2)
        · rw [mul_comm, Nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
            mul_one]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          rw [← hcd.1.1, h.2, mul_comm, Nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]
      · trans Nat.gcd (b1 * b2) (a1 * b1)
        · rw [mul_comm, Nat.gcd_mul_right,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mul]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          rw [← hcd.2.1, h.1, mul_comm c1 d1, Nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one]
      · trans Nat.gcd (b1 * b2) (a2 * b2)
        · rw [Nat.gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,
            one_mul]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          rw [← hcd.2.1, h.2, Nat.gcd_mul_right,
            cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
    · rintro ⟨b1, b2⟩ h
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
      simp only [exists_prop, Prod.mk.inj_iff, Ne.def, mem_product, mem_divisorsAntidiagonal]
      rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
        Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
      · rw [Nat.mul_eq_zero, not_or] at h
        simp [h.2.1, h.2.2]
      rw [mul_comm n m, h.1]⟩
#align nat.arithmetic_function.is_multiplicative.mul Nat.ArithmeticFunction.IsMultiplicative.mul

theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun {m n} cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩
#align nat.arithmetic_function.is_multiplicative.pmul Nat.ArithmeticFunction.IsMultiplicative.pmul

theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨ by simp [hf, hg], fun {m n} cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop,
      div_eq_mul_inv, mul_inv]
    apply mul_mul_mul_comm ⟩

/-- For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
nonrec  -- porting note: added
theorem multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) :=
  multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn
#align nat.arithmetic_function.is_multiplicative.multiplicative_factorization Nat.ArithmeticFunction.IsMultiplicative.multiplicative_factorization

/-- A recapitulation of the definition of multiplicative that is simpler for proofs -/
theorem iff_ne_zero [MonoidWithZero R] {f : ArithmeticFunction R} :
    IsMultiplicative f ↔
      f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n := by
  refine' and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => _⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn
#align nat.arithmetic_function.is_multiplicative.iff_ne_zero Nat.ArithmeticFunction.IsMultiplicative.iff_ne_zero

/-- Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers -/
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : ℕ, Nat.Prime p → f (p ^ i) = g (p ^ i) := by
  constructor
  · intro h p i _
    rw [h]
  intro h
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn, multiplicative_factorization g hg hn]
  exact Finset.prod_congr rfl fun p hp ↦ h p _ (Nat.prime_of_mem_primeFactors hp)
#align nat.arithmetic_function.is_multiplicative.eq_iff_eq_on_prime_powers Nat.ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers

theorem lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} :
    f (x.lcm y) * f (x.gcd y) = f x * f y := by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y ≠ 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := lcm_ne_zero hx hy
  have hfi_zero : ∀ {i}, f (i ^ 0) = 1
  · intro i; rw [pow_zero, hf.1]
  iterate 4 rw [hf.multiplicative_factorization f (by assumption),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hfi_zero)
      (s := (x.primeFactors ⊔ y.primeFactors))]
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rcases Nat.le_or_le (x.factorization p) (y.factorization p) with h | h <;>
      simp only [factorization_lcm hx hy, ge_iff_le, Finsupp.sup_apply, h, sup_of_le_right,
        sup_of_le_left, inf_of_le_right, Nat.factorization_gcd hx hy, Finsupp.inf_apply,
        inf_of_le_left, mul_comm]
  · apply Finset.subset_union_right
  · apply Finset.subset_union_left
  · rw [factorization_gcd hx hy, Finsupp.support_inf, Finset.sup_eq_union]
    apply Finset.inter_subset_union
  · simp [factorization_lcm hx hy]

end IsMultiplicative

section SpecialFunctions

/-- The identity on `ℕ` as an `ArithmeticFunction`.  -/
nonrec  -- porting note: added
def id : ArithmeticFunction ℕ :=
  ⟨id, rfl⟩
#align nat.arithmetic_function.id Nat.ArithmeticFunction.id

@[simp]
theorem id_apply {x : ℕ} : id x = x :=
  rfl
#align nat.arithmetic_function.id_apply Nat.ArithmeticFunction.id_apply

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : ArithmeticFunction ℕ :=
  id.ppow k
#align nat.arithmetic_function.pow Nat.ArithmeticFunction.pow

@[simp]
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k
  · simp [pow]
  rename_i k  -- porting note: added
  simp [pow, (ne_of_lt (Nat.succ_pos k)).symm]
#align nat.arithmetic_function.pow_apply Nat.ArithmeticFunction.pow_apply

theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp
#align nat.arithmetic_function.pow_zero_eq_zeta Nat.ArithmeticFunction.pow_zero_eq_zeta

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d in divisors n, d ^ k, by simp⟩
#align nat.arithmetic_function.sigma Nat.ArithmeticFunction.sigma

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "σ" => Nat.ArithmeticFunction.sigma

theorem sigma_apply {k n : ℕ} : σ k n = ∑ d in divisors n, d ^ k :=
  rfl
#align nat.arithmetic_function.sigma_apply Nat.ArithmeticFunction.sigma_apply

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d in divisors n, d := by simp [sigma_apply]
#align nat.arithmetic_function.sigma_one_apply Nat.ArithmeticFunction.sigma_one_apply

theorem sigma_zero_apply (n : ℕ) : σ 0 n = (divisors n).card := by simp [sigma_apply]
#align nat.arithmetic_function.sigma_zero_apply Nat.ArithmeticFunction.sigma_zero_apply

theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  rw [sigma_zero_apply, divisors_prime_pow hp, card_map, card_range]
#align nat.arithmetic_function.sigma_zero_apply_prime_pow Nat.ArithmeticFunction.sigma_zero_apply_prime_pow

theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  rw [sigma, zeta_mul_apply]
  apply sum_congr rfl
  intro x hx
  rw [pow_apply, if_neg (not_and_of_not_right _ _)]
  contrapose! hx
  simp [hx]
#align nat.arithmetic_function.zeta_mul_pow_eq_sigma Nat.ArithmeticFunction.zeta_mul_pow_eq_sigma

theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2
    ⟨by simp, by
      intro m n hm _hn hmn
      rcases eq_or_ne m 1 with (rfl | hm')
      · simp
      rw [one_apply_ne, one_apply_ne hm', zero_mul]
      rw [Ne.def, mul_eq_one, not_and_or]
      exact Or.inl hm'⟩
#align nat.arithmetic_function.is_multiplicative_one Nat.ArithmeticFunction.isMultiplicative_one

theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align nat.arithmetic_function.is_multiplicative_zeta Nat.ArithmeticFunction.isMultiplicative_zeta

theorem isMultiplicative_id : IsMultiplicative ArithmeticFunction.id :=
  ⟨rfl, fun {_ _} _ => rfl⟩
#align nat.arithmetic_function.is_multiplicative_id Nat.ArithmeticFunction.isMultiplicative_id

theorem IsMultiplicative.ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction' k with k hi
  · exact isMultiplicative_zeta.nat_cast
  · rw [ppow_succ]
    apply hf.pmul hi
#align nat.arithmetic_function.is_multiplicative.ppow Nat.ArithmeticFunction.IsMultiplicative.ppow

theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
#align nat.arithmetic_function.is_multiplicative_pow Nat.ArithmeticFunction.isMultiplicative_pow

theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow
#align nat.arithmetic_function.is_multiplicative_sigma Nat.ArithmeticFunction.isMultiplicative_sigma

/-- `Ω n` is the number of prime factors of `n`. -/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.length, by simp⟩
#align nat.arithmetic_function.card_factors Nat.ArithmeticFunction.cardFactors

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "Ω" => Nat.ArithmeticFunction.cardFactors

theorem cardFactors_apply {n : ℕ} : Ω n = n.factors.length :=
  rfl
#align nat.arithmetic_function.card_factors_apply Nat.ArithmeticFunction.cardFactors_apply

@[simp]
theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors]
#align nat.arithmetic_function.card_factors_one Nat.ArithmeticFunction.cardFactors_one

theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine' ⟨fun h => _, fun h => List.length_eq_one.2 ⟨n, factors_prime h⟩⟩
  cases' n with n
  · contrapose! h
    simp
  rcases List.length_eq_one.1 h with ⟨x, hx⟩
  rw [← prod_factors n.succ_ne_zero, hx, List.prod_singleton]
  apply prime_of_mem_factors
  rw [hx, List.mem_singleton]
#align nat.arithmetic_function.card_factors_eq_one_iff_prime Nat.ArithmeticFunction.cardFactors_eq_one_iff_prime

theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]
#align nat.arithmetic_function.card_factors_mul Nat.ArithmeticFunction.cardFactors_mul

theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  revert h0
  -- porting note: was `apply s.induction_on`
  refine s.induction_on ?_ ?_
  · simp
  intro a t h h0
  rw [Multiset.prod_cons, mul_ne_zero_iff] at h0
  simp [h0, cardFactors_mul, h]
#align nat.arithmetic_function.card_factors_multiset_prod Nat.ArithmeticFunction.cardFactors_multiset_prod

@[simp]
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp
#align nat.arithmetic_function.card_factors_apply_prime Nat.ArithmeticFunction.cardFactors_apply_prime

@[simp]
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  rw [cardFactors_apply, hp.factors_pow, List.length_replicate]
#align nat.arithmetic_function.card_factors_apply_prime_pow Nat.ArithmeticFunction.cardFactors_apply_prime_pow

/-- `ω n` is the number of distinct prime factors of `n`. -/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.dedup.length, by simp⟩
#align nat.arithmetic_function.card_distinct_factors Nat.ArithmeticFunction.cardDistinctFactors

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "ω" => Nat.ArithmeticFunction.cardDistinctFactors

theorem cardDistinctFactors_zero : ω 0 = 0 := by simp
#align nat.arithmetic_function.card_distinct_factors_zero Nat.ArithmeticFunction.cardDistinctFactors_zero

@[simp]
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]
#align nat.arithmetic_function.card_distinct_factors_one Nat.ArithmeticFunction.cardDistinctFactors_one

theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.factors.dedup.length :=
  rfl
#align nat.arithmetic_function.card_distinct_factors_apply Nat.ArithmeticFunction.cardDistinctFactors_apply

theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_factors h0, cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.factors.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · rw [h.dedup]
    rfl
#align nat.arithmetic_function.card_distinct_factors_eq_card_factors_iff_squarefree Nat.ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree

@[simp]
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 := by
  rw [cardDistinctFactors_apply, hp.factors_pow, List.replicate_dedup hk, List.length_singleton]
#align nat.arithmetic_function.card_distinct_factors_apply_prime_pow Nat.ArithmeticFunction.cardDistinctFactors_apply_prime_pow

@[simp]
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]
#align nat.arithmetic_function.card_distinct_factors_apply_prime Nat.ArithmeticFunction.cardDistinctFactors_apply_prime

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩
#align nat.arithmetic_function.moebius Nat.ArithmeticFunction.moebius

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "μ" => Nat.ArithmeticFunction.moebius

@[simp]
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h
#align nat.arithmetic_function.moebius_apply_of_squarefree Nat.ArithmeticFunction.moebius_apply_of_squarefree

@[simp]
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h
#align nat.arithmetic_function.moebius_eq_zero_of_not_squarefree Nat.ArithmeticFunction.moebius_eq_zero_of_not_squarefree

theorem moebius_apply_one : μ 1 = 1 := by simp
#align nat.arithmetic_function.moebius_apply_one Nat.ArithmeticFunction.moebius_apply_one

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · simp [h, pow_ne_zero]
#align nat.arithmetic_function.moebius_ne_zero_iff_squarefree Nat.ArithmeticFunction.moebius_ne_zero_iff_squarefree

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  constructor <;> intro h
  · rw [moebius_ne_zero_iff_squarefree] at h
    rw [moebius_apply_of_squarefree h]
    apply neg_one_pow_eq_or
  · rcases h with (h | h) <;> simp [h]
#align nat.arithmetic_function.moebius_ne_zero_iff_eq_or Nat.ArithmeticFunction.moebius_ne_zero_iff_eq_or

theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]
#align nat.arithmetic_function.moebius_apply_prime Nat.ArithmeticFunction.moebius_apply_prime

theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  exact Or.inr h
#align nat.arithmetic_function.moebius_apply_prime_pow Nat.ArithmeticFunction.moebius_apply_prime_pow

theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  rintro rfl
  exact hn' (by simpa)
#align nat.arithmetic_function.moebius_apply_is_prime_pow_not_prime Nat.ArithmeticFunction.moebius_apply_isPrimePow_not_prime

theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine' ⟨by simp, fun {n m} hn hm hnm => _⟩
  simp only [moebius, ZeroHom.coe_mk, coe_mk, ZeroHom.toFun_eq_coe, Eq.ndrec, ZeroHom.coe_mk,
    IsUnit.mul_iff, Nat.isUnit_iff, squarefree_mul hnm, ite_zero_mul_ite_zero,
    cardFactors_mul hn hm, pow_add]
#align nat.arithmetic_function.is_multiplicative_moebius Nat.ArithmeticFunction.isMultiplicative_moebius

open UniqueFactorizationMonoid

@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  refine' recOnPosPrimePosCoprime _ _ _ _ n
  · intro p n hp hn
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp_rw [pow_zero, moebius_apply_one,
      moebius_apply_prime_pow hp (Nat.succ_ne_zero _), Nat.succ_inj', sum_ite_eq', mem_range,
      if_pos hn, add_left_neg]
    rw [one_apply_ne]
    rw [Ne.def, pow_eq_one_iff]
    · exact hp.ne_one
    · exact hn.ne'
  · rw [ZeroHom.map_zero, ZeroHom.map_zero]
  · simp
  · intro a b _ha _hb hab ha' hb'
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.nat_cast
#align nat.arithmetic_function.moebius_mul_coe_zeta Nat.ArithmeticFunction.moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]
#align nat.arithmetic_function.coe_zeta_mul_moebius Nat.ArithmeticFunction.coe_zeta_mul_moebius

@[simp]
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]
#align nat.arithmetic_function.coe_moebius_mul_coe_zeta Nat.ArithmeticFunction.coe_moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]
#align nat.arithmetic_function.coe_zeta_mul_coe_moebius Nat.ArithmeticFunction.coe_zeta_mul_coe_moebius

section CommRing

variable [CommRing R]

instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/-- A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`. -/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩
#align nat.arithmetic_function.zeta_unit Nat.ArithmeticFunction.zetaUnit

@[simp]
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl
#align nat.arithmetic_function.coe_zeta_unit Nat.ArithmeticFunction.coe_zetaUnit

@[simp]
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl
#align nat.arithmetic_function.inv_zeta_unit Nat.ArithmeticFunction.inv_zetaUnit

end CommRing

/-- Möbius inversion for functions to an `AddCommGroup`. -/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i in n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction ℤ) • f' = g'
  · rw [ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', if_false, ZeroHom.coe_mk]
      simp only [coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (ne_of_gt (Nat.pos_of_mem_divisors hx))]
  trans μ • g' = f'
  · constructor <;> intro h
    · rw [← h, ← mul_smul, moebius_mul_coe_zeta, one_smul]
    · rw [← h, ← mul_smul, coe_zeta_mul_moebius, one_smul]
  · rw [ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', smul_apply, if_false,
        ZeroHom.coe_mk]
      -- porting note: added following `simp only`
      simp only [Nat.isUnit_iff, coe_mk, ZeroHom.toFun_eq_coe, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (ne_of_gt (Nat.pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)))]
#align nat.arithmetic_function.sum_eq_iff_sum_smul_moebius_eq Nat.ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq

/-- Möbius inversion for functions to a `Ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [Ring R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i in n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x : ℕ × ℕ in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine' fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => _).congr_left
  rw [zsmul_eq_mul]
#align nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq Nat.ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq

/-- Möbius inversion for functions to a `CommGroup`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∏ i in n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x : ℕ × ℕ in n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _
#align nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq Nat.ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq

/-- Möbius inversion for functions to a `CommGroupWithZero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R}
    (hf : ∀ n : ℕ, 0 < n → f n ≠ 0) (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
    (∀ n > 0, ∏ i in n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x : ℕ × ℕ in n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine'
      Iff.trans
        (Iff.trans (forall_congr' fun n => _)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => _) <;>
    refine' imp_congr_right fun hn => _
  · dsimp
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (Nat.pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]
#align nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq_of_nonzero Nat.ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero

/-- Möbius inversion for functions to an `AddCommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i in n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n:ℕ) => (∑ i in n.divisors, f i)
    intro n hn hnP
    suffices ∑ d in n.divisors, μ (n/d) • G d = f n from by
      rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • g y), ← this, sum_congr rfl]
      intro d hd
      rw [← h d (Nat.pos_of_mem_divisors hd) $ hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    rw [← Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n:ℕ) => ∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d in n.divisors, F d = g n from by
      rw [← this, sum_congr rfl]
      intro d hd
      rw [← h d (Nat.pos_of_mem_divisors hd) $ hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl

theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i in n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine' forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h _ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on [Ring R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i in n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x : ℕ × ℕ in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine' imp_congr_right _
  refine' fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => _).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∏ i in n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x : ℕ × ℕ in n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/-- Möbius inversion for functions to a `CommGroupWithZero`, where the equalities only hold on
a well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) {f g : ℕ → R}
    (hf : ∀ n > 0, f n ≠ 0) (hg : ∀ n > 0, g n ≠ 0):
    (∀ n > 0, n ∈ s → (∏ i in n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x : ℕ × ℕ in n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine'
      Iff.trans
        (Iff.trans (forall_congr' fun n => _)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs) )
        (forall_congr' fun n => _) <;>
    refine' imp_congr_right fun hn => _
  · dsimp
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (Nat.pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end SpecialFunctions

end ArithmeticFunction

end Nat
