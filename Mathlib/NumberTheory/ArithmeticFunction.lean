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
import Mathlib.Algebra.Invertible
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
                                -- 🎉 no goals

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
                                -- 🎉 no goals

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
  -- ⊢ ↑↑↑f x✝ = ↑↑f x✝
  simp
  -- 🎉 no goals
#align nat.arithmetic_function.coe_coe Nat.ArithmeticFunction.coe_coe

@[simp]
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction ℕ) : ArithmeticFunction R) = 1 := by
  ext n
  -- ⊢ ↑↑1 n = ↑1 n
  simp [one_apply]
  -- 🎉 no goals
#align nat.arithmetic_function.nat_coe_one Nat.ArithmeticFunction.natCoe_one

@[simp]
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction ℤ) :
    ArithmeticFunction R) = 1 := by
  ext n
  -- ⊢ ↑↑1 n = ↑1 n
  simp [one_apply]
  -- 🎉 no goals
#align nat.arithmetic_function.int_coe_one Nat.ArithmeticFunction.intCoe_one

section AddMonoid

variable [AddMonoid R]

instance add : Add (ArithmeticFunction R) :=
  ⟨fun f g => ⟨fun n => f n + g n, by simp⟩⟩
                                      -- 🎉 no goals

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
                                                                   -- 🎉 no goals
    natCast_zero := by ext; simp
                       -- ⊢ ↑(NatCast.natCast 0) x✝ = ↑0 x✝
                            -- 🎉 no goals
    natCast_succ := fun n => by ext x; by_cases h : x = 1 <;> simp [h] }
                                -- ⊢ ↑(NatCast.natCast (n + 1)) x = ↑(NatCast.natCast n + 1) x
                                       -- ⊢ ↑(NatCast.natCast (n + 1)) x = ↑(NatCast.natCast n + 1) x
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals
#align nat.arithmetic_function.add_monoid_with_one Nat.ArithmeticFunction.instAddMonoidWithOne

instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _ }

instance [AddGroup R] : AddGroup (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with
    neg := fun f => ⟨fun n => -f n, by simp⟩
                                       -- 🎉 no goals
    add_left_neg := fun _ => ext fun _ => add_left_neg _ }

instance [AddCommGroup R] : AddCommGroup (ArithmeticFunction R) :=
  { show AddGroup (ArithmeticFunction R) by infer_instance with
                                            -- 🎉 no goals
    add_comm := fun _ _ ↦ add_comm _ _ }

section SMul

variable {M : Type*} [Zero R] [AddCommMonoid M] [SMul R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : SMul (ArithmeticFunction R) (ArithmeticFunction M) :=
  ⟨fun f g => ⟨fun n => ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩⟩
                                                                             -- 🎉 no goals

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
                                                                                              -- 🎉 no goals
#align nat.arithmetic_function.mul_apply_one Nat.ArithmeticFunction.mul_apply_one

@[simp, norm_cast]
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  -- ⊢ ↑↑(f * g) n = ↑(↑f * ↑g) n
  simp
  -- 🎉 no goals
#align nat.arithmetic_function.nat_coe_mul Nat.ArithmeticFunction.natCoe_mul

@[simp, norm_cast]
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  -- ⊢ ↑↑(f * g) n = ↑(↑f * ↑g) n
  simp
  -- 🎉 no goals
#align nat.arithmetic_function.int_coe_mul Nat.ArithmeticFunction.intCoe_mul

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  -- ⊢ ↑((f * g) • h) n = ↑(f • g • h) n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, Finset.sum_sigma']
  -- ⊢ ∑ x in Finset.sigma (divisorsAntidiagonal n) fun a => divisorsAntidiagonal a …
  apply Finset.sum_bij
  pick_goal 5
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _H
    -- ⊢ (_ : ℕ × ℕ) × ℕ × ℕ
    exact ⟨(k, l * j), (l, j)⟩
    -- 🎉 no goals
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H
    -- ⊢ Sigma.casesOn (motive := fun x => (x ∈ Finset.sigma (divisorsAntidiagonal n) …
    simp only [Finset.mem_sigma, mem_divisorsAntidiagonal] at H ⊢
    -- ⊢ (k * (l * j) = n ∧ n ≠ 0) ∧ True ∧ l * j ≠ 0
    rcases H with ⟨⟨rfl, n0⟩, rfl, i0⟩
    -- ⊢ (k * (l * j) = k * l * j ∧ k * l * j ≠ 0) ∧ True ∧ l * j ≠ 0
    refine' ⟨⟨(mul_assoc _ _ _).symm, n0⟩, trivial, _⟩
    -- ⊢ l * j ≠ 0
    rw [mul_ne_zero_iff] at *
    -- ⊢ l ≠ 0 ∧ j ≠ 0
    exact ⟨i0.2, n0.2⟩
    -- 🎉 no goals
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _H
    -- ⊢ ↑f { fst := (i, j), snd := (k, l) }.snd.fst • ↑g { fst := (i, j), snd := (k, …
    simp only [mul_assoc]
    -- 🎉 no goals
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩ H₁ H₂
    -- ⊢ Sigma.casesOn (motive := fun x => (x ∈ Finset.sigma (divisorsAntidiagonal n) …
    simp only [Finset.mem_sigma, mem_divisorsAntidiagonal, and_imp, Prod.mk.inj_iff, add_comm,
      heq_iff_eq] at H₁ H₂ ⊢
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq, and_imp] -- porting note: added
    -- ⊢ c = k → d * b = l * j → d = l → b = j → (a = i ∧ b = j) ∧ c = k ∧ d = l
    rintro h h2 rfl rfl
    -- ⊢ (a = i ∧ b = b) ∧ c = k ∧ d = d
    subst h -- porting note: added.  The `rintro h ...` above was `rintro rfl ...`
    -- ⊢ (a = i ∧ b = b) ∧ c = c ∧ d = d
    exact ⟨⟨Eq.trans H₁.2.1.symm H₂.2.1, rfl⟩, rfl, rfl⟩
    -- 🎉 no goals
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H
    -- ⊢ ∃ a ha, { fst := (i, j), snd := (k, l) } = Sigma.casesOn (motive := fun x => …
    refine' ⟨⟨(i * k, l), (i, k)⟩, _, _⟩
    -- ⊢ { fst := (i * k, l), snd := (i, k) } ∈ Finset.sigma (divisorsAntidiagonal n) …
    · simp only [Finset.mem_sigma, mem_divisorsAntidiagonal] at H ⊢
      -- ⊢ (i * k * l = n ∧ n ≠ 0) ∧ True ∧ i * k ≠ 0
      rcases H with ⟨⟨rfl, n0⟩, rfl, j0⟩
      -- ⊢ (i * k * l = i * (k * l) ∧ i * (k * l) ≠ 0) ∧ True ∧ i * k ≠ 0
      refine' ⟨⟨mul_assoc _ _ _, n0⟩, trivial, _⟩
      -- ⊢ i * k ≠ 0
      rw [mul_ne_zero_iff] at *
      -- ⊢ i ≠ 0 ∧ k ≠ 0
      exact ⟨n0.1, j0.1⟩
      -- 🎉 no goals
    · simp only [true_and_iff, mem_divisorsAntidiagonal, and_true_iff, Prod.mk.inj_iff,
        eq_self_iff_true, Ne.def, mem_sigma, heq_iff_eq] at H ⊢
      rw [H.2.1]
      -- 🎉 no goals
#align nat.arithmetic_function.mul_smul' Nat.ArithmeticFunction.mul_smul'

theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
  ext x
  -- ⊢ ↑(1 • b) x = ↑b x
  rw [smul_apply]
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑1 x.fst • ↑b x.snd = ↑b x
  by_cases x0 : x = 0
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑1 x.fst • ↑b x.snd = ↑b x
  · simp [x0]
    -- 🎉 no goals
  have h : {(1, x)} ⊆ divisorsAntidiagonal x := by simp [x0]
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑1 x.fst • ↑b x.snd = ↑b x
  rw [← sum_subset h]
  -- ⊢ ∑ x in {(1, x)}, ↑1 x.fst • ↑b x.snd = ↑b x
  · simp
    -- 🎉 no goals
  intro y ymem ynmem
  -- ⊢ ↑1 y.fst • ↑b y.snd = 0
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
  -- 🎉 no goals
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
      -- ⊢ ↑(f * 1) x = ↑f x
      rw [mul_apply]
      -- ⊢ ∑ x in divisorsAntidiagonal x, ↑f x.fst * ↑1 x.snd = ↑f x
      by_cases x0 : x = 0
      -- ⊢ ∑ x in divisorsAntidiagonal x, ↑f x.fst * ↑1 x.snd = ↑f x
      · simp [x0]
        -- 🎉 no goals
      have h : {(x, 1)} ⊆ divisorsAntidiagonal x := by simp [x0]
      -- ⊢ ∑ x in divisorsAntidiagonal x, ↑f x.fst * ↑1 x.snd = ↑f x
      rw [← sum_subset h]
      -- ⊢ ∑ x in {(x, 1)}, ↑f x.fst * ↑1 x.snd = ↑f x
      · simp
        -- 🎉 no goals
      intro y ymem ynmem
      -- ⊢ ↑f y.fst * ↑1 y.snd = 0
      have y2ne : y.snd ≠ 1 := by
        intro con
        cases y; subst con -- porting note: added
        simp only [Con, mem_divisorsAntidiagonal, mul_one, Ne.def] at ymem
        simp only [mem_singleton, Prod.ext_iff] at ynmem
        tauto
      simp [y2ne]
      -- 🎉 no goals
    mul_assoc := mul_smul' }
#align nat.arithmetic_function.monoid Nat.ArithmeticFunction.instMonoid

instance instSemiring : Semiring (ArithmeticFunction R) :=
  -- porting note: I reorganized this instance
  { ArithmeticFunction.instAddMonoidWithOne,
    ArithmeticFunction.instMonoid,
    ArithmeticFunction.instAddCommMonoid with
    zero_mul := fun f => by
      ext
      -- ⊢ ↑(0 * f) x✝ = ↑0 x✝
      simp only [mul_apply, zero_mul, sum_const_zero, zero_apply]
      -- 🎉 no goals
    mul_zero := fun f => by
      ext
      -- ⊢ ↑(f * 0) x✝ = ↑0 x✝
      -- ⊢ ↑(a * (b + c)) x✝ = ↑(a * b + a * c) x✝
      simp only [mul_apply, sum_const_zero, mul_zero, zero_apply]
      -- 🎉 no goals
      -- 🎉 no goals
    left_distrib := fun a b c => by
      -- ⊢ ↑((a + b) * c) x✝ = ↑(a * c + b * c) x✝
      ext
      -- 🎉 no goals
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
      -- ⊢ ↑(f * g) x✝ = ↑(g * f) x✝
      rw [mul_apply, ← map_swap_divisorsAntidiagonal, sum_map]
      -- ⊢ ∑ x in divisorsAntidiagonal x✝, ↑f (↑(Equiv.toEmbedding (Equiv.prodComm ℕ ℕ) …
      simp [mul_comm] }
      -- 🎉 no goals

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
    -- ⊢ ↑(r • (x + y)) x✝ = ↑(r • x + r • y) x✝
    simp only [sum_add_distrib, smul_add, smul_apply, add_apply]
    -- 🎉 no goals
    -- ⊢ ↑(r • 0) x✝ = ↑0 x✝
  smul_zero r := by
    -- 🎉 no goals
    ext
    simp only [smul_apply, sum_const_zero, smul_zero, zero_apply]
  add_smul r s x := by
    ext
    -- ⊢ ↑((r + s) • x) x✝ = ↑(r • x + s • x) x✝
    simp only [add_smul, sum_add_distrib, smul_apply, add_apply]
    -- 🎉 no goals
  zero_smul r := by
    ext
    -- ⊢ ↑(0 • r) x✝ = ↑0 x✝
    simp only [smul_apply, sum_const_zero, zero_smul, zero_apply]
    -- 🎉 no goals

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
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑↑ζ x.fst • ↑f x.snd = ∑ i in divisors x, ↑f i
  trans ∑ i in divisorsAntidiagonal x, f i.snd
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑↑ζ x.fst • ↑f x.snd = ∑ i in divisorsAntidia …
  · refine' sum_congr rfl fun i hi => _
    -- ⊢ ↑↑ζ i.fst • ↑f i.snd = ↑f i.snd
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    -- ⊢ ↑↑ζ i.fst • ↑f i.snd = ↑f i.snd
    rw [natCoe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
    -- 🎉 no goals
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]
    -- 🎉 no goals
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
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑f x.fst * ↑↑ζ x.snd = ∑ i in divisors x, ↑f i
  trans ∑ i in divisorsAntidiagonal x, f i.1
  -- ⊢ ∑ x in divisorsAntidiagonal x, ↑f x.fst * ↑↑ζ x.snd = ∑ i in divisorsAntidia …
  · refine' sum_congr rfl fun i hi => _
    -- ⊢ ↑f i.fst * ↑↑ζ i.snd = ↑f i.fst
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    -- ⊢ ↑f i.fst * ↑↑ζ i.snd = ↑f i.fst
    rw [natCoe_apply, zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one]
    -- 🎉 no goals
  · rw [← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
    -- 🎉 no goals
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
                          -- 🎉 no goals
#align nat.arithmetic_function.pmul Nat.ArithmeticFunction.pmul

@[simp]
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : ℕ} : f.pmul g x = f x * g x :=
  rfl
#align nat.arithmetic_function.pmul_apply Nat.ArithmeticFunction.pmul_apply

theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  -- ⊢ ↑(pmul f g) x✝ = ↑(pmul g f) x✝
  simp [mul_comm]
  -- 🎉 no goals
#align nat.arithmetic_function.pmul_comm Nat.ArithmeticFunction.pmul_comm

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  -- ⊢ ↑(pmul f ↑ζ) x = ↑f x
  cases x <;> simp [Nat.succ_ne_zero]
  -- ⊢ ↑(pmul f ↑ζ) Nat.zero = ↑f Nat.zero
              -- 🎉 no goals
              -- 🎉 no goals
#align nat.arithmetic_function.pmul_zeta Nat.ArithmeticFunction.pmul_zeta

@[simp]
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  -- ⊢ ↑(pmul (↑ζ) f) x = ↑f x
  cases x <;> simp [Nat.succ_ne_zero]
  -- ⊢ ↑(pmul (↑ζ) f) Nat.zero = ↑f Nat.zero
              -- 🎉 no goals
              -- 🎉 no goals
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
      -- ⊢ ↑f 0 ^ k = 0
      rw [map_zero]
      -- ⊢ 0 ^ k = 0
      exact zero_pow (Nat.pos_of_ne_zero h0)⟩
      -- 🎉 no goals
#align nat.arithmetic_function.ppow Nat.ArithmeticFunction.ppow

@[simp]
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]
                                                                  -- 🎉 no goals
#align nat.arithmetic_function.ppow_zero Nat.ArithmeticFunction.ppow_zero

@[simp]
theorem ppow_apply {f : ArithmeticFunction R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow, dif_neg (ne_of_gt kpos)]
  -- ⊢ ↑{ toFun := fun x => ↑f x ^ k, map_zero' := (_ : (fun x => ↑f x ^ k) 0 = 0)  …
  rfl
  -- 🎉 no goals
#align nat.arithmetic_function.ppow_apply Nat.ArithmeticFunction.ppow_apply

theorem ppow_succ {f : ArithmeticFunction R} {k : ℕ} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  -- ⊢ ↑(ppow f (k + 1)) x = ↑(pmul f (ppow f k)) x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ]
  -- ⊢ ↑f x * ↑f x ^ k = ↑(pmul f (ppow f k)) x
  induction k <;> simp
  -- ⊢ ↑f x * ↑f x ^ Nat.zero = ↑(pmul f (ppow f Nat.zero)) x
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat.arithmetic_function.ppow_succ Nat.ArithmeticFunction.ppow_succ

theorem ppow_succ' {f : ArithmeticFunction R} {k : ℕ} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  -- ⊢ ↑(ppow f (k + 1)) x = ↑(pmul (ppow f k) f) x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ']
  -- ⊢ ↑f x ^ k * ↑f x = ↑(pmul (ppow f k) f) x
  induction k <;> simp
  -- ⊢ ↑f x ^ Nat.zero * ↑f x = ↑(pmul (ppow f Nat.zero) f) x
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat.arithmetic_function.ppow_succ' Nat.ArithmeticFunction.ppow_succ'

end Pmul

section Pdiv

/-- This is the pointwise division of `ArithmeticFunction`s. -/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, ne_eq, not_true, div_zero]⟩
                          -- 🎉 no goals

@[simp]
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coersion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  -- ⊢ ↑(pdiv f ↑ζ) n = ↑f n
  cases n <;> simp [succ_ne_zero]
  -- ⊢ ↑(pdiv f ↑ζ) Nat.zero = ↑f Nat.zero
              -- 🎉 no goals
              -- 🎉 no goals

end Pdiv

/-- Multiplicative functions -/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.coprime n → f (m * n) = f m * f n
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
    (h : m.coprime n) : f (m * n) = f m * f n :=
  hf.2 h
#align nat.arithmetic_function.is_multiplicative.map_mul_of_coprime Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime

end MonoidWithZero

theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι → ℕ) {f : Nat.ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (coprime on g)) :
    f (∏ i in s, g i) = ∏ i in s, f (g i) := by
  classical
    induction' s using Finset.induction_on with a s has ih hs
    · simp [hf]
    rw [coe_insert, Set.pairwise_insert_of_symmetric (coprime.symmetric.comap g)] at hs
    rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.coprime_prod_right fun i hi => hs.2 _ hi (hi.ne_of_not_mem has).symm
#align nat.arithmetic_function.is_multiplicative.map_prod Nat.ArithmeticFunction.IsMultiplicative.map_prod

theorem nat_cast {f : ArithmeticFunction ℕ} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
      -- 🎉 no goals
                                    -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.nat_cast Nat.ArithmeticFunction.IsMultiplicative.nat_cast

theorem int_cast {f : ArithmeticFunction ℤ} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
      -- 🎉 no goals
                                    -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.int_cast Nat.ArithmeticFunction.IsMultiplicative.int_cast

theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f * g) :=
  ⟨by
    -- porting note was `simp [hf, hg]`.
    simp [hf.1, hg.1],
    -- 🎉 no goals
  by
    simp only [mul_apply]
    -- ⊢ ∀ {m n : ℕ}, coprime m n → ∑ x in divisorsAntidiagonal (m * n), ↑f x.fst * ↑ …
    intro m n cop
    -- ⊢ ∑ x in divisorsAntidiagonal (m * n), ↑f x.fst * ↑g x.snd = (∑ x in divisorsA …
    rw [sum_mul_sum]
    -- ⊢ ∑ x in divisorsAntidiagonal (m * n), ↑f x.fst * ↑g x.snd = ∑ p in divisorsAn …
    symm
    -- ⊢ ∑ p in divisorsAntidiagonal m ×ˢ divisorsAntidiagonal n, ↑f p.fst.fst * ↑g p …
    apply sum_bij fun (x : (ℕ × ℕ) × ℕ × ℕ) _h => (x.1.1 * x.2.1, x.1.2 * x.2.2)
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
      -- ⊢ (((a1, a2), b1, b2).fst.fst * ((a1, a2), b1, b2).snd.fst, ((a1, a2), b1, b2) …
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      -- ⊢ (((a1, a2), b1, b2).fst.fst * ((a1, a2), b1, b2).snd.fst, ((a1, a2), b1, b2) …
      rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      -- ⊢ (((a1, a2), b1, b2).fst.fst * ((a1, a2), b1, b2).snd.fst, ((a1, a2), b1, b2) …
      simp only [mem_divisorsAntidiagonal, Nat.mul_eq_zero, Ne.def]
      -- ⊢ a1 * b1 * (a2 * b2) = a1 * a2 * (b1 * b2) ∧ ¬((a1 = 0 ∨ a2 = 0) ∨ b1 = 0 ∨ b …
      constructor
      -- ⊢ a1 * b1 * (a2 * b2) = a1 * a2 * (b1 * b2)
      · ring
        -- 🎉 no goals
      rw [Nat.mul_eq_zero] at *
      -- ⊢ ¬((a1 = 0 ∨ a2 = 0) ∨ b1 = 0 ∨ b2 = 0)
      apply not_or_of_not ha hb
      -- 🎉 no goals
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
      -- ⊢ ↑f ((a1, a2), b1, b2).fst.fst * ↑g ((a1, a2), b1, b2).fst.snd * (↑f ((a1, a2 …
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      -- ⊢ ↑f ((a1, a2), b1, b2).fst.fst * ↑g ((a1, a2), b1, b2).fst.snd * (↑f ((a1, a2 …
      rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      -- ⊢ ↑f ((a1, a2), b1, b2).fst.fst * ↑g ((a1, a2), b1, b2).fst.snd * (↑f ((a1, a2 …
      dsimp only
      -- ⊢ ↑f a1 * ↑g a2 * (↑f b1 * ↑g b2) = ↑f (a1 * b1) * ↑g (a2 * b2)
      rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
        hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
      ring
      -- 🎉 no goals
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h
      -- ⊢ ((a1, a2), b1, b2) = ((c1, c2), d1, d2)
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at hab
      -- ⊢ ((a1, a2), b1, b2) = ((c1, c2), d1, d2)
      rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
      -- ⊢ ((a1, a2), b1, b2) = ((c1, c2), d1, d2)
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at hcd
      -- ⊢ ((a1, a2), b1, b2) = ((c1, c2), d1, d2)
      simp only [Prod.mk.inj_iff] at h
      -- ⊢ ((a1, a2), b1, b2) = ((c1, c2), d1, d2)
      ext <;> dsimp only
              -- ⊢ a1 = c1
              -- ⊢ a2 = c2
              -- ⊢ b1 = d1
              -- ⊢ b2 = d2
      · trans Nat.gcd (a1 * a2) (a1 * b1)
        -- ⊢ a1 = gcd (a1 * a2) (a1 * b1)
        · rw [Nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
          -- 🎉 no goals
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          -- ⊢ gcd (a1 * a2) (a1 * b1) = c1
          rw [← hcd.1.1, h.1, Nat.gcd_mul_left,
            cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · trans Nat.gcd (a1 * a2) (a2 * b2)
        -- ⊢ a2 = gcd (a1 * a2) (a2 * b2)
        · rw [mul_comm, Nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
            mul_one]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          -- ⊢ gcd (a1 * a2) (a2 * b2) = c2
          rw [← hcd.1.1, h.2, mul_comm, Nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]
      · trans Nat.gcd (b1 * b2) (a1 * b1)
        -- ⊢ b1 = gcd (b1 * b2) (a1 * b1)
        · rw [mul_comm, Nat.gcd_mul_right,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mul]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          -- ⊢ gcd (b1 * b2) (a1 * b1) = d1
          rw [← hcd.2.1, h.1, mul_comm c1 d1, Nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one]
      · trans Nat.gcd (b1 * b2) (a2 * b2)
        -- ⊢ b2 = gcd (b1 * b2) (a2 * b2)
        · rw [Nat.gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,
            one_mul]
        · rw [← hcd.1.1, ← hcd.2.1] at cop
          -- ⊢ gcd (b1 * b2) (a2 * b2) = d2
          rw [← hcd.2.1, h.2, Nat.gcd_mul_right,
            cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
    · rintro ⟨b1, b2⟩ h
      -- ⊢ ∃ a ha, (b1, b2) = (a.fst.fst * a.snd.fst, a.fst.snd * a.snd.snd)
      simp only [mem_divisorsAntidiagonal, Ne.def, mem_product] at h
      -- ⊢ ∃ a ha, (b1, b2) = (a.fst.fst * a.snd.fst, a.fst.snd * a.snd.snd)
      use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
      -- ⊢ ∃ ha, (b1, b2) = (((gcd b1 m, gcd b2 m), gcd b1 n, gcd b2 n).fst.fst * ((gcd …
      simp only [exists_prop, Prod.mk.inj_iff, Ne.def, mem_product, mem_divisorsAntidiagonal]
      -- ⊢ ((gcd b1 m * gcd b2 m = m ∧ ¬m = 0) ∧ gcd b1 n * gcd b2 n = n ∧ ¬n = 0) ∧ b1 …
      rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
        Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
      · rw [Nat.mul_eq_zero, not_or] at h
        -- ⊢ ((m = m ∧ ¬m = 0) ∧ n = n ∧ ¬n = 0) ∧ b1 = gcd b1 (b1 * b2) ∧ b2 = gcd b2 (b …
        simp [h.2.1, h.2.2]
        -- 🎉 no goals
      rw [mul_comm n m, h.1]⟩
      -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.mul Nat.ArithmeticFunction.IsMultiplicative.mul

theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun {m n} cop => by
      -- 🎉 no goals
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    -- ⊢ ↑f m * ↑f n * (↑g m * ↑g n) = ↑f m * ↑g m * (↑f n * ↑g n)
    ring⟩
    -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.pmul Nat.ArithmeticFunction.IsMultiplicative.pmul

theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
  (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨ by simp [hf, hg], fun {m n} cop => by
       -- 🎉 no goals
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop,
      div_eq_mul_inv, mul_inv]
    apply mul_mul_mul_comm ⟩
    -- 🎉 no goals

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
      f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.coprime n → f (m * n) = f m * f n := by
  refine' and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => _⟩)
  -- ⊢ ↑f (m * n) = ↑f m * ↑f n
  rcases eq_or_ne m 0 with (rfl | hm)
  -- ⊢ ↑f (0 * n) = ↑f 0 * ↑f n
  · simp
    -- 🎉 no goals
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ ↑f (m * 0) = ↑f m * ↑f 0
  · simp
    -- 🎉 no goals
  exact h hm hn hmn
  -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.iff_ne_zero Nat.ArithmeticFunction.IsMultiplicative.iff_ne_zero

/-- Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers -/
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : ℕ, Nat.Prime p → f (p ^ i) = g (p ^ i) := by
  constructor
  -- ⊢ f = g → ∀ (p i : ℕ), Prime p → ↑f (p ^ i) = ↑g (p ^ i)
  · intro h p i _
    -- ⊢ ↑f (p ^ i) = ↑g (p ^ i)
    rw [h]
    -- 🎉 no goals
  intro h
  -- ⊢ f = g
  ext n
  -- ⊢ ↑f n = ↑g n
  by_cases hn : n = 0
  -- ⊢ ↑f n = ↑g n
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
    -- 🎉 no goals
  rw [multiplicative_factorization f hf hn, multiplicative_factorization g hg hn]
  -- ⊢ (Finsupp.prod (factorization n) fun p k => ↑f (p ^ k)) = Finsupp.prod (facto …
  refine' Finset.prod_congr rfl _
  -- ⊢ ∀ (x : ℕ), x ∈ (factorization n).support → (fun p k => ↑f (p ^ k)) x (↑(fact …
  simp only [support_factorization, List.mem_toFinset]
  -- ⊢ ∀ (x : ℕ), x ∈ factors n → ↑f (x ^ ↑(factorization n) x) = ↑g (x ^ ↑(factori …
  intro p hp
  -- ⊢ ↑f (p ^ ↑(factorization n) p) = ↑g (p ^ ↑(factorization n) p)
  exact h p _ (Nat.prime_of_mem_factors hp)
  -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.eq_iff_eq_on_prime_powers Nat.ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers

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
  -- ⊢ ↑(pow Nat.zero) n = if Nat.zero = 0 ∧ n = 0 then 0 else n ^ Nat.zero
  · simp [pow]
    -- 🎉 no goals
  rename_i k  -- porting note: added
  -- ⊢ ↑(pow (succ k)) n = if succ k = 0 ∧ n = 0 then 0 else n ^ succ k
  simp [pow, (ne_of_lt (Nat.succ_pos k)).symm]
  -- 🎉 no goals
#align nat.arithmetic_function.pow_apply Nat.ArithmeticFunction.pow_apply

theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  -- ⊢ ↑(pow 0) n = ↑ζ n
  simp
  -- 🎉 no goals
#align nat.arithmetic_function.pow_zero_eq_zeta Nat.ArithmeticFunction.pow_zero_eq_zeta

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d in divisors n, d ^ k, by simp⟩
                                         -- 🎉 no goals
#align nat.arithmetic_function.sigma Nat.ArithmeticFunction.sigma

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "σ" => Nat.ArithmeticFunction.sigma

theorem sigma_apply {k n : ℕ} : σ k n = ∑ d in divisors n, d ^ k :=
  rfl
#align nat.arithmetic_function.sigma_apply Nat.ArithmeticFunction.sigma_apply

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d in divisors n, d := by simp [sigma_apply]
                                                                     -- 🎉 no goals
#align nat.arithmetic_function.sigma_one_apply Nat.ArithmeticFunction.sigma_one_apply

theorem sigma_zero_apply (n : ℕ) : σ 0 n = (divisors n).card := by simp [sigma_apply]
                                                                   -- 🎉 no goals
#align nat.arithmetic_function.sigma_zero_apply Nat.ArithmeticFunction.sigma_zero_apply

theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  rw [sigma_zero_apply, divisors_prime_pow hp, card_map, card_range]
  -- 🎉 no goals
#align nat.arithmetic_function.sigma_zero_apply_prime_pow Nat.ArithmeticFunction.sigma_zero_apply_prime_pow

theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  -- ⊢ ↑(ζ * pow k) x✝ = ↑(σ k) x✝
  rw [sigma, zeta_mul_apply]
  -- ⊢ ∑ i in divisors x✝, ↑(pow k) i = ↑{ toFun := fun n => ∑ d in divisors n, d ^ …
  apply sum_congr rfl
  -- ⊢ ∀ (x : ℕ), x ∈ divisors x✝ → ↑(pow k) x = x ^ k
  intro x hx
  -- ⊢ ↑(pow k) x = x ^ k
  rw [pow_apply, if_neg (not_and_of_not_right _ _)]
  -- ⊢ ¬x = 0
  contrapose! hx
  -- ⊢ ¬x ∈ divisors x✝
  simp [hx]
  -- 🎉 no goals
#align nat.arithmetic_function.zeta_mul_pow_eq_sigma Nat.ArithmeticFunction.zeta_mul_pow_eq_sigma

theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2
    ⟨by simp, by
        -- 🎉 no goals
      intro m n hm _hn hmn
      -- ⊢ ↑1 (m * n) = ↑1 m * ↑1 n
      rcases eq_or_ne m 1 with (rfl | hm')
      -- ⊢ ↑1 (1 * n) = ↑1 1 * ↑1 n
      · simp
        -- 🎉 no goals
      rw [one_apply_ne, one_apply_ne hm', zero_mul]
      -- ⊢ m * n ≠ 1
      rw [Ne.def, mul_eq_one, not_and_or]
      -- ⊢ ¬m = 1 ∨ ¬n = 1
      exact Or.inl hm'⟩
      -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative_one Nat.ArithmeticFunction.isMultiplicative_one

theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp (config := { contextual := true })⟩
                                     -- 🎉 no goals
                                              -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative_zeta Nat.ArithmeticFunction.isMultiplicative_zeta

theorem isMultiplicative_id : IsMultiplicative ArithmeticFunction.id :=
  ⟨rfl, fun {_ _} _ => rfl⟩
#align nat.arithmetic_function.is_multiplicative_id Nat.ArithmeticFunction.isMultiplicative_id

theorem IsMultiplicative.ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction' k with k hi
  -- ⊢ IsMultiplicative (ArithmeticFunction.ppow f Nat.zero)
  · exact isMultiplicative_zeta.nat_cast
    -- 🎉 no goals
  · rw [ppow_succ]
    -- ⊢ IsMultiplicative (ArithmeticFunction.pmul f (ArithmeticFunction.ppow f k))
    apply hf.pmul hi
    -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative.ppow Nat.ArithmeticFunction.IsMultiplicative.ppow

theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
#align nat.arithmetic_function.is_multiplicative_pow Nat.ArithmeticFunction.isMultiplicative_pow

theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  -- ⊢ IsMultiplicative (ζ * pow k)
  apply isMultiplicative_zeta.mul isMultiplicative_pow
  -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative_sigma Nat.ArithmeticFunction.isMultiplicative_sigma

/-- `Ω n` is the number of prime factors of `n`. -/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.length, by simp⟩
                                 -- 🎉 no goals
#align nat.arithmetic_function.card_factors Nat.ArithmeticFunction.cardFactors

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "Ω" => Nat.ArithmeticFunction.cardFactors

theorem cardFactors_apply {n : ℕ} : Ω n = n.factors.length :=
  rfl
#align nat.arithmetic_function.card_factors_apply Nat.ArithmeticFunction.cardFactors_apply

@[simp]
theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors]
                                        -- 🎉 no goals
#align nat.arithmetic_function.card_factors_one Nat.ArithmeticFunction.cardFactors_one

theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine' ⟨fun h => _, fun h => List.length_eq_one.2 ⟨n, factors_prime h⟩⟩
  -- ⊢ Prime n
  cases' n with n
  -- ⊢ Prime Nat.zero
  · contrapose! h
    -- ⊢ ↑Ω Nat.zero ≠ 1
    simp
    -- 🎉 no goals
  rcases List.length_eq_one.1 h with ⟨x, hx⟩
  -- ⊢ Prime (succ n)
  rw [← prod_factors n.succ_ne_zero, hx, List.prod_singleton]
  -- ⊢ Prime x
  apply prime_of_mem_factors
  -- ⊢ x ∈ factors ?succ.intro.n
  rw [hx, List.mem_singleton]
  -- 🎉 no goals
#align nat.arithmetic_function.card_factors_eq_one_iff_prime Nat.ArithmeticFunction.cardFactors_eq_one_iff_prime

theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]
#align nat.arithmetic_function.card_factors_mul Nat.ArithmeticFunction.cardFactors_mul

theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  revert h0
  -- ⊢ Multiset.prod s ≠ 0 → ↑Ω (Multiset.prod s) = Multiset.sum (Multiset.map (↑Ω) …
  -- porting note: was `apply s.induction_on`
  refine s.induction_on ?_ ?_
  -- ⊢ Multiset.prod 0 ≠ 0 → ↑Ω (Multiset.prod 0) = Multiset.sum (Multiset.map (↑Ω) …
  · simp
    -- 🎉 no goals
  intro a t h h0
  -- ⊢ ↑Ω (Multiset.prod (a ::ₘ t)) = Multiset.sum (Multiset.map (↑Ω) (a ::ₘ t))
  rw [Multiset.prod_cons, mul_ne_zero_iff] at h0
  -- ⊢ ↑Ω (Multiset.prod (a ::ₘ t)) = Multiset.sum (Multiset.map (↑Ω) (a ::ₘ t))
  simp [h0, cardFactors_mul, h]
  -- 🎉 no goals
#align nat.arithmetic_function.card_factors_multiset_prod Nat.ArithmeticFunction.cardFactors_multiset_prod

@[simp]
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp
#align nat.arithmetic_function.card_factors_apply_prime Nat.ArithmeticFunction.cardFactors_apply_prime

@[simp]
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  rw [cardFactors_apply, hp.factors_pow, List.length_replicate]
  -- 🎉 no goals
#align nat.arithmetic_function.card_factors_apply_prime_pow Nat.ArithmeticFunction.cardFactors_apply_prime_pow

/-- `ω n` is the number of distinct prime factors of `n`. -/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.dedup.length, by simp⟩
                                       -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors Nat.ArithmeticFunction.cardDistinctFactors

-- porting note: added `Nat.` to the scoped namespace
@[inherit_doc]
scoped[Nat.ArithmeticFunction] notation "ω" => Nat.ArithmeticFunction.cardDistinctFactors

theorem cardDistinctFactors_zero : ω 0 = 0 := by simp
                                                 -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors_zero Nat.ArithmeticFunction.cardDistinctFactors_zero

@[simp]
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]
                                                -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors_one Nat.ArithmeticFunction.cardDistinctFactors_one

theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.factors.dedup.length :=
  rfl
#align nat.arithmetic_function.card_distinct_factors_apply Nat.ArithmeticFunction.cardDistinctFactors_apply

theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_factors h0, cardDistinctFactors_apply]
  -- ⊢ List.length (List.dedup (factors n)) = ↑Ω n ↔ List.Nodup (factors n)
  constructor <;> intro h
  -- ⊢ List.length (List.dedup (factors n)) = ↑Ω n → List.Nodup (factors n)
                  -- ⊢ List.Nodup (factors n)
                  -- ⊢ List.length (List.dedup (factors n)) = ↑Ω n
  · rw [← n.factors.dedup_sublist.eq_of_length h]
    -- ⊢ List.Nodup (List.dedup (factors n))
    apply List.nodup_dedup
    -- 🎉 no goals
  · rw [h.dedup]
    -- ⊢ List.length (factors n) = ↑Ω n
    rfl
    -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors_eq_card_factors_iff_squarefree Nat.ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree

@[simp]
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 := by
  rw [cardDistinctFactors_apply, hp.factors_pow, List.replicate_dedup hk, List.length_singleton]
  -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors_apply_prime_pow Nat.ArithmeticFunction.cardDistinctFactors_apply_prime_pow

@[simp]
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]
  -- 🎉 no goals
#align nat.arithmetic_function.card_distinct_factors_apply_prime Nat.ArithmeticFunction.cardDistinctFactors_apply_prime

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩
                                                                 -- 🎉 no goals
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
                                          -- 🎉 no goals
#align nat.arithmetic_function.moebius_apply_one Nat.ArithmeticFunction.moebius_apply_one

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  -- ⊢ ↑μ n ≠ 0 → Squarefree n
                  -- ⊢ Squarefree n
                  -- ⊢ ↑μ n ≠ 0
  · contrapose! h
    -- ⊢ ↑μ n = 0
    simp [h]
    -- 🎉 no goals
  · simp [h, pow_ne_zero]
    -- 🎉 no goals
#align nat.arithmetic_function.moebius_ne_zero_iff_squarefree Nat.ArithmeticFunction.moebius_ne_zero_iff_squarefree

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  constructor <;> intro h
  -- ⊢ ↑μ n ≠ 0 → ↑μ n = 1 ∨ ↑μ n = -1
                  -- ⊢ ↑μ n = 1 ∨ ↑μ n = -1
                  -- ⊢ ↑μ n ≠ 0
  · rw [moebius_ne_zero_iff_squarefree] at h
    -- ⊢ ↑μ n = 1 ∨ ↑μ n = -1
    rw [moebius_apply_of_squarefree h]
    -- ⊢ (-1) ^ ↑Ω n = 1 ∨ (-1) ^ ↑Ω n = -1
    apply neg_one_pow_eq_or
    -- 🎉 no goals
  · rcases h with (h | h) <;> simp [h]
    -- ⊢ ↑μ n ≠ 0
                              -- 🎉 no goals
                              -- 🎉 no goals
#align nat.arithmetic_function.moebius_ne_zero_iff_eq_or Nat.ArithmeticFunction.moebius_ne_zero_iff_eq_or

theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]
  -- 🎉 no goals
#align nat.arithmetic_function.moebius_apply_prime Nat.ArithmeticFunction.moebius_apply_prime

theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  -- ⊢ ↑μ (p ^ k) = -1
  · rw [h, pow_one, moebius_apply_prime hp]
    -- 🎉 no goals
  rw [moebius_eq_zero_of_not_squarefree]
  -- ⊢ ¬Squarefree (p ^ k)
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  -- ⊢ ¬Squarefree p ∨ ¬k = 1
  exact Or.inr h
  -- 🎉 no goals
#align nat.arithmetic_function.moebius_apply_prime_pow Nat.ArithmeticFunction.moebius_apply_prime_pow

theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  -- ⊢ ↑μ (p ^ k) = 0
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  -- ⊢ ¬k = 1
  rintro rfl
  -- ⊢ False
  exact hn' (by simpa)
  -- 🎉 no goals
#align nat.arithmetic_function.moebius_apply_is_prime_pow_not_prime Nat.ArithmeticFunction.moebius_apply_isPrimePow_not_prime

theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  -- ⊢ ↑μ 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → coprime m n → ↑μ (m * n) = ↑μ m * ↑μ n
  refine' ⟨by simp, fun {n m} hn hm hnm => _⟩
  -- ⊢ ↑μ (n * m) = ↑μ n * ↑μ m
  -- porting note: the rest of this proof was a single `simp only` with all the lemmas thrown in
  -- followed by the last `rw`.
  simp only [moebius, ZeroHom.coe_mk]
  -- ⊢ ↑{ toFun := fun n => if Squarefree n then (-1) ^ ↑Ω n else 0, map_zero' := ( …
  dsimp only [coe_mk, ZeroHom.toFun_eq_coe, Eq.ndrec, ZeroHom.coe_mk]
  -- ⊢ (if Squarefree (n * m) then (-1) ^ ↑Ω (n * m) else 0) = (if Squarefree n the …
  simp only [IsUnit.mul_iff, Nat.isUnit_iff, squarefree_mul hnm, ite_and, mul_ite, ite_mul,
    zero_mul, mul_zero]
  rw [cardFactors_mul hn hm] -- porting note: `simp` does not seem to use this lemma.
  -- ⊢ (if Squarefree n then if Squarefree m then (-1) ^ (↑Ω n + ↑Ω m) else 0 else  …
  simp only [moebius, ZeroHom.coe_mk, squarefree_mul hnm, ite_and, cardFactors_mul hn hm]
  -- ⊢ (if Squarefree n then if Squarefree m then (-1) ^ (↑Ω n + ↑Ω m) else 0 else  …
  rw [pow_add, ite_mul_zero_left, ite_mul_zero_right]
  -- ⊢ ((if Squarefree m then (-1) ^ ↑Ω n else 0) * if Squarefree n then (-1) ^ ↑Ω  …
  split_ifs <;>  -- porting note: added
  simp           -- porting note: added
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align nat.arithmetic_function.is_multiplicative_moebius Nat.ArithmeticFunction.isMultiplicative_moebius

open UniqueFactorizationMonoid

@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  -- ⊢ ↑(μ * ↑ζ) n = ↑1 n
  refine' recOnPosPrimePosCoprime _ _ _ _ n
  · intro p n hp hn
    -- ⊢ ↑(μ * ↑ζ) (p ^ n) = ↑1 (p ^ n)
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    -- ⊢ ∑ k in range n, ↑μ (p ^ (k + 1)) + ↑μ (p ^ 0) = ↑1 (p ^ n)
    simp_rw [pow_zero, moebius_apply_one,
      moebius_apply_prime_pow hp (Nat.succ_ne_zero _), Nat.succ_inj', sum_ite_eq', mem_range,
      if_pos hn, add_left_neg]
    rw [one_apply_ne]
    -- ⊢ p ^ n ≠ 1
    rw [Ne.def, pow_eq_one_iff]
    -- ⊢ ¬p = 1
    · exact hp.ne_one
      -- 🎉 no goals
    · exact hn.ne'
      -- 🎉 no goals
  · rw [ZeroHom.map_zero, ZeroHom.map_zero]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · intro a b _ha _hb hab ha' hb'
    -- ⊢ ↑(μ * ↑ζ) (a * b) = ↑1 (a * b)
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.nat_cast
    -- 🎉 no goals
#align nat.arithmetic_function.moebius_mul_coe_zeta Nat.ArithmeticFunction.moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]
  -- 🎉 no goals
#align nat.arithmetic_function.coe_zeta_mul_moebius Nat.ArithmeticFunction.coe_zeta_mul_moebius

@[simp]
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]
  -- 🎉 no goals
#align nat.arithmetic_function.coe_moebius_mul_coe_zeta Nat.ArithmeticFunction.coe_moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]
  -- 🎉 no goals
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
  -- ⊢ (∀ (n : ℕ), n > 0 → ∑ i in divisors n, f i = g n) ↔ ∀ (n : ℕ), n > 0 → ∑ x i …
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  -- ⊢ (∀ (n : ℕ), n > 0 → ∑ i in divisors n, f i = g n) ↔ ∀ (n : ℕ), n > 0 → ∑ x i …
  trans (ζ : ArithmeticFunction ℤ) • f' = g'
  -- ⊢ (∀ (n : ℕ), n > 0 → ∑ i in divisors n, f i = g n) ↔ ↑ζ • f' = g'
  · rw [ext_iff]
    -- ⊢ (∀ (n : ℕ), n > 0 → ∑ i in divisors n, f i = g n) ↔ ∀ (x : ℕ), ↑(↑ζ • f') x  …
    apply forall_congr'
    -- ⊢ ∀ (a : ℕ), a > 0 → ∑ i in divisors a, f i = g a ↔ ↑(↑ζ • f') a = ↑g' a
    intro n
    -- ⊢ n > 0 → ∑ i in divisors n, f i = g n ↔ ↑(↑ζ • f') n = ↑g' n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', if_false, ZeroHom.coe_mk]
      simp only [coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (ne_of_gt (Nat.pos_of_mem_divisors hx))]
  trans μ • g' = f'
  -- ⊢ ↑ζ • f' = g' ↔ μ • g' = f'
  · constructor <;> intro h
    -- ⊢ ↑ζ • f' = g' → μ • g' = f'
                    -- ⊢ μ • g' = f'
                    -- ⊢ ↑ζ • f' = g'
    · rw [← h, ← mul_smul, moebius_mul_coe_zeta, one_smul]
      -- 🎉 no goals
    · rw [← h, ← mul_smul, coe_zeta_mul_moebius, one_smul]
      -- 🎉 no goals
  · rw [ext_iff]
    -- ⊢ (∀ (x : ℕ), ↑(μ • g') x = ↑f' x) ↔ ∀ (n : ℕ), n > 0 → ∑ x in divisorsAntidia …
    apply forall_congr'
    -- ⊢ ∀ (a : ℕ), ↑(μ • g') a = ↑f' a ↔ a > 0 → ∑ x in divisorsAntidiagonal a, ↑μ x …
    intro n
    -- ⊢ ↑(μ • g') n = ↑f' n ↔ n > 0 → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x. …
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
  -- ⊢ (∀ (n : ℕ), n > 0 → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.snd = f n) …
  apply forall_congr'
  -- ⊢ ∀ (a : ℕ), a > 0 → ∑ x in divisorsAntidiagonal a, ↑μ x.fst • g x.snd = f a ↔ …
  refine' fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => _).congr_left
  -- ⊢ ↑μ x.fst • g x.snd = ↑(↑μ x.fst) * g x.snd
  rw [zsmul_eq_mul]
  -- 🎉 no goals
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
    -- ⊢ ∏ i in divisors n, f i = g n ↔ (∏ i in divisors n, if h : 0 < i then Units.m …
    -- ⊢ (∏ x in divisorsAntidiagonal n, (if h : 0 < x.snd then Units.mk0 (g x.snd) ( …
  · dsimp
    -- ⊢ ∏ i in divisors n, f i = g n ↔ (∏ i in divisors n, if h : 0 < i then Units.m …
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    -- ⊢ f x = ↑(Units.coeHom R) (if h : 0 < x then Units.mk0 (f x) (_ : f x ≠ 0) els …
    rw [dif_pos (Nat.pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
    -- 🎉 no goals
  · dsimp
    -- ⊢ (∏ x in divisorsAntidiagonal n, (if h : 0 < x.snd then Units.mk0 (g x.snd) ( …
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    -- ⊢ ↑(Units.coeHom R) ((if h : 0 < x.snd then Units.mk0 (g x.snd) (_ : g x.snd ≠ …
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
  -- ⊢ (∀ (n : ℕ), n > 0 → n ∈ s → ∑ i in divisors n, f i = g n) → ∀ (n : ℕ), n > 0 …
  · intro h
    -- ⊢ ∀ (n : ℕ), n > 0 → n ∈ s → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.snd …
    let G := fun (n:ℕ) => (∑ i in n.divisors, f i)
    -- ⊢ ∀ (n : ℕ), n > 0 → n ∈ s → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.snd …
    intro n hn hnP
    -- ⊢ ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.snd = f n
    suffices ∑ d in n.divisors, μ (n/d) • G d = f n from by
      rw [Nat.sum_divisorsAntidiagonal' (f:= fun x y => μ x • g y), ←this, sum_congr rfl]
      intro d hd
      rw [←h d (Nat.pos_of_mem_divisors hd) $ hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    rw [←Nat.sum_divisorsAntidiagonal' (f:= fun x y => μ x • G y)]
    -- ⊢ ∑ i in divisorsAntidiagonal n, ↑μ i.fst • G i.snd = f n
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    -- ⊢ ∀ (n : ℕ), n > 0 → ∑ i in divisors n, f i = G n
    intro _ _; rfl
    -- ⊢ ∑ i in divisors n✝, f i = G n✝
               -- 🎉 no goals
  · intro h
    -- ⊢ ∀ (n : ℕ), n > 0 → n ∈ s → ∑ i in divisors n, f i = g n
    let F := fun (n:ℕ) => ∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd
    -- ⊢ ∀ (n : ℕ), n > 0 → n ∈ s → ∑ i in divisors n, f i = g n
    intro n hn hnP
    -- ⊢ ∑ i in divisors n, f i = g n
    suffices ∑ d in n.divisors, F d = g n from by
      rw [←this, sum_congr rfl]
      intro d hd
      rw [←h d (Nat.pos_of_mem_divisors hd) $ hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    -- ⊢ ∀ (n : ℕ), n > 0 → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.snd = F n
    intro _ _; rfl
    -- ⊢ ∑ x in divisorsAntidiagonal n✝, ↑μ x.fst • g x.snd = F n✝
               -- 🎉 no goals

theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i in n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine' forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h _ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs
  -- 🎉 no goals

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on [Ring R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i in n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x : ℕ × ℕ in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  -- ⊢ (∀ (n : ℕ), n > 0 → n ∈ s → ∑ x in divisorsAntidiagonal n, ↑μ x.fst • g x.sn …
  apply forall_congr'
  -- ⊢ ∀ (a : ℕ), a > 0 → a ∈ s → ∑ x in divisorsAntidiagonal a, ↑μ x.fst • g x.snd …
  intro a; refine' imp_congr_right _
  -- ⊢ a > 0 → a ∈ s → ∑ x in divisorsAntidiagonal a, ↑μ x.fst • g x.snd = f a ↔ a  …
           -- ⊢ a > 0 → (a ∈ s → ∑ x in divisorsAntidiagonal a, ↑μ x.fst • g x.snd = f a ↔ a …
  refine' fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => _).congr_left
  -- ⊢ ↑μ x.fst • g x.snd = ↑(↑μ x.fst) * g x.snd
  rw [zsmul_eq_mul]
  -- 🎉 no goals

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
    -- ⊢ n ∈ s → ∏ i in divisors n, f i = g n ↔ n ∈ s → ∏ i in divisors n, (fun n =>  …
    -- ⊢ n ∈ s → ∏ x in divisorsAntidiagonal n, (fun n => if h : 0 < n then Units.mk0 …
  · dsimp
    -- ⊢ n ∈ s → ∏ i in divisors n, f i = g n ↔ n ∈ s → (∏ i in divisors n, if h : 0  …
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    -- ⊢ f x = ↑(Units.coeHom R) (if h : 0 < x then Units.mk0 (f x) (_ : f x ≠ 0) els …
    rw [dif_pos (Nat.pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
    -- 🎉 no goals
  · dsimp
    -- ⊢ (n ∈ s → ∏ x in divisorsAntidiagonal n, (if h : 0 < x.snd then Units.mk0 (g  …
    rw [dif_pos hn, ← Units.eq_iff, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    -- ⊢ ↑(Units.coeHom R) ((if h : 0 < x.snd then Units.mk0 (g x.snd) (_ : g x.snd ≠ …
    rw [dif_pos (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end SpecialFunctions

end ArithmeticFunction

end Nat
