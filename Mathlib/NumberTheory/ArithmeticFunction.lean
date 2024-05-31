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
import Mathlib.Tactic.ArithMult

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
 * `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
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

All notation is localized in the namespace `ArithmeticFunction`.

The arithmetic functions `ζ`, `σ`, `ω`, `Ω` and `μ` have Greek letter names.

In addition, there are separate locales `ArithmeticFunction.zeta` for `ζ`,
`ArithmeticFunction.sigma` for `σ`, `ArithmeticFunction.omega` for `ω`,
`ArithmeticFunction.Omega` for `Ω`, and `ArithmeticFunction.Moebius` for `μ`,
to allow for selective access to these notations.

The arithmetic function $$n \mapsto \prod_{p \mid n} f(p)$$ is given custom notation
`∏ᵖ p ∣ n, f p` when applied to `n`.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

open Finset

open Nat

variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `ArithmeticFunctions` is by
  Dirichlet convolution. -/
def ArithmeticFunction [Zero R] :=
  ZeroHom ℕ R
#align nat.arithmetic_function ArithmeticFunction

instance ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R) :=
  inferInstanceAs (Zero (ZeroHom ℕ R))

instance [Zero R] : Inhabited (ArithmeticFunction R) := inferInstanceAs (Inhabited (ZeroHom ℕ R))

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

--  porting note: used to be `CoeFun`
instance : FunLike (ArithmeticFunction R) ℕ R :=
  inferInstanceAs (FunLike (ZeroHom ℕ R) ℕ R)

@[simp]
theorem toFun_eq (f : ArithmeticFunction R) : f.toFun = f := rfl
#align nat.arithmetic_function.to_fun_eq ArithmeticFunction.toFun_eq

@[simp]
theorem coe_mk (f : ℕ → R) (hf) : @DFunLike.coe (ArithmeticFunction R) _ _ _
    (ZeroHom.mk f hf) = f := rfl

@[simp]
theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
  ZeroHom.map_zero' f
#align nat.arithmetic_function.map_zero ArithmeticFunction.map_zero

theorem coe_inj {f g : ArithmeticFunction R} : (f : ℕ → R) = g ↔ f = g :=
  DFunLike.coe_fn_eq
#align nat.arithmetic_function.coe_inj ArithmeticFunction.coe_inj

@[simp]
theorem zero_apply {x : ℕ} : (0 : ArithmeticFunction R) x = 0 :=
  ZeroHom.zero_apply x
#align nat.arithmetic_function.zero_apply ArithmeticFunction.zero_apply

@[ext]
theorem ext ⦃f g : ArithmeticFunction R⦄ (h : ∀ x, f x = g x) : f = g :=
  ZeroHom.ext h
#align nat.arithmetic_function.ext ArithmeticFunction.ext

theorem ext_iff {f g : ArithmeticFunction R} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align nat.arithmetic_function.ext_iff ArithmeticFunction.ext_iff

section One

variable [One R]

instance one : One (ArithmeticFunction R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
  rfl
#align nat.arithmetic_function.one_apply ArithmeticFunction.one_apply

@[simp]
theorem one_one : (1 : ArithmeticFunction R) 1 = 1 :=
  rfl
#align nat.arithmetic_function.one_one ArithmeticFunction.one_one

@[simp]
theorem one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : ArithmeticFunction R) x = 0 :=
  if_neg h
#align nat.arithmetic_function.one_apply_ne ArithmeticFunction.one_apply_ne

end One

end Zero

/-- Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We cannot inline
this in `natCoe` because it gets unfolded too much. -/
@[coe]  -- Porting note: added `coe` tag.
def natToArithmeticFunction [AddMonoidWithOne R] :
    (ArithmeticFunction ℕ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction ℕ) (ArithmeticFunction R) :=
  ⟨natToArithmeticFunction⟩
#align nat.arithmetic_function.nat_coe ArithmeticFunction.natCoe

@[simp]
theorem natCoe_nat (f : ArithmeticFunction ℕ) : natToArithmeticFunction f = f :=
  ext fun _ => cast_id _
#align nat.arithmetic_function.nat_coe_nat ArithmeticFunction.natCoe_nat

@[simp]
theorem natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x :=
  rfl
#align nat.arithmetic_function.nat_coe_apply ArithmeticFunction.natCoe_apply

/-- Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We cannot inline
this in `intCoe` because it gets unfolded too much. -/
@[coe]
def ofInt [AddGroupWithOne R] :
    (ArithmeticFunction ℤ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction ℤ) (ArithmeticFunction R) :=
  ⟨ofInt⟩
#align nat.arithmetic_function.int_coe ArithmeticFunction.intCoe

@[simp]
theorem intCoe_int (f : ArithmeticFunction ℤ) : ofInt f = f :=
  ext fun _ => Int.cast_id
#align nat.arithmetic_function.int_coe_int ArithmeticFunction.intCoe_int

@[simp]
theorem intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction ℤ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x := rfl
#align nat.arithmetic_function.int_coe_apply ArithmeticFunction.intCoe_apply

@[simp]
theorem coe_coe [AddGroupWithOne R] {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℤ) : ArithmeticFunction R) = (f : ArithmeticFunction R) := by
  ext
  simp
#align nat.arithmetic_function.coe_coe ArithmeticFunction.coe_coe

@[simp]
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction ℕ) : ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]
#align nat.arithmetic_function.nat_coe_one ArithmeticFunction.natCoe_one

@[simp]
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction ℤ) :
    ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]
#align nat.arithmetic_function.int_coe_one ArithmeticFunction.intCoe_one

section AddMonoid

variable [AddMonoid R]

instance add : Add (ArithmeticFunction R) :=
  ⟨fun f g => ⟨fun n => f n + g n, by simp⟩⟩

@[simp]
theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
  rfl
#align nat.arithmetic_function.add_apply ArithmeticFunction.add_apply

instance instAddMonoid : AddMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.zero R,
    ArithmeticFunction.add with
    add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
    zero_add := fun _ => ext fun _ => zero_add _
    add_zero := fun _ => ext fun _ => add_zero _
    nsmul := nsmulRec }
#align nat.arithmetic_function.add_monoid ArithmeticFunction.instAddMonoid

end AddMonoid

instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid,
    ArithmeticFunction.one with
    natCast := fun n => ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
    natCast_zero := by ext; simp
    natCast_succ := fun n => by ext x; by_cases h : x = 1 <;> simp [h] }
#align nat.arithmetic_function.add_monoid_with_one ArithmeticFunction.instAddMonoidWithOne

instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _ }

instance [NegZeroClass R] : Neg (ArithmeticFunction R) where
  neg f := ⟨fun n => -f n, by simp⟩

instance [AddGroup R] : AddGroup (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with
    add_left_neg := fun _ => ext fun _ => add_left_neg _
    zsmul := zsmulRec }

instance [AddCommGroup R] : AddCommGroup (ArithmeticFunction R) :=
  { show AddGroup (ArithmeticFunction R) by infer_instance with
    add_comm := fun _ _ ↦ add_comm _ _ }

section SMul

variable {M : Type*} [Zero R] [AddCommMonoid M] [SMul R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : SMul (ArithmeticFunction R) (ArithmeticFunction M) :=
  ⟨fun f g => ⟨fun n => ∑ x ∈ divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩⟩

@[simp]
theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
    (f • g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst • g x.snd :=
  rfl
#align nat.arithmetic_function.smul_apply ArithmeticFunction.smul_apply

end SMul

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance [Semiring R] : Mul (ArithmeticFunction R) :=
  ⟨(· • ·)⟩

@[simp]
theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f * g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst * g x.snd :=
  rfl
#align nat.arithmetic_function.mul_apply ArithmeticFunction.mul_apply

theorem mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 * g 1 := by simp
#align nat.arithmetic_function.mul_apply_one ArithmeticFunction.mul_apply_one

@[simp, norm_cast]
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  simp
#align nat.arithmetic_function.nat_coe_mul ArithmeticFunction.natCoe_mul

@[simp, norm_cast]
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  simp
#align nat.arithmetic_function.int_coe_mul ArithmeticFunction.intCoe_mul

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)
#align nat.arithmetic_function.mul_smul' ArithmeticFunction.mul_smul'

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
    simp only [Con, mem_divisorsAntidiagonal, one_mul, Ne] at ymem
    simp only [mem_singleton, Prod.ext_iff] at ynmem
    -- Porting note: `tauto` worked from here.
    cases y
    subst con
    simp only [true_and, one_mul, x0, not_false_eq_true, and_true] at ynmem ymem
    tauto

  simp [y1ne]
#align nat.arithmetic_function.one_smul' ArithmeticFunction.one_smul'

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
        cases y; subst con -- Porting note: added
        simp only [Con, mem_divisorsAntidiagonal, mul_one, Ne] at ymem
        simp only [mem_singleton, Prod.ext_iff] at ynmem
        tauto
      simp [y2ne]
    mul_assoc := mul_smul' }
#align nat.arithmetic_function.monoid ArithmeticFunction.instMonoid

instance instSemiring : Semiring (ArithmeticFunction R) :=
  -- Porting note: I reorganized this instance
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
#align nat.arithmetic_function.semiring ArithmeticFunction.instSemiring

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
    mul_comm := mul_comm
    zsmul := (· • ·) }

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
#align nat.arithmetic_function.zeta ArithmeticFunction.zeta

@[inherit_doc]
scoped[ArithmeticFunction] notation "ζ" => ArithmeticFunction.zeta

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta

@[simp]
theorem zeta_apply {x : ℕ} : ζ x = if x = 0 then 0 else 1 :=
  rfl
#align nat.arithmetic_function.zeta_apply ArithmeticFunction.zeta_apply

theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 :=
  if_neg h
#align nat.arithmetic_function.zeta_apply_ne ArithmeticFunction.zeta_apply_ne

-- Porting note: removed `@[simp]`, LHS not in normal form
theorem coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [Module R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    ((↑ζ : ArithmeticFunction R) • f) x = ∑ i ∈ divisors x, f i := by
  rw [smul_apply]
  trans ∑ i ∈ divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]
#align nat.arithmetic_function.coe_zeta_smul_apply ArithmeticFunction.coe_zeta_smul_apply

-- Porting note: removed `@[simp]` to make the linter happy.
theorem coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (↑ζ * f) x = ∑ i ∈ divisors x, f i :=
  coe_zeta_smul_apply
#align nat.arithmetic_function.coe_zeta_mul_apply ArithmeticFunction.coe_zeta_mul_apply

-- Porting note: removed `@[simp]` to make the linter happy.
theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (f * ζ) x = ∑ i ∈ divisors x, f i := by
  rw [mul_apply]
  trans ∑ i ∈ divisorsAntidiagonal x, f i.1
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one]
  · rw [← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
#align nat.arithmetic_function.coe_mul_zeta_apply ArithmeticFunction.coe_mul_zeta_apply

theorem zeta_mul_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (ζ * f) x = ∑ i ∈ divisors x, f i :=
  coe_zeta_mul_apply
  -- Porting note: was `by rw [← nat_coe_nat ζ, coe_zeta_mul_apply]`.  Is this `theorem` obsolete?
#align nat.arithmetic_function.zeta_mul_apply ArithmeticFunction.zeta_mul_apply

theorem mul_zeta_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (f * ζ) x = ∑ i ∈ divisors x, f i :=
  coe_mul_zeta_apply
  -- Porting note: was `by rw [← natCoe_nat ζ, coe_mul_zeta_apply]`.  Is this `theorem` obsolete=
#align nat.arithmetic_function.mul_zeta_apply ArithmeticFunction.mul_zeta_apply

end Zeta

open ArithmeticFunction

section Pmul

/-- This is the pointwise product of `ArithmeticFunction`s. -/
def pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun x => f x * g x, by simp⟩
#align nat.arithmetic_function.pmul ArithmeticFunction.pmul

@[simp]
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : ℕ} : f.pmul g x = f x * g x :=
  rfl
#align nat.arithmetic_function.pmul_apply ArithmeticFunction.pmul_apply

theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  simp [mul_comm]
#align nat.arithmetic_function.pmul_comm ArithmeticFunction.pmul_comm

lemma pmul_assoc [CommMonoidWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R) :
    pmul (pmul f₁ f₂) f₃ = pmul f₁ (pmul f₂ f₃) := by
  ext
  simp only [pmul_apply, mul_assoc]

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  cases x <;> simp [Nat.succ_ne_zero]
#align nat.arithmetic_function.pmul_zeta ArithmeticFunction.pmul_zeta

@[simp]
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  cases x <;> simp [Nat.succ_ne_zero]
#align nat.arithmetic_function.zeta_pmul ArithmeticFunction.zeta_pmul

end NonAssocSemiring

variable [Semiring R]

/-- This is the pointwise power of `ArithmeticFunction`s. -/
def ppow (f : ArithmeticFunction R) (k : ℕ) : ArithmeticFunction R :=
  if h0 : k = 0 then ζ else ⟨fun x ↦ f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩
#align nat.arithmetic_function.ppow ArithmeticFunction.ppow

@[simp]
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]
#align nat.arithmetic_function.ppow_zero ArithmeticFunction.ppow_zero

@[simp]
theorem ppow_apply {f : ArithmeticFunction R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow, dif_neg (Nat.ne_of_gt kpos)]
  rfl
#align nat.arithmetic_function.ppow_apply ArithmeticFunction.ppow_apply

theorem ppow_succ' {f : ArithmeticFunction R} {k : ℕ} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ']
  induction k <;> simp
#align nat.arithmetic_function.ppow_succ ArithmeticFunction.ppow_succ'

theorem ppow_succ {f : ArithmeticFunction R} {k : ℕ} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  rw [ppow_apply (Nat.succ_pos k), _root_.pow_succ]
  induction k <;> simp
#align nat.arithmetic_function.ppow_succ' ArithmeticFunction.ppow_succ

end Pmul

section Pdiv

/-- This is the pointwise division of `ArithmeticFunction`s. -/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, ne_eq, not_true, div_zero]⟩

@[simp]
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coercion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  cases n <;> simp [succ_ne_zero]

end Pdiv

section ProdPrimeFactors

/-- The map $n \mapsto \prod_{p \mid n} f(p)$ as an arithmetic function -/
def prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, f p
  map_zero' := if_pos rfl

open Batteries.ExtendedBinder

/-- `∏ᵖ p ∣ n, f p` is custom notation for `prodPrimeFactors f n` -/
scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x ↦ $r) $n)

@[simp]
theorem prodPrimeFactors_apply [CommMonoidWithZero R] {f: ℕ → R} {n : ℕ} (hn : n ≠ 0) :
    ∏ᵖ p ∣ n, f p = ∏ p ∈ n.primeFactors, f p :=
  if_neg hn

end ProdPrimeFactors

/-- Multiplicative functions -/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n
#align nat.arithmetic_function.is_multiplicative ArithmeticFunction.IsMultiplicative

namespace IsMultiplicative

section MonoidWithZero

variable [MonoidWithZero R]

@[simp, arith_mult]
theorem map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1 :=
  h.1
#align nat.arithmetic_function.is_multiplicative.map_one ArithmeticFunction.IsMultiplicative.map_one

@[simp]
theorem map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : ℕ}
    (h : m.Coprime n) : f (m * n) = f m * f n :=
  hf.2 h
#align nat.arithmetic_function.is_multiplicative.map_mul_of_coprime ArithmeticFunction.IsMultiplicative.map_mul_of_coprime

end MonoidWithZero

theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι → ℕ) {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (Coprime on g)) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  classical
    induction' s using Finset.induction_on with a s has ih hs
    · simp [hf]
    rw [coe_insert, Set.pairwise_insert_of_symmetric (Coprime.symmetric.comap g)] at hs
    rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact .prod_right fun i hi => hs.2 _ hi (hi.ne_of_not_mem has).symm
#align nat.arithmetic_function.is_multiplicative.map_prod ArithmeticFunction.IsMultiplicative.map_prod

theorem map_prod_of_prime [CommSemiring R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f)
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

theorem map_prod_of_subset_primeFactors [CommSemiring R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f) (l : ℕ)
    (t : Finset ℕ) (ht : t ⊆ l.primeFactors) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

@[arith_mult]
theorem natCast {f : ArithmeticFunction ℕ} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- Porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
#align nat.arithmetic_function.is_multiplicative.nat_cast ArithmeticFunction.IsMultiplicative.natCast

@[deprecated (since := "2024-04-17")]
alias nat_cast := natCast

@[arith_mult]
theorem intCast {f : ArithmeticFunction ℤ} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
                                 -- Porting note: was `by simp [cop, h]`
  ⟨by simp [h], fun {m n} cop => by simp [h.2 cop]⟩
#align nat.arithmetic_function.is_multiplicative.int_cast ArithmeticFunction.IsMultiplicative.intCast

@[deprecated (since := "2024-04-17")]
alias int_cast := intCast

@[arith_mult]
theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f * g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  simp only [mul_apply]
  intro m n cop
  rw [sum_mul_sum, ← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) ↦ (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    simp only [mem_divisorsAntidiagonal, Nat.mul_eq_zero, Ne]
    constructor
    · ring
    rw [Nat.mul_eq_zero] at *
    apply not_or_of_not ha hb
  · simp only [Set.InjOn, mem_coe, mem_divisorsAntidiagonal, Ne, mem_product, Prod.mk.inj_iff]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hcd h
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
  · simp only [Set.SurjOn, Set.subset_def, mem_coe, mem_divisorsAntidiagonal, Ne, mem_product,
      Set.mem_image, exists_prop, Prod.mk.inj_iff]
    rintro ⟨b1, b2⟩ h
    dsimp at h
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
      Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Nat.mul_eq_zero, not_or] at h
      simp [h.2.1, h.2.2]
    rw [mul_comm n m, h.1]
  · simp only [mem_divisorsAntidiagonal, Ne, mem_product]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    dsimp only
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
      hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
    ring
#align nat.arithmetic_function.is_multiplicative.mul ArithmeticFunction.IsMultiplicative.mul

@[arith_mult]
theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun {m n} cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩
#align nat.arithmetic_function.is_multiplicative.pmul ArithmeticFunction.IsMultiplicative.pmul

@[arith_mult]
theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨ by simp [hf, hg], fun {m n} cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop,
      div_eq_mul_inv, mul_inv]
    apply mul_mul_mul_comm ⟩

/-- For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
nonrec  -- Porting note: added
theorem multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) :=
  multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn
#align nat.arithmetic_function.is_multiplicative.multiplicative_factorization ArithmeticFunction.IsMultiplicative.multiplicative_factorization

/-- A recapitulation of the definition of multiplicative that is simpler for proofs -/
theorem iff_ne_zero [MonoidWithZero R] {f : ArithmeticFunction R} :
    IsMultiplicative f ↔
      f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n := by
  refine and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => ?_⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn
#align nat.arithmetic_function.is_multiplicative.iff_ne_zero ArithmeticFunction.IsMultiplicative.iff_ne_zero

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
#align nat.arithmetic_function.is_multiplicative.eq_iff_eq_on_prime_powers ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers

@[arith_mult]
theorem prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) :
    IsMultiplicative (prodPrimeFactors f) := by
  rw [iff_ne_zero]
  refine ⟨prodPrimeFactors_apply one_ne_zero, ?_⟩
  intro x y hx hy hxy
  have hxy₀ : x * y ≠ 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀, prodPrimeFactors_apply hx, prodPrimeFactors_apply hy,
    Nat.primeFactors_mul hx hy, ← Finset.prod_union hxy.disjoint_primeFactors]

theorem prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : ℕ} (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f:=f) (g:=g)]
  rw [Finset.prod_add, mul_apply, sum_divisorsAntidiagonal (f · * g ·),
    ← divisors_filter_squarefree_of_squarefree hn, sum_divisors_filter_squarefree hn.ne_zero,
    factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  rw [t.prod_val, Function.id_def,
    ← prod_primeFactors_sdiff_of_squarefree hn (Finset.mem_powerset.mp ht),
    hf.map_prod_of_subset_primeFactors n t (Finset.mem_powerset.mp ht),
    ← hg.map_prod_of_subset_primeFactors n (_ \ t) (Finset.sdiff_subset _ t)]

theorem lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} :
    f (x.lcm y) * f (x.gcd y) = f x * f y := by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, Nat.lcm_zero_left, Nat.gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, Nat.lcm_zero_right, Nat.gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y ≠ 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := lcm_ne_zero hx hy
  have hfi_zero : ∀ {i}, f (i ^ 0) = 1 := by
    intro i; rw [Nat.pow_zero, hf.1]
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
nonrec  -- Porting note (#11445): added
def id : ArithmeticFunction ℕ :=
  ⟨id, rfl⟩
#align nat.arithmetic_function.id ArithmeticFunction.id

@[simp]
theorem id_apply {x : ℕ} : id x = x :=
  rfl
#align nat.arithmetic_function.id_apply ArithmeticFunction.id_apply

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : ArithmeticFunction ℕ :=
  id.ppow k
#align nat.arithmetic_function.pow ArithmeticFunction.pow

@[simp]
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k
  · simp [pow]
  rename_i k  -- Porting note: added
  simp [pow, k.succ_pos.ne']
#align nat.arithmetic_function.pow_apply ArithmeticFunction.pow_apply

theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp
#align nat.arithmetic_function.pow_zero_eq_zeta ArithmeticFunction.pow_zero_eq_zeta

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩
#align nat.arithmetic_function.sigma ArithmeticFunction.sigma

@[inherit_doc]
scoped[ArithmeticFunction] notation "σ" => ArithmeticFunction.sigma

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

theorem sigma_apply {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl
#align nat.arithmetic_function.sigma_apply ArithmeticFunction.sigma_apply

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]
#align nat.arithmetic_function.sigma_one_apply ArithmeticFunction.sigma_one_apply

theorem sigma_zero_apply (n : ℕ) : σ 0 n = (divisors n).card := by simp [sigma_apply]
#align nat.arithmetic_function.sigma_zero_apply ArithmeticFunction.sigma_zero_apply

theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  rw [sigma_zero_apply, divisors_prime_pow hp, card_map, card_range]
#align nat.arithmetic_function.sigma_zero_apply_prime_pow ArithmeticFunction.sigma_zero_apply_prime_pow

theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  rw [sigma, zeta_mul_apply]
  apply sum_congr rfl
  intro x hx
  rw [pow_apply, if_neg (not_and_of_not_right _ _)]
  contrapose! hx
  simp [hx]
#align nat.arithmetic_function.zeta_mul_pow_eq_sigma ArithmeticFunction.zeta_mul_pow_eq_sigma

@[arith_mult]
theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2
    ⟨by simp, by
      intro m n hm _hn hmn
      rcases eq_or_ne m 1 with (rfl | hm')
      · simp
      rw [one_apply_ne, one_apply_ne hm', zero_mul]
      rw [Ne, mul_eq_one, not_and_or]
      exact Or.inl hm'⟩
#align nat.arithmetic_function.is_multiplicative_one ArithmeticFunction.isMultiplicative_one

@[arith_mult]
theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align nat.arithmetic_function.is_multiplicative_zeta ArithmeticFunction.isMultiplicative_zeta

@[arith_mult]
theorem isMultiplicative_id : IsMultiplicative ArithmeticFunction.id :=
  ⟨rfl, fun {_ _} _ => rfl⟩
#align nat.arithmetic_function.is_multiplicative_id ArithmeticFunction.isMultiplicative_id

@[arith_mult]
theorem IsMultiplicative.ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction' k with k hi
  · exact isMultiplicative_zeta.natCast
  · rw [ppow_succ']
    apply hf.pmul hi
#align nat.arithmetic_function.is_multiplicative.ppow ArithmeticFunction.IsMultiplicative.ppow

@[arith_mult]
theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
#align nat.arithmetic_function.is_multiplicative_pow ArithmeticFunction.isMultiplicative_pow

@[arith_mult]
theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow
#align nat.arithmetic_function.is_multiplicative_sigma ArithmeticFunction.isMultiplicative_sigma

/-- `Ω n` is the number of prime factors of `n`. -/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.length, by simp⟩
#align nat.arithmetic_function.card_factors ArithmeticFunction.cardFactors

@[inherit_doc]
scoped[ArithmeticFunction] notation "Ω" => ArithmeticFunction.cardFactors

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

theorem cardFactors_apply {n : ℕ} : Ω n = n.factors.length :=
  rfl
#align nat.arithmetic_function.card_factors_apply ArithmeticFunction.cardFactors_apply

lemma cardFactors_zero : Ω 0 = 0 := by simp

@[simp] theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors_apply]
#align nat.arithmetic_function.card_factors_one ArithmeticFunction.cardFactors_one

@[simp]
theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine ⟨fun h => ?_, fun h => List.length_eq_one.2 ⟨n, factors_prime h⟩⟩
  cases' n with n
  · simp at h
  rcases List.length_eq_one.1 h with ⟨x, hx⟩
  rw [← prod_factors n.add_one_ne_zero, hx, List.prod_singleton]
  apply prime_of_mem_factors
  rw [hx, List.mem_singleton]
#align nat.arithmetic_function.card_factors_eq_one_iff_prime ArithmeticFunction.cardFactors_eq_one_iff_prime

theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]
#align nat.arithmetic_function.card_factors_mul ArithmeticFunction.cardFactors_mul

theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]
#align nat.arithmetic_function.card_factors_multiset_prod ArithmeticFunction.cardFactors_multiset_prod

@[simp]
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp
#align nat.arithmetic_function.card_factors_apply_prime ArithmeticFunction.cardFactors_apply_prime

@[simp]
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  rw [cardFactors_apply, hp.factors_pow, List.length_replicate]
#align nat.arithmetic_function.card_factors_apply_prime_pow ArithmeticFunction.cardFactors_apply_prime_pow

/-- `ω n` is the number of distinct prime factors of `n`. -/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.factors.dedup.length, by simp⟩
#align nat.arithmetic_function.card_distinct_factors ArithmeticFunction.cardDistinctFactors

@[inherit_doc]
scoped[ArithmeticFunction] notation "ω" => ArithmeticFunction.cardDistinctFactors

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

theorem cardDistinctFactors_zero : ω 0 = 0 := by simp
#align nat.arithmetic_function.card_distinct_factors_zero ArithmeticFunction.cardDistinctFactors_zero

@[simp]
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]
#align nat.arithmetic_function.card_distinct_factors_one ArithmeticFunction.cardDistinctFactors_one

theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.factors.dedup.length :=
  rfl
#align nat.arithmetic_function.card_distinct_factors_apply ArithmeticFunction.cardDistinctFactors_apply

theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_factors h0, cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.factors.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · rw [h.dedup]
    rfl
#align nat.arithmetic_function.card_distinct_factors_eq_card_factors_iff_squarefree ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree

@[simp]
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 := by
  rw [cardDistinctFactors_apply, hp.factors_pow, List.replicate_dedup hk, List.length_singleton]
#align nat.arithmetic_function.card_distinct_factors_apply_prime_pow ArithmeticFunction.cardDistinctFactors_apply_prime_pow

@[simp]
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]
#align nat.arithmetic_function.card_distinct_factors_apply_prime ArithmeticFunction.cardDistinctFactors_apply_prime

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩
#align nat.arithmetic_function.moebius ArithmeticFunction.moebius

@[inherit_doc]
scoped[ArithmeticFunction] notation "μ" => ArithmeticFunction.moebius

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

@[simp]
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h
#align nat.arithmetic_function.moebius_apply_of_squarefree ArithmeticFunction.moebius_apply_of_squarefree

@[simp]
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h
#align nat.arithmetic_function.moebius_eq_zero_of_not_squarefree ArithmeticFunction.moebius_eq_zero_of_not_squarefree

theorem moebius_apply_one : μ 1 = 1 := by simp
#align nat.arithmetic_function.moebius_apply_one ArithmeticFunction.moebius_apply_one

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · simp [h, pow_ne_zero]
#align nat.arithmetic_function.moebius_ne_zero_iff_squarefree ArithmeticFunction.moebius_ne_zero_iff_squarefree

theorem moebius_eq_or (n : ℕ) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  have := moebius_eq_or n
  aesop
#align nat.arithmetic_function.moebius_ne_zero_iff_eq_or ArithmeticFunction.moebius_ne_zero_iff_eq_or

theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [pow_eq_zero_iff, moebius_eq_zero_of_not_squarefree h,
    zero_pow (show 2 ≠ 0 by norm_num)]

theorem abs_moebius {n : ℕ} :
    |μ n| = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

theorem abs_moebius_le_one {n : ℕ} : |μ n| ≤ 1 := by
  rw [abs_moebius, apply_ite (· ≤ 1)]
  simp

theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]
#align nat.arithmetic_function.moebius_apply_prime ArithmeticFunction.moebius_apply_prime

theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  exact Or.inr h
#align nat.arithmetic_function.moebius_apply_prime_pow ArithmeticFunction.moebius_apply_prime_pow

theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  rintro rfl
  exact hn' (by simpa)
#align nat.arithmetic_function.moebius_apply_is_prime_pow_not_prime ArithmeticFunction.moebius_apply_isPrimePow_not_prime

@[arith_mult]
theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, ZeroHom.coe_mk, coe_mk, ZeroHom.toFun_eq_coe, Eq.ndrec, ZeroHom.coe_mk,
    IsUnit.mul_iff, Nat.isUnit_iff, squarefree_mul hnm, ite_zero_mul_ite_zero,
    cardFactors_mul hn hm, pow_add]
#align nat.arithmetic_function.is_multiplicative_moebius ArithmeticFunction.isMultiplicative_moebius

theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree [CommSemiring R]
    {f : ArithmeticFunction R} (h_mult : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 + f p) = ∑ d ∈ n.divisors, f d := by
  trans (∏ᵖ p ∣ n, ((ζ:ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply Finset.prod_congr rfl; intro p hp;
    rw [zeta_apply_ne (prime_of_mem_factors <| List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree h_mult hn,
    coe_zeta_mul_apply]

theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d := by
  trans (∏ p ∈ n.primeFactors, (1 + (ArithmeticFunction.pmul (μ:ArithmeticFunction R) f) p))
  · apply Finset.prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_factors (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.intCast.pmul hf).prodPrimeFactors_one_add_of_squarefree hn]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  refine recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p n hp hn
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp_rw [Nat.pow_zero, moebius_apply_one,
      moebius_apply_prime_pow hp (Nat.succ_ne_zero _), Nat.succ_inj', sum_ite_eq', mem_range,
      if_pos hn, add_left_neg]
    rw [one_apply_ne]
    rw [Ne, pow_eq_one_iff]
    · exact hp.ne_one
    · exact hn.ne'
  · rw [ZeroHom.map_zero, ZeroHom.map_zero]
  · simp
  · intro a b _ha _hb hab ha' hb'
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast
#align nat.arithmetic_function.moebius_mul_coe_zeta ArithmeticFunction.moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]
#align nat.arithmetic_function.coe_zeta_mul_moebius ArithmeticFunction.coe_zeta_mul_moebius

@[simp]
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]
#align nat.arithmetic_function.coe_moebius_mul_coe_zeta ArithmeticFunction.coe_moebius_mul_coe_zeta

@[simp]
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]
#align nat.arithmetic_function.coe_zeta_mul_coe_moebius ArithmeticFunction.coe_zeta_mul_coe_moebius

section CommRing

variable [CommRing R]

instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/-- A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`. -/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩
#align nat.arithmetic_function.zeta_unit ArithmeticFunction.zetaUnit

@[simp]
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl
#align nat.arithmetic_function.coe_zeta_unit ArithmeticFunction.coe_zetaUnit

@[simp]
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl
#align nat.arithmetic_function.inv_zeta_unit ArithmeticFunction.inv_zetaUnit

end CommRing

/-- Möbius inversion for functions to an `AddCommGroup`. -/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
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
      simp only [f', g', coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (Nat.pos_of_mem_divisors hx).ne']
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
      -- Porting note: added following `simp only`
      simp only [f', g', Nat.isUnit_iff, coe_mk, ZeroHom.toFun_eq_coe, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (Nat.pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)).ne']
#align nat.arithmetic_function.sum_eq_iff_sum_smul_moebius_eq ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq

/-- Möbius inversion for functions to a `Ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [Ring R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]
#align nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq

/-- Möbius inversion for functions to a `CommGroup`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _
#align nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq

/-- Möbius inversion for functions to a `CommGroupWithZero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R}
    (hf : ∀ n : ℕ, 0 < n → f n ≠ 0) (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
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
#align nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq_of_nonzero ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero

/-- Möbius inversion for functions to an `AddCommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n:ℕ) => (∑ i ∈ n.divisors, f i)
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, μ (n/d) • G d = f n from by
      rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • g y), ← this, sum_congr rfl]
      intro d hd
      rw [← h d (Nat.pos_of_mem_divisors hd) <| hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    rw [← Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n:ℕ) => ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, F d = g n from by
      rw [← this, sum_congr rfl]
      intro d hd
      rw [← h d (Nat.pos_of_mem_divisors hd) <| hs d n (Nat.dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl

theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i ∈ n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on [Ring R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/-- Möbius inversion for functions to a `CommGroupWithZero`, where the equalities only hold on
a well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) {f g : ℕ → R}
    (hf : ∀ n > 0, f n ≠ 0) (hg : ∀ n > 0, g n ≠ 0):
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs) )
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
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

theorem card_divisors (n : ℕ) (hnne0 : n ≠ 0) :
    n.divisors.card = n.primeFactors.prod (n.factorization · + 1) := by
  rw [← sigma_zero_apply, isMultiplicative_sigma.multiplicative_factorization _ hnne0]
  exact Finset.prod_congr n.support_factorization fun _ h =>
    sigma_zero_apply_prime_pow <| Nat.prime_of_mem_primeFactors h

end ArithmeticFunction
