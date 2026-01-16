/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# The arithmetic function `ζ`

We define `ζ` to be the arithmetic function with `ζ n = 1` for `0 < n` (whose Dirichlet series
is the Riemann zeta function).

## Main Definitions

* `ArithmeticFunction.zeta` is the arithmetic function such that `ζ x = 1` for `0 < x`. The notation
  `ζ` for this function is available by opening `ArithmeticFunction.zeta`.
* `ArithmeticFunction.pmul` and `ArithmeticFunction.pdiv` are the pointwise multiplication and
  division on `ArithmeticFunction`s (for which `ζ` is the identity). These are not the same as
  the multiplication instance defined by Dirichlet convolution.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann `ζ`. -/
def zeta : ArithmeticFunction ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩

@[inherit_doc]
scoped[ArithmeticFunction.zeta] notation "ζ" => ArithmeticFunction.zeta

open scoped zeta

section Zeta

@[simp]
theorem zeta_apply {x : ℕ} : ζ x = if x = 0 then 0 else 1 :=
  rfl

theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 :=
  if_neg h

theorem zeta_eq_zero {x : ℕ} : ζ x = 0 ↔ x = 0 := by simp [zeta]

theorem zeta_pos {x : ℕ} : 0 < ζ x ↔ 0 < x := by simp [pos_iff_ne_zero]

theorem coe_zeta_smul_apply {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    ((↑ζ : ArithmeticFunction R) • f) x = ∑ i ∈ divisors x, f i := by
  rw [smul_apply]
  trans ∑ i ∈ divisorsAntidiagonal x, f i.snd
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
  · rw [← map_div_left_divisors, sum_map, Function.Embedding.coeFn_mk]

/-- `@[simp]`-normal form of `coe_zeta_smul_apply`. -/
@[simp]
theorem sum_divisorsAntidiagonal_eq_sum_divisors {M} [Semiring R] [AddCommMonoid M] [MulAction R M]
    {f : ArithmeticFunction M} {x : ℕ} :
    (∑ x ∈ x.divisorsAntidiagonal, if x.1 = 0 then (0 : R) • f x.2 else f x.2) =
      ∑ i ∈ divisors x, f i := by
  simp [← coe_zeta_smul_apply (R := R)]

theorem coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (ζ * f) x = ∑ i ∈ divisors x, f i :=
  coe_zeta_smul_apply

theorem coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} :
    (f * ζ) x = ∑ i ∈ divisors x, f i := by
  rw [mul_apply]
  trans ∑ i ∈ divisorsAntidiagonal x, f i.1
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [natCoe_apply, zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one]
  · rw [← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]

theorem coe_zeta_mul_comm [Semiring R] {f : ArithmeticFunction R} : ζ * f = f * ζ := by
  ext x
  rw [coe_zeta_mul_apply, coe_mul_zeta_apply]

theorem zeta_mul_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (ζ * f) x = ∑ i ∈ divisors x, f i := by
  rw [← natCoe_nat ζ, coe_zeta_mul_apply]

theorem mul_zeta_apply {f : ArithmeticFunction ℕ} {x : ℕ} : (f * ζ) x = ∑ i ∈ divisors x, f i := by
  rw [← natCoe_nat ζ, coe_mul_zeta_apply]

theorem zeta_mul_comm {f : ArithmeticFunction ℕ} : ζ * f = f * ζ := by
  rw [← natCoe_nat ζ, coe_zeta_mul_comm]

end Zeta

section Pmul

/-- This is the pointwise product of `ArithmeticFunction`s. -/
def pmul [MulZeroClass R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun x => f x * g x, by simp⟩

@[simp]
theorem pmul_apply [MulZeroClass R] {f g : ArithmeticFunction R} {x : ℕ} : f.pmul g x = f x * g x :=
  rfl

theorem pmul_comm [CommMonoidWithZero R] (f g : ArithmeticFunction R) : f.pmul g = g.pmul f := by
  ext
  simp [mul_comm]

lemma pmul_assoc [SemigroupWithZero R] (f₁ f₂ f₃ : ArithmeticFunction R) :
    pmul (pmul f₁ f₂) f₃ = pmul f₁ (pmul f₂ f₃) := by
  ext
  simp only [pmul_apply, mul_assoc]

section NonAssocSemiring

variable [NonAssocSemiring R]

@[simp]
theorem pmul_zeta (f : ArithmeticFunction R) : f.pmul ↑ζ = f := by
  ext x
  cases x <;> simp

@[simp]
theorem zeta_pmul (f : ArithmeticFunction R) : (ζ : ArithmeticFunction R).pmul f = f := by
  ext x
  cases x <;> simp

end NonAssocSemiring

variable [Semiring R]

open scoped zeta

/-- This is the pointwise power of `ArithmeticFunction`s. -/
def ppow (f : ArithmeticFunction R) (k : ℕ) : ArithmeticFunction R :=
  if h0 : k = 0 then ζ else ⟨fun x ↦ f x ^ k, by simp_rw [map_zero, zero_pow h0]⟩

@[simp]
theorem ppow_zero {f : ArithmeticFunction R} : f.ppow 0 = ζ := by rw [ppow, dif_pos rfl]

@[simp]
theorem ppow_one {f : ArithmeticFunction R} : f.ppow 1 = f := by
  ext; simp [ppow]

@[simp]
theorem ppow_apply {f : ArithmeticFunction R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = f x ^ k := by
  rw [ppow, dif_neg (Nat.ne_of_gt kpos), coe_mk]

theorem ppow_succ' {f : ArithmeticFunction R} {k : ℕ} : f.ppow (k + 1) = f.pmul (f.ppow k) := by
  ext x
  rw [ppow_apply (succ_pos k), _root_.pow_succ']
  induction k <;> simp

theorem ppow_succ {f : ArithmeticFunction R} {k : ℕ} {kpos : 0 < k} :
    f.ppow (k + 1) = (f.ppow k).pmul f := by
  ext x
  rw [ppow_apply (succ_pos k), _root_.pow_succ]
  induction k <;> simp

end Pmul

section Pdiv

/-- This is the pointwise division of `ArithmeticFunction`s. -/
def pdiv [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n / g n, by simp only [map_zero, div_zero]⟩

@[simp]
theorem pdiv_apply [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) :
    pdiv f g n = f n / g n := rfl

/-- This result only holds for `DivisionSemiring`s instead of `GroupWithZero`s because zeta takes
values in ℕ, and hence the coercion requires an `AddMonoidWithOne`. TODO: Generalise zeta -/
@[simp]
theorem pdiv_zeta [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f zeta = f := by
  ext n
  cases n <;> simp

end Pdiv

@[arith_mult]
theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

namespace IsMultiplicative

@[arith_mult]
theorem pmul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f.pmul g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
    ring⟩

@[arith_mult]
theorem pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) : IsMultiplicative (pdiv f g) :=
  ⟨by simp [hf, hg], fun cop => by
    simp only [pdiv_apply, map_mul_of_coprime hf cop, map_mul_of_coprime hg cop, div_eq_mul_inv,
      mul_inv]
    apply mul_mul_mul_comm ⟩

@[arith_mult]
theorem ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

end IsMultiplicative

end ArithmeticFunction

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.zeta`. -/
@[positivity ArithmeticFunction.zeta _]
meta def evalArithmeticFunctionZeta : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(ArithmeticFunction.zeta $n) =>
    let rn ← core z p n
    assumeInstancesCommute
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.zeta_pos $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.zeta"

end Mathlib.Meta.Positivity
