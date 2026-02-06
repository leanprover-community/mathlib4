/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.ArithMult

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions

* `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
* An arithmetic function `f` `IsMultiplicative` when `x.Coprime y → f (x * y) = f x * f y`.
* Multiplication and power instances on `ArithmeticFunction R`, are defined using Dirichlet
  convolution.

Further examples of arithmetic functions, such as the Möbius function `μ`, are available in
other files in the `Mathlib.NumberTheory.ArithmeticFunction` directory.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset

open Nat

variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `ArithmeticFunctions` is by
  Dirichlet convolution. -/
def ArithmeticFunction [Zero R] :=
  ZeroHom ℕ R

instance ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R) :=
  inferInstanceAs (Zero (ZeroHom ℕ R))

instance [Zero R] : Inhabited (ArithmeticFunction R) := inferInstanceAs (Inhabited (ZeroHom ℕ R))

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

instance : FunLike (ArithmeticFunction R) ℕ R :=
  inferInstanceAs (FunLike (ZeroHom ℕ R) ℕ R)

@[simp]
theorem toFun_eq (f : ArithmeticFunction R) : f.toFun = f := rfl

@[simp]
theorem coe_mk (f : ℕ → R) (hf) : @DFunLike.coe (ArithmeticFunction R) _ _ _
    (ZeroHom.mk f hf) = f := rfl

@[simp]
theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
  ZeroHom.map_zero' f

theorem coe_inj {f g : ArithmeticFunction R} : (f : ℕ → R) = g ↔ f = g :=
  DFunLike.coe_fn_eq

@[simp]
theorem zero_apply {x : ℕ} : (0 : ArithmeticFunction R) x = 0 :=
  rfl

@[ext]
theorem ext ⦃f g : ArithmeticFunction R⦄ (h : ∀ x, f x = g x) : f = g :=
  ZeroHom.ext h

section One

variable [One R]

instance one : One (ArithmeticFunction R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
  rfl

@[simp]
theorem one_one : (1 : ArithmeticFunction R) 1 = 1 :=
  rfl

@[simp]
theorem one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : ArithmeticFunction R) x = 0 :=
  if_neg h

end One

end Zero

/-- Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We cannot inline
this in `natCoe` because it gets unfolded too much. -/
@[coe]
def natToArithmeticFunction [AddMonoidWithOne R] :
    (ArithmeticFunction ℕ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction ℕ) (ArithmeticFunction R) :=
  ⟨natToArithmeticFunction⟩

@[simp]
theorem natCoe_nat (f : ArithmeticFunction ℕ) : natToArithmeticFunction f = f :=
  ext fun _ => cast_id _

@[simp]
theorem natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x :=
  rfl

/-- Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We cannot inline
this in `intCoe` because it gets unfolded too much. -/
@[coe]
def ofInt [AddGroupWithOne R] :
    (ArithmeticFunction ℤ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

instance intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction ℤ) (ArithmeticFunction R) :=
  ⟨ofInt⟩

@[simp]
theorem intCoe_int (f : ArithmeticFunction ℤ) : ofInt f = f :=
  ext fun _ => Int.cast_id

@[simp]
theorem intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction ℤ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x := rfl

@[simp]
theorem coe_coe [AddGroupWithOne R] {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℤ) : ArithmeticFunction R) = (f : ArithmeticFunction R) := by
  ext
  simp

@[simp]
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction ℕ) : ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

@[simp]
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction ℤ) :
    ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

section AddMonoid

variable [AddMonoid R]

instance add : Add (ArithmeticFunction R) :=
  ⟨fun f g => ⟨fun n => f n + g n, by simp⟩⟩

@[simp]
theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
  rfl

instance instAddMonoid : AddMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.zero R,
    ArithmeticFunction.add with
    add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
    zero_add := fun _ => ext fun _ => zero_add _
    add_zero := fun _ => ext fun _ => add_zero _
    nsmul := nsmulRec }

end AddMonoid

instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid,
    ArithmeticFunction.one with
    natCast := fun n => ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
    natCast_zero := by ext; simp
    natCast_succ := fun n => by ext x; by_cases h : x = 1 <;> simp [h] }

instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _ }

instance [NegZeroClass R] : Neg (ArithmeticFunction R) where
  neg f := ⟨fun n => -f n, by simp⟩

@[simp]
theorem neg_apply [NegZeroClass R] {f : ArithmeticFunction R} {n : ℕ} : (-f) n = -f n := by
  rfl

instance [AddGroup R] : AddGroup (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoid with
    neg_add_cancel := fun _ => ext fun _ => neg_add_cancel _
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

end SMul

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance [Semiring R] : Mul (ArithmeticFunction R) :=
  ⟨(· • ·)⟩

@[simp]
theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f * g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst * g x.snd :=
  rfl

theorem mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 * g 1 := by simp

@[simp, norm_cast]
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  simp

@[simp, norm_cast]
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  simp

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)

theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
  ext x
  rw [smul_apply]
  by_cases x0 : x = 0
  · simp [x0]
  have h : {(1, x)} ⊆ divisorsAntidiagonal x := by simp [x0]
  rw [← sum_subset h]
  · simp
  intro y ymem ynotMem
  have y1ne : y.fst ≠ 1 := fun con => by simp_all [Prod.ext_iff]
  simp [y1ne]

end Module

section Semiring

variable [Semiring R]

instance instMonoid : Monoid (ArithmeticFunction R) where
  one_mul := one_smul'
  mul_one := fun f => by
    ext x
    rw [mul_apply]
    by_cases x0 : x = 0
    · simp [x0]
    have h : {(x, 1)} ⊆ divisorsAntidiagonal x := by simp [x0]
    rw [← sum_subset h]
    · simp
    intro ⟨y₁, y₂⟩ ymem ynotMem
    have y2ne : y₂ ≠ 1 := by
      intro con
      simp_all
    simp [y2ne]
  mul_assoc := mul_smul'

instance instSemiring : Semiring (ArithmeticFunction R) :=
  { ArithmeticFunction.instAddMonoidWithOne,
    ArithmeticFunction.instMonoid,
    ArithmeticFunction.instAddCommMonoid with
    zero_mul := fun f => by
      ext
      simp
    mul_zero := fun f => by
      ext
      simp
    left_distrib := fun a b c => by
      ext
      simp [← sum_add_distrib, mul_add]
    right_distrib := fun a b c => by
      ext
      simp [← sum_add_distrib, add_mul] }

end Semiring

instance [CommSemiring R] : CommSemiring (ArithmeticFunction R) :=
  { ArithmeticFunction.instSemiring with
    mul_comm := fun f g => by
      ext
      rw [mul_apply, ← map_swap_divisorsAntidiagonal, sum_map]
      simp [mul_comm] }

instance [CommRing R] : CommRing (ArithmeticFunction R) :=
  { ArithmeticFunction.instSemiring with
    neg_add_cancel := neg_add_cancel
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


/-- Multiplicative functions -/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n

namespace IsMultiplicative

section MonoidWithZero

variable [MonoidWithZero R]

@[simp, arith_mult]
theorem map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1 :=
  h.1

@[simp]
theorem map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : ℕ}
    (h : m.gcd n = 1) : f (m * n) = f m * f n :=
  hf.2 h

end MonoidWithZero

open scoped Function in -- required for scoped `on` notation
theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι → ℕ) {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (Coprime on g)) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert _ _ has ih =>
      rw [coe_insert, Set.pairwise_insert_of_symmetric (Coprime.symmetric.comap g)] at hs
      rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1]
      exact Coprime.prod_right fun i hi => hs.2 _ hi (hi.ne_of_notMem has).symm

theorem map_prod_of_prime [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f)
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

theorem map_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f) (l : ℕ)
    (t : Finset ℕ) (ht : t ⊆ l.primeFactors) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

theorem prod_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [← h_mult.map_prod_of_subset_primeFactors l _ Subset.rfl,
    prod_primeFactors_of_squarefree hl]

theorem map_div_of_coprime [GroupWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {l d : ℕ} (hdl : d ∣ l) (hl : (l / d).Coprime d) (hd : f d ≠ 0) :
    f (l / d) = f l / f d := by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right hl, Nat.div_mul_cancel hdl]

@[arith_mult]
theorem natCast {f : ArithmeticFunction ℕ} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
theorem intCast {f : ArithmeticFunction ℤ} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

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
    simp only [mem_divisorsAntidiagonal, mul_eq_zero, Ne]
    constructor
    · ring
    rw [mul_eq_zero] at *
    exact not_or_intro ha hb
  · simp only [Set.InjOn, mem_coe, mem_divisorsAntidiagonal, mem_product, Prod.mk_inj]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hcd h
    ext
    · trans gcd (a1 * a2) (a1 * b1)
      · rw [gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.1, gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,
          mul_one]
    · trans gcd (a1 * a2) (a2 * b2)
      · rw [mul_comm, gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
          mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.2, mul_comm, gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]
    · trans gcd (b1 * b2) (a1 * b1)
      · rw [mul_comm, gcd_mul_right, cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,
          one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.1, mul_comm c1 d1, gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one]
    · trans gcd (b1 * b2) (a2 * b2)
      · rw [gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.2, gcd_mul_right,
          cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
  · simp only [Set.SurjOn, Set.subset_def, mem_coe, mem_divisorsAntidiagonal, mem_product,
      Set.mem_image]
    rintro ⟨b1, b2⟩ h
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
      gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Ne, mul_eq_zero, not_or] at h
      simp [h.2.1, h.2.2]
    rw [mul_comm n m, h.1]
  · simp only [mem_divisorsAntidiagonal, mem_product]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
      hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
    ring

/-- For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) :=
  Nat.multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn

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

/-- Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers -/
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : ℕ, Nat.Prime p → f (p ^ i) = g (p ^ i) := by
  constructor <;> intro h
  · simp [h]
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn, multiplicative_factorization g hg hn]
  exact prod_congr rfl fun p hp ↦ h p _ (prime_of_mem_primeFactors hp)

theorem lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} :
    f (x.lcm y) * f (x.gcd y) = f x * f y := by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y ≠ 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := lcm_ne_zero hx hy
  have hfi_zero : ∀ {i}, f (i ^ 0) = 1 := by
    intro i; rw [pow_zero, hf.1]
  iterate 4 rw [hf.multiplicative_factorization f (by assumption),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hfi_zero)
      (s := (x.primeFactors ∪ y.primeFactors))]
  · rw [← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    rcases Nat.le_or_le (x.factorization p) (y.factorization p) with h | h <;>
      simp only [factorization_lcm hx hy, Finsupp.sup_apply, h, sup_of_le_right,
        sup_of_le_left, inf_of_le_right, factorization_gcd hx hy, Finsupp.inf_apply,
        inf_of_le_left, mul_comm]
  · apply subset_union_right
  · apply subset_union_left
  · rw [factorization_gcd hx hy, Finsupp.support_inf]
    apply inter_subset_union
  · simp [factorization_lcm hx hy]

theorem map_gcd [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} (hf_lcm : f (x.lcm y) ≠ 0) :
    f (x.gcd y) = f x * f y / f (x.lcm y) := by
  rw [← hf.lcm_apply_mul_gcd_apply, mul_div_cancel_left₀ _ hf_lcm]

theorem map_lcm [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} (hf_gcd : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [← hf.lcm_apply_mul_gcd_apply, mul_div_cancel_right₀ _ hf_gcd]

theorem eq_zero_of_squarefree_of_dvd_eq_zero [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {m n : ℕ} (hn : Squarefree n) (hmn : m ∣ n)
    (h_zero : f m = 0) :
    f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [zero_mul, hf.map_mul_of_coprime (coprime_of_squarefree_mul hn), h_zero]

end IsMultiplicative

@[arith_mult]
theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

end ArithmeticFunction
