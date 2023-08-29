/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Inductions
import Mathlib.RingTheory.Localization.Basic

#align_import data.polynomial.laurent from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!  # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`.  Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`.  Thus, negative exponents are allowed.  The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials.

## Notation
The symbol `R[T;T⁻¹]` stands for `LaurentPolynomial R`.  We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `AddMonoidAlgebra R ℤ`.
Thus, they are essentially `Finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `Polynomial`, that instead shields away
the implementation via `Finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `LaurentPolynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `Finsupp` implementation of `R[X]` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

##  Future work
Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- (Riccardo) giving a morphism (as `R`-alg, so in the commutative case)
  from `R[T,T⁻¹]` to `S` is the same as choosing a unit of `S`.
-- A "better" definition of `trunc` would be as an `R`-linear map.  This works:
--  ```
--  def trunc : R[T;T⁻¹] →[R] R[X] :=
--  begin
--    refine (_ : AddMonoidAlgebra R ℕ →[R] R[X]).comp _,
--    { exact ⟨(toFinsuppIso R).symm, by simp⟩ },
--    { refine ⟨λ r, comapDomain _ r (Set.injOn_of_injective (λ a b ab, Int.ofNat.inj ab) _), _⟩,
--      exact λ r f, comapDomain_smul _ _ _ }
--  end
--  ```
--  but it would make sense to bundle the maps better, for a smoother user experience.
--  I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
--  this stage of the Laurent process!
--  This would likely involve adding a `comapDomain` analogue of
--  `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
--  `Polynomial.toFinsuppIso`.
-- Add `degree, int_degree, int_trailing_degree, leading_coeff, trailing_coeff,...`.
-/


open Polynomial BigOperators Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R : Type*}

/-- The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R ℤ
#align laurent_polynomial LaurentPolynomial

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

open LaurentPolynomial

-- Porting note: `ext` no longer applies `Finsupp.ext` automatically
@[ext]
theorem LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : ∀ a, p a = q a) : p = q :=
  Finsupp.ext h

/-- The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurent [Semiring R] : R[X] →+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R)
#align polynomial.to_laurent Polynomial.toLaurent

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
theorem Polynomial.toLaurent_apply [Semiring R] (p : R[X]) :
    toLaurent p = p.toFinsupp.mapDomain (↑) :=
  rfl
#align polynomial.to_laurent_apply Polynomial.toLaurent_apply

/-- The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurentAlg [CommSemiring R] : R[X] →ₐ[R] R[T;T⁻¹] := by
  refine' AlgHom.comp _ (toFinsuppIsoAlg R).toAlgHom
  -- ⊢ AddMonoidAlgebra R ℕ →ₐ[R] R[T;T⁻¹]
  exact mapDomainAlgHom R R Int.ofNatHom
  -- 🎉 no goals
#align polynomial.to_laurent_alg Polynomial.toLaurentAlg

@[simp] lemma Polynomial.coe_toLaurentAlg [CommSemiring R] :
    (toLaurentAlg : R[X] → R[T;T⁻¹]) = toLaurent :=
  rfl

theorem Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : toLaurentAlg f = toLaurent f :=
  rfl
#align polynomial.to_laurent_alg_apply Polynomial.toLaurentAlg_apply

namespace LaurentPolynomial

section Semiring

variable [Semiring R]

theorem single_zero_one_eq_one : (Finsupp.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) :=
  rfl
#align laurent_polynomial.single_zero_one_eq_one LaurentPolynomial.single_zero_one_eq_one

/-!  ### The functions `C` and `T`. -/


/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
  singleZeroRingHom
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.C LaurentPolynomial.C

theorem algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = C (algebraMap R A r) :=
  rfl
#align laurent_polynomial.algebra_map_apply LaurentPolynomial.algebraMap_apply

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R R[T;T⁻¹] r :=
  rfl
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.C_eq_algebra_map LaurentPolynomial.C_eq_algebraMap

theorem single_eq_C (r : R) : Finsupp.single 0 r = C r := rfl
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.single_eq_C LaurentPolynomial.single_eq_C

@[simp] lemma C_apply (t : R) (n : ℤ) : C t n = if n = 0 then t else 0 := by
  rw [← single_eq_C, Finsupp.single_apply]; aesop
  -- ⊢ (if 0 = n then t else 0) = if n = 0 then t else 0
                                            -- 🎉 no goals

/-- The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
def T (n : ℤ) : R[T;T⁻¹] :=
  Finsupp.single n 1
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T LaurentPolynomial.T

@[simp] lemma T_apply (m n : ℤ) : (T n : R[T;T⁻¹]) m = if n = m then 1 else 0 :=
  Finsupp.single_apply

@[simp]
theorem T_zero : (T 0 : R[T;T⁻¹]) = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_zero LaurentPolynomial.T_zero

theorem T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n := by
  -- Porting note: was `convert single_mul_single.symm`
  simp [T, single_mul_single]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_add LaurentPolynomial.T_add

theorem T_sub (m n : ℤ) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n) := by rw [← T_add, sub_eq_add_neg]
                                                                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_sub LaurentPolynomial.T_sub

@[simp]
theorem T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) := by
  rw [T, T, single_pow n, one_pow, nsmul_eq_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_pow LaurentPolynomial.T_pow

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * T m * T n = f * T (m + n) := by
  simp [← T_add, mul_assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.mul_T_assoc LaurentPolynomial.mul_T_assoc

@[simp]
theorem single_eq_C_mul_T (r : R) (n : ℤ) :
    (Finsupp.single n r : R[T;T⁻¹]) = (C r * T n : R[T;T⁻¹]) := by
  -- Porting note: was `convert single_mul_single.symm`
  simp [C, T, single_mul_single]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.single_eq_C_mul_T LaurentPolynomial.single_eq_C_mul_T

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
theorem _root_.Polynomial.toLaurent_C_mul_T (n : ℕ) (r : R) :
    (toLaurent (Polynomial.monomial n r) : R[T;T⁻¹]) = C r * T n :=
  show Finsupp.mapDomain (↑) (monomial n r).toFinsupp = (C r * T n : R[T;T⁻¹]) by
    rw [toFinsupp_monomial, Finsupp.mapDomain_single, single_eq_C_mul_T]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_C_mul_T Polynomial.toLaurent_C_mul_T

@[simp]
theorem _root_.Polynomial.toLaurent_C (r : R) : toLaurent (Polynomial.C r) = C r := by
  convert Polynomial.toLaurent_C_mul_T 0 r
  -- ⊢ ↑C r = ↑C r * T ↑0
  simp only [Int.ofNat_zero, T_zero, mul_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_C Polynomial.toLaurent_C

@[simp]
theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ Polynomial.C = C :=
  funext Polynomial.toLaurent_C

@[simp]
theorem _root_.Polynomial.toLaurent_X : (toLaurent Polynomial.X : R[T;T⁻¹]) = T 1 := by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  -- ⊢ ↑toLaurent X = T 1
  simp [this, Polynomial.toLaurent_C_mul_T]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_X Polynomial.toLaurent_X

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) 1 = 1 :=
  map_one Polynomial.toLaurent
#align polynomial.to_laurent_one Polynomial.toLaurent_one

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : R[X]) :
    toLaurent (Polynomial.C r * f) = C r * toLaurent f := by
  simp only [_root_.map_mul, Polynomial.toLaurent_C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_C_mul_eq Polynomial.toLaurent_C_mul_eq

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_X_pow (n : ℕ) : toLaurent (X ^ n : R[X]) = T n := by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_X_pow Polynomial.toLaurent_X_pow

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : ℕ) (r : R) :
    toLaurent (Polynomial.C r * X ^ n) = C r * T n := by
  simp only [_root_.map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.to_laurent_C_mul_X_pow Polynomial.toLaurent_C_mul_X_pow

instance invertibleT (n : ℤ) : Invertible (T n : R[T;T⁻¹]) where
  invOf := T (-n)
  invOf_mul_self := by rw [← T_add, add_left_neg, T_zero]
                       -- 🎉 no goals
  mul_invOf_self := by rw [← T_add, add_right_neg, T_zero]
                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.invertible_T LaurentPolynomial.invertibleT

@[simp]
theorem invOf_T (n : ℤ) : ⅟ (T n : R[T;T⁻¹]) = T (-n) :=
  rfl
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.inv_of_T LaurentPolynomial.invOf_T

theorem isUnit_T (n : ℤ) : IsUnit (T n : R[T;T⁻¹]) :=
  isUnit_of_invertible _
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.is_unit_T LaurentPolynomial.isUnit_T

@[elab_as_elim]
protected theorem induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_C : ∀ a, M (C a))
    (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_C_mul_T : ∀ (n : ℕ) (a : R), M (C a * T n) → M (C a * T (n + 1)))
    (h_C_mul_T_Z : ∀ (n : ℕ) (a : R), M (C a * T (-n)) → M (C a * T (-n - 1))) : M p := by
  have A : ∀ {n : ℤ} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : ∀ s : Finset ℤ, M (s.sum fun n : ℤ => C (p.toFun n) * T n) := by
    apply Finset.induction
    · convert h_C 0
      simp only [Finset.sum_empty, _root_.map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert B p.support
  -- ⊢ p = ∑ n in p.support, ↑C (toFun p n) * T n
  ext a
  -- ⊢ ↑p a = ↑(∑ n in p.support, ↑C (toFun p n) * T n) a
  simp_rw [← single_eq_C_mul_T]
  -- ⊢ ↑p a = ↑(∑ x in p.support, Finsupp.single x (toFun p x)) a
  -- Porting note: did not make progress in `simp_rw`
  rw [Finset.sum_apply']
  -- ⊢ ↑p a = ∑ k in p.support, ↑(Finsupp.single k (toFun p k)) a
  simp_rw [Finsupp.single_apply, Finset.sum_ite_eq']
  -- ⊢ ↑p a = if a ∈ p.support then toFun p a else 0
  split_ifs with h
  -- ⊢ ↑p a = toFun p a
  · rfl
    -- 🎉 no goals
  · exact Finsupp.not_mem_support_iff.mp h
    -- 🎉 no goals
#align laurent_polynomial.induction_on LaurentPolynomial.induction_on

/-- To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
    (h_add : ∀ p q, M p → M q → M (p + q)) (h_C_mul_T : ∀ (n : ℤ) (a : R), M (C a * T n)) :
    M p := by
  refine' p.induction_on (fun a => _) (fun {p q} => h_add p q) _ _ <;>
      try exact fun n f _ => h_C_mul_T _ f
      -- ⊢ M (↑C a)
      -- 🎉 no goals
      -- 🎉 no goals
  convert h_C_mul_T 0 a
  -- ⊢ ↑C a = ↑C a * T 0
  exact (mul_one _).symm
  -- 🎉 no goals
#align laurent_polynomial.induction_on' LaurentPolynomial.induction_on'

theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (T n) f :=
  f.induction_on' (fun p q Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      -- ⊢ AddMonoidAlgebra.single (n + (0 + m)) (1 * (a * 1)) = AddMonoidAlgebra.singl …
      simp [add_comm]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.commute_T LaurentPolynomial.commute_T

@[simp]
theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : T n * f = f * T n :=
  (commute_T n f).eq
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_mul LaurentPolynomial.T_mul

/-- `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree of `f` "vanish".
`trunc` is a left-inverse to `Polynomial.toLaurent`. -/
def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comapDomain.addMonoidHom fun _ _ => Int.ofNat.inj
#align laurent_polynomial.trunc LaurentPolynomial.trunc

@[simp]
theorem trunc_C_mul_T (n : ℤ) (r : R) : trunc (C r * T n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  -- Porting note: added. Should move elsewhere after the port.
  have : Function.Injective Int.ofNat := fun x y h => Int.ofNat_inj.mp h
  -- ⊢ ↑trunc (↑C r * T n) = if 0 ≤ n then ↑(monomial (Int.toNat n)) r else 0
  apply (toFinsuppIso R).injective
  -- ⊢ ↑(toFinsuppIso R) (↑trunc (↑C r * T n)) = ↑(toFinsuppIso R) (if 0 ≤ n then ↑ …
  rw [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply]
  -- ⊢ ↑(toFinsuppIso R) (↑(RingEquiv.toAddMonoidHom (RingEquiv.symm (toFinsuppIso  …
  -- Porting note: was `rw`
  erw [comapDomain.addMonoidHom_apply this]
  -- ⊢ comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.InjOn Int.ofNat (Int.ofN …
  rw [toFinsuppIso_apply]
  -- ⊢ comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.InjOn Int.ofNat (Int.ofN …
  -- Porting note: rewrote proof below relative to mathlib3.
  by_cases n0 : 0 ≤ n
  -- ⊢ comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.InjOn Int.ofNat (Int.ofN …
  · lift n to ℕ using n0
    -- ⊢ comapDomain Int.ofNat (Finsupp.single (↑n) r) (_ : Set.InjOn Int.ofNat (Int. …
    erw [comapDomain_single]
    -- ⊢ Finsupp.single n r = (if 0 ≤ ↑n then ↑(monomial (Int.toNat ↑n)) r else 0).to …
    simp only [Nat.cast_nonneg, Int.toNat_ofNat, ite_true, toFinsupp_monomial]
    -- 🎉 no goals
  · lift -n to ℕ using (neg_pos.mpr (not_le.mp n0)).le with m
    -- ⊢ comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.InjOn Int.ofNat (Int.ofN …
    rw [toFinsupp_inj, if_neg n0]
    -- ⊢ { toFinsupp := comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.InjOn Int …
    ext a
    -- ⊢ coeff { toFinsupp := comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.Inj …
    have := ((not_le.mp n0).trans_le (Int.ofNat_zero_le a)).ne
    -- ⊢ coeff { toFinsupp := comapDomain Int.ofNat (Finsupp.single n r) (_ : Set.Inj …
    simp only [coeff_ofFinsupp, comapDomain_apply, Int.ofNat_eq_coe, coeff_zero,
      single_eq_of_ne this]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.trunc_C_mul_T LaurentPolynomial.trunc_C_mul_T

@[simp]
theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine' fun f => f.induction_on' _ _
  -- ⊢ ∀ (p q : R[X]), ↑trunc (↑toLaurent p) = p → ↑trunc (↑toLaurent q) = q → ↑tru …
  · intro f g hf hg
    -- ⊢ ↑trunc (↑toLaurent (f + g)) = f + g
    simp only [hf, hg, _root_.map_add]
    -- 🎉 no goals
  · intro n r
    -- ⊢ ↑trunc (↑toLaurent (↑(monomial n) r)) = ↑(monomial n) r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.coe_nat_nonneg, Int.toNat_coe_nat,
      if_true]
#align laurent_polynomial.left_inverse_trunc_to_laurent LaurentPolynomial.leftInverse_trunc_toLaurent

@[simp]
theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : trunc (toLaurent f) = f :=
  leftInverse_trunc_toLaurent _
#align polynomial.trunc_to_laurent Polynomial.trunc_toLaurent

theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) :=
  leftInverse_trunc_toLaurent.injective
#align polynomial.to_laurent_injective Polynomial.toLaurent_injective

@[simp]
theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g :=
  ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩
#align polynomial.to_laurent_inj Polynomial.toLaurent_inj

theorem _root_.Polynomial.toLaurent_ne_zero {f : R[X]} : f ≠ 0 ↔ toLaurent f ≠ 0 :=
  (map_ne_zero_iff _ Polynomial.toLaurent_injective).symm
#align polynomial.to_laurent_ne_zero Polynomial.toLaurent_ne_zero

theorem exists_T_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), toLaurent f' = f * T n := by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  -- ⊢ ∀ (p q : R[T;T⁻¹]), (∃ n f', ↑toLaurent f' = p * T ↑n) → (∃ n f', ↑toLaurent …
                                              -- ⊢ ∀ (p q : R[T;T⁻¹]), (∃ n f', ↑toLaurent f' = p * T ↑n) → (∃ n f', ↑toLaurent …
                                              -- ⊢ ∃ n_1 f', ↑toLaurent f' = ↑C a * T n * T ↑n_1
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    -- ⊢ ∃ n f', ↑toLaurent f' = (f + g) * T ↑n
    refine' ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩
    -- ⊢ ↑toLaurent (fn * X ^ n + gn * X ^ m) = (f + g) * T ↑(m + n)
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.ofNat_add]
  · cases' n with n n
    -- ⊢ ∃ n_1 f', ↑toLaurent f' = ↑C a * T (Int.ofNat n) * T ↑n_1
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
      -- 🎉 no goals
    · refine' ⟨n + 1, Polynomial.C a, _⟩
      -- ⊢ ↑toLaurent (↑Polynomial.C a) = ↑C a * T (Int.negSucc n) * T ↑(n + 1)
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.ofNat_succ, mul_T_assoc, add_left_neg,
        T_zero, mul_one]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.exists_T_pow LaurentPolynomial.exists_T_pow

/-- This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_elim]
theorem induction_on_mul_T {Q : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
    (Qf : ∀ {f : R[X]} {n : ℕ}, Q (toLaurent f * T (-n))) : Q f := by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  -- ⊢ Q f
  rw [← mul_one f, ← T_zero, ← Nat.cast_zero, ← Nat.sub_self n, Nat.cast_sub rfl.le, T_sub,
    ← mul_assoc, ← hf]
  exact Qf
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.induction_on_mul_T LaurentPolynomial.induction_on_mul_T

/-- Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;
it follow that `Q` is true on all Laurent polynomials. -/
theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
    (Qf : ∀ f : R[X], Q (toLaurent f)) (QT : ∀ f, Q (f * T 1) → Q f) : Q f := by
  induction' f using LaurentPolynomial.induction_on_mul_T with f n
  -- ⊢ Q (↑toLaurent f * T (-↑n))
  induction' n with n hn
  -- ⊢ Q (↑toLaurent f * T (-↑Nat.zero))
  · simpa only [Nat.zero_eq, Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
    -- 🎉 no goals
  · convert QT _ _
    -- ⊢ Q (↑toLaurent f * T (-↑(Nat.succ n)) * T 1)
    simpa using hn
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.reduce_to_polynomial_of_mul_T LaurentPolynomial.reduce_to_polynomial_of_mul_T

section Support

theorem support_C_mul_T (a : R) (n : ℤ) : Finsupp.support (C a * T n) ⊆ {n} := by
  -- Porting note: was
  -- simpa only [← single_eq_C_mul_T] using support_single_subset
  rw [← single_eq_C_mul_T]
  -- ⊢ (Finsupp.single n a).support ⊆ {n}
  exact support_single_subset
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.support_C_mul_T LaurentPolynomial.support_C_mul_T

theorem support_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    Finsupp.support (C a * T n) = {n} := by
  rw [← single_eq_C_mul_T]
  -- ⊢ (Finsupp.single n a).support = {n}
  exact support_single_ne_zero _ a0
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.support_C_mul_T_of_ne_zero LaurentPolynomial.support_C_mul_T_of_ne_zero

/-- The support of a polynomial `f` is a finset in `ℕ`.  The lemma `toLaurent_support f`
shows that the support of `f.toLaurent` is the same finset, but viewed in `ℤ` under the natural
inclusion `ℕ ↪ ℤ`. -/
theorem toLaurent_support (f : R[X]) : f.toLaurent.support = f.support.map Nat.castEmbedding := by
  generalize hd : f.support = s
  -- ⊢ (↑toLaurent f).support = Finset.map Nat.castEmbedding s
  revert f
  -- ⊢ ∀ (f : R[X]), Polynomial.support f = s → (↑toLaurent f).support = Finset.map …
  refine' Finset.induction_on s _ _ <;> clear s
  -- ⊢ ∀ (f : R[X]), Polynomial.support f = ∅ → (↑toLaurent f).support = Finset.map …
                                        -- ⊢ ∀ (f : R[X]), Polynomial.support f = ∅ → (↑toLaurent f).support = Finset.map …
                                        -- ⊢ ∀ ⦃a : ℕ⦄ {s : Finset ℕ}, ¬a ∈ s → (∀ (f : R[X]), Polynomial.support f = s → …
  · simp (config := { contextual := true }) only [Polynomial.support_eq_empty, map_zero,
      Finsupp.support_zero, eq_self_iff_true, imp_true_iff, Finset.map_empty,
      Finsupp.support_eq_empty]
  · intro a s as hf f fs
    -- ⊢ (↑toLaurent f).support = Finset.map Nat.castEmbedding (insert a s)
    have : (erase a f).toLaurent.support = s.map Nat.castEmbedding := by
      refine' hf (f.erase a) _
      simp only [fs, Finset.erase_eq_of_not_mem as, Polynomial.support_erase,
        Finset.erase_insert_eq_erase]
    rw [← monomial_add_erase f a, Finset.map_insert, ← this, map_add, Polynomial.toLaurent_C_mul_T,
      support_add_eq, Finset.insert_eq]
    · congr
      -- ⊢ (↑C (coeff f a) * T ↑a).support = {↑Nat.castEmbedding a}
      exact support_C_mul_T_of_ne_zero (Polynomial.mem_support_iff.mp (by simp [fs])) _
      -- 🎉 no goals
    · rw [this]
      -- ⊢ Disjoint (↑C (coeff f a) * T ↑a).support (Finset.map Nat.castEmbedding s)
      exact Disjoint.mono_left (support_C_mul_T _ _) (by simpa)
      -- 🎉 no goals
#align laurent_polynomial.to_laurent_support LaurentPolynomial.toLaurent_support

end Support

section Degrees

/-- The degree of a Laurent polynomial takes values in `WithBot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its support of `f`,
or `⊥`, if `f = 0`. -/
def degree (f : R[T;T⁻¹]) : WithBot ℤ :=
  f.support.max
#align laurent_polynomial.degree LaurentPolynomial.degree

@[simp]
theorem degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ :=
  rfl
#align laurent_polynomial.degree_zero LaurentPolynomial.degree_zero

@[simp]
theorem degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 := by
  refine' ⟨fun h => _, fun h => by rw [h, degree_zero]⟩
  -- ⊢ f = 0
  rw [degree, Finset.max_eq_sup_withBot] at h
  -- ⊢ f = 0
  ext n
  -- ⊢ ↑f n = ↑0 n
  refine' not_not.mp fun f0 => _
  -- ⊢ False
  simp_rw [Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne.def, WithBot.coe_ne_bot] at h
  -- ⊢ False
  exact h n f0
  -- 🎉 no goals
#align laurent_polynomial.degree_eq_bot_iff LaurentPolynomial.degree_eq_bot_iff

section ExactDegrees

open Classical

@[simp]
theorem degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : degree (C a * T n) = n := by
  rw [degree]
  -- ⊢ Finset.max (↑C a * T n).support = ↑n
  -- Porting note: was `convert Finset.max_singleton`
  have : Finsupp.support (C a * T n) = {n} := by
    refine' support_eq_singleton.mpr _
    rw [← single_eq_C_mul_T]
    simp only [single_eq_same, a0, Ne.def, not_false_iff, eq_self_iff_true, and_self_iff]
  rw [this]
  -- ⊢ Finset.max {n} = ↑n
  exact Finset.max_singleton
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T LaurentPolynomial.degree_C_mul_T

theorem degree_C_mul_T_ite (n : ℤ) (a : R) : degree (C a * T n) = ite (a = 0) ⊥ ↑n := by
  split_ifs with h <;>
  -- ⊢ degree (↑C a * T n) = ⊥
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne.def,
      not_false_iff]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T_ite LaurentPolynomial.degree_C_mul_T_ite

@[simp]
theorem degree_T [Nontrivial R] (n : ℤ) : (T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (T n), ← map_one C]
  -- ⊢ degree (↑C 1 * T n) = ↑n
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_T LaurentPolynomial.degree_T

theorem degree_C {a : R} (a0 : a ≠ 0) : (C a).degree = 0 := by
  rw [← mul_one (C a), ← T_zero]
  -- ⊢ degree (↑C a * T 0) = 0
  exact degree_C_mul_T 0 a a0
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C LaurentPolynomial.degree_C

theorem degree_C_ite (a : R) : (C a).degree = ite (a = 0) ⊥ 0 := by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne.def, not_false_iff]
  -- ⊢ degree (↑C a) = ⊥
                       -- 🎉 no goals
                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_ite LaurentPolynomial.degree_C_ite

end ExactDegrees

section DegreeBounds

theorem degree_C_mul_T_le (n : ℤ) (a : R) : degree (C a * T n) ≤ n := by
  by_cases a0 : a = 0
  -- ⊢ degree (↑C a * T n) ≤ ↑n
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
    -- 🎉 no goals
  · exact (degree_C_mul_T n a a0).le
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T_le LaurentPolynomial.degree_C_mul_T_le

theorem degree_T_le (n : ℤ) : (T n : R[T;T⁻¹]).degree ≤ n :=
  (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))
                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_T_le LaurentPolynomial.degree_T_le

theorem degree_C_le (a : R) : (C a).degree ≤ 0 :=
  (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)
                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_le LaurentPolynomial.degree_C_le

end DegreeBounds

end Degrees

instance : Module R[X] R[T;T⁻¹] :=
  Module.compHom _ Polynomial.toLaurent

instance (R : Type*) [Semiring R] : IsScalarTower R[X] R[X] R[T;T⁻¹] where
  smul_assoc x y z := by simp only [(· • ·), SMul.smul, SMul.comp.smul, map_mul, mul_assoc]
                         -- 🎉 no goals

end Semiring

section CommSemiring

variable [CommSemiring R]

instance algebraPolynomial (R : Type*) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] :=
  { Polynomial.toLaurent with
    commutes' := fun f l => by simp [mul_comm]
                               -- 🎉 no goals
    smul_def' := fun f l => rfl }
#align laurent_polynomial.algebra_polynomial LaurentPolynomial.algebraPolynomial

theorem algebraMap_X_pow (n : ℕ) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n :=
  Polynomial.toLaurent_X_pow n
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.algebra_map_X_pow LaurentPolynomial.algebraMap_X_pow

@[simp]
theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f :=
  rfl
#align laurent_polynomial.algebra_map_eq_to_laurent LaurentPolynomial.algebraMap_eq_toLaurent

theorem isLocalization : IsLocalization (Submonoid.closure ({X} : Set R[X])) R[T;T⁻¹] :=
  { map_units' := fun t => by
      cases' t with t ht
      -- ⊢ IsUnit (↑(algebraMap R[X] R[T;T⁻¹]) ↑{ val := t, property := ht })
      rcases Submonoid.mem_closure_singleton.mp ht with ⟨n, rfl⟩
      -- ⊢ IsUnit (↑(algebraMap R[X] R[T;T⁻¹]) ↑{ val := X ^ n, property := ht })
      simp only [isUnit_T n, algebraMap_eq_toLaurent, Polynomial.toLaurent_X_pow]
      -- 🎉 no goals
    surj' := fun f => by
      induction' f using LaurentPolynomial.induction_on_mul_T with f n
      -- ⊢ ∃ x, ↑toLaurent f * T (-↑n) * ↑(algebraMap R[X] R[T;T⁻¹]) ↑x.snd = ↑(algebra …
      have := (Submonoid.closure ({X} : Set R[X])).pow_mem Submonoid.mem_closure_singleton_self n
      -- ⊢ ∃ x, ↑toLaurent f * T (-↑n) * ↑(algebraMap R[X] R[T;T⁻¹]) ↑x.snd = ↑(algebra …
      refine' ⟨(f, ⟨_, this⟩), _⟩
      -- ⊢ ↑toLaurent f * T (-↑n) * ↑(algebraMap R[X] R[T;T⁻¹]) ↑(f, { val := X ^ n, pr …
      simp only [algebraMap_eq_toLaurent, Polynomial.toLaurent_X_pow, mul_T_assoc,
        add_left_neg, T_zero, mul_one]
    eq_iff_exists' := fun {f g} => by
      rw [algebraMap_eq_toLaurent, algebraMap_eq_toLaurent, Polynomial.toLaurent_inj]
      -- ⊢ f = g ↔ ∃ c, ↑c * f = ↑c * g
      refine' ⟨_, _⟩
      -- ⊢ f = g → ∃ c, ↑c * f = ↑c * g
      · rintro rfl
        -- ⊢ ∃ c, ↑c * f = ↑c * f
        exact ⟨1, rfl⟩
        -- 🎉 no goals
      · rintro ⟨⟨h, hX⟩, h⟩
        -- ⊢ f = g
        rcases Submonoid.mem_closure_singleton.mp hX with ⟨n, rfl⟩
        -- ⊢ f = g
        exact (isRegular_X_pow n).left h }
        -- 🎉 no goals
#align laurent_polynomial.is_localization LaurentPolynomial.isLocalization

end CommSemiring

section Inversion

variable {R : Type*} [CommSemiring R]

/-- The map which substitutes `T ↦ T⁻¹` into a Laurent polynomial. -/
def invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] := AddMonoidAlgebra.domCongr R R <| AddEquiv.neg _

@[simp] lemma invert_T (n : ℤ) : invert (T n : R[T;T⁻¹]) = T (-n) :=
  AddMonoidAlgebra.domCongr_single _ _ _ _ _

@[simp] lemma invert_apply (f : R[T;T⁻¹]) (n : ℤ) : invert f n = f (-n) := rfl

@[simp] lemma invert_comp_C : invert ∘ (@C R _) = C := by ext; simp
                                                          -- ⊢ ↑((↑invert ∘ ↑C) x✝) a✝ = ↑(↑C x✝) a✝
                                                               -- 🎉 no goals

@[simp] lemma invert_C (t : R) : invert (C t) = C t := by ext; simp
                                                          -- ⊢ ↑(↑invert (↑C t)) a✝ = ↑(↑C t) a✝
                                                               -- 🎉 no goals

lemma involutive_invert : Involutive (invert (R := R)) := fun _ ↦ by ext; simp
                                                                     -- ⊢ ↑(↑invert (↑invert x✝)) a✝ = ↑x✝ a✝
                                                                          -- 🎉 no goals

@[simp] lemma invert_symm : (invert (R := R)).symm = invert := rfl

lemma toLaurent_reverse (p : R[X]) :
    toLaurent p.reverse = invert (toLaurent p) * (T p.natDegree) := by
  nontriviality R
  -- ⊢ ↑toLaurent (reverse p) = ↑invert (↑toLaurent p) * T ↑(natDegree p)
  induction' p using Polynomial.recOnHorner with p t _ _ ih p hp ih
  · simp
    -- 🎉 no goals
  · simp [add_mul, ← ih]
    -- 🎉 no goals
  · simpa [natDegree_mul_X hp]
    -- 🎉 no goals

end Inversion

end LaurentPolynomial
