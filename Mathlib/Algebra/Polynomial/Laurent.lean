/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Localization.Away.Basic

/-!  # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`. Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`. Thus, negative exponents are allowed. The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials.

## Notation

The symbol `R[T;T⁻¹]` stands for `LaurentPolynomial R`. We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `AddMonoidAlgebra R ℤ`.
Thus, they are essentially `Finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `Polynomial`, that instead shields away
the implementation via `Finsupp`s. It is closer to the original definition of polynomials.

As a consequence, `LaurentPolynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `Finsupp` implementation of `R[X]` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed. Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

## Future work

Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- A "better" definition of `trunc` would be as an `R`-linear map. This works:
-- `--  def trunc : R[T;T⁻¹] →[R] R[X] := --    refine (?_ : R[ℕ] →[R] R[X]).comp ?_ --    · exact ⟨(toFinsuppIso R).symm, by simp⟩ --    · refine ⟨fun r ↦ comapDomain _ r --        (Set.injOn_of_injective (fun _ _ ↦ Int.ofNat.inj) _), ?_⟩ --      exact fun r f ↦ comapDomain_smul .. -- `
-- but it would make sense to bundle the maps better, for a smoother user experience.
-- I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
-- this stage of the Laurent process!
-- This would likely involve adding a `comapDomain` analogue of
-- `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
-- `Polynomial.toFinsuppIso`.
-- Add `degree, intDegree, intTrailingDegree, leadingCoeff, trailingCoeff,...`.
-/

@[expose] public section


open Polynomial Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R S : Type*}

/-- The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R ℤ

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

open LaurentPolynomial

@[ext]
theorem LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : ∀ a, p a = q a) : p = q :=
  Finsupp.ext h

/-- The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurent [Semiring R] : R[X] →+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R).toRingHom

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
theorem Polynomial.toLaurent_apply [Semiring R] (p : R[X]) :
    toLaurent p = p.toFinsupp.mapDomain (↑) :=
  rfl

/-- The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurentAlg [CommSemiring R] : R[X] →ₐ[R] R[T;T⁻¹] :=
  (mapDomainAlgHom R R Int.ofNatHom).comp (toFinsuppIsoAlg R).toAlgHom

@[simp] lemma Polynomial.coe_toLaurentAlg [CommSemiring R] :
    (toLaurentAlg : R[X] → R[T;T⁻¹]) = toLaurent :=
  rfl

theorem Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : toLaurentAlg f = toLaurent f :=
  rfl

namespace LaurentPolynomial

section Semiring

variable [Semiring R]

theorem single_zero_one_eq_one : (.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) :=
  rfl

/-!  ### The functions `C` and `T`. -/

/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
  singleZeroRingHom

theorem algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = C (algebraMap R A r) :=
  rfl

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R R[T;T⁻¹] r :=
  rfl

theorem single_eq_C (r : R) : .single 0 r = C r := rfl

@[simp] lemma C_apply (t : R) (n : ℤ) : C t n = if n = 0 then t else 0 := by
  rw [← single_eq_C, Finsupp.single_apply]; aesop

/-- The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`. Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
def T (n : ℤ) : R[T;T⁻¹] :=
  .single n 1

@[simp] lemma T_apply (m n : ℤ) : (T n : R[T;T⁻¹]) m = if n = m then 1 else 0 :=
  Finsupp.single_apply

@[simp]
theorem T_zero : (T 0 : R[T;T⁻¹]) = 1 :=
  rfl

theorem T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n := by
  simp [T, single_mul_single]

theorem T_sub (m n : ℤ) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n) := by rw [← T_add, sub_eq_add_neg]

@[simp]
theorem T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) := by
  rw [T, T, single_pow, one_pow, nsmul_eq_mul]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * T m * T n = f * T (m + n) := by
  simp [← T_add, mul_assoc]

@[simp]
theorem single_eq_C_mul_T (r : R) (n : ℤ) : .single n r = C r * T n := by
  simp [C, T, single_mul_single]

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
theorem _root_.Polynomial.toLaurent_C_mul_T (n : ℕ) (r : R) :
    (toLaurent (Polynomial.monomial n r) : R[T;T⁻¹]) = C r * T n := by simp [toLaurent]

@[simp]
theorem _root_.Polynomial.toLaurent_C (r : R) : toLaurent (Polynomial.C r) = C r := by
  convert Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, T_zero, mul_one]

@[simp]
theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ Polynomial.C = C :=
  funext Polynomial.toLaurent_C

@[simp]
theorem _root_.Polynomial.toLaurent_X : (toLaurent Polynomial.X : R[T;T⁻¹]) = T 1 := by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

@[simp]
theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) 1 = 1 :=
  map_one Polynomial.toLaurent

@[simp]
theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : R[X]) :
    toLaurent (Polynomial.C r * f) = C r * toLaurent f := by
  simp only [map_mul, Polynomial.toLaurent_C]

@[simp]
theorem _root_.Polynomial.toLaurent_X_pow (n : ℕ) : toLaurent (X ^ n : R[X]) = T n := by
  simp only [map_pow, Polynomial.toLaurent_X, T_pow, mul_one]

theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : ℕ) (r : R) :
    toLaurent (Polynomial.C r * X ^ n) = C r * T n := by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

instance invertibleT (n : ℤ) : Invertible (T n : R[T;T⁻¹]) where
  invOf := T (-n)
  invOf_mul_self := by rw [← T_add, neg_add_cancel, T_zero]
  mul_invOf_self := by rw [← T_add, add_neg_cancel, T_zero]

@[simp]
theorem invOf_T (n : ℤ) : ⅟(T n : R[T;T⁻¹]) = T (-n) :=
  rfl

theorem isUnit_T (n : ℤ) : IsUnit (T n : R[T;T⁻¹]) :=
  isUnit_of_invertible _

set_option backward.isDefEq.respectTransparency false in
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
  have B : ∀ s : Finset ℤ, M (s.sum fun n : ℤ => C (p n) * T n) := by
    apply Finset.induction
    · convert h_C 0
      simp only [Finset.sum_empty, map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert B p.support
  ext a
  simp_rw [← single_eq_C_mul_T]
  rw [Finset.sum_apply', Finset.sum_eq_single a, single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same, notMem_support_iff.mp ha]

/-- To prove something about Laurent polynomials, it suffices to show that

* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {motive : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (C_mul_T : ∀ (n : ℤ) (a : R), motive (C a * T n)) : motive p := by
  refine p.induction_on (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert C_mul_T 0 a
  exact (mul_one _).symm

theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (T n) f :=
  f.induction_on' (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      simp [add_comm]

@[simp]
theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : T n * f = f * T n :=
  (commute_T n f).eq

set_option backward.isDefEq.respectTransparency false in
theorem smul_eq_C_mul (r : R) (f : R[T;T⁻¹]) : r • f = C r * f := by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add, mul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← smul_mul_assoc, mul_left_inj_of_invertible, ← map_mul, ← single_eq_C,
      Finsupp.smul_single']
    rfl

/-- `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`. The terms of negative degree of `f` "vanish".
`trunc` is a left-inverse to `Polynomial.toLaurent`. -/
def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comapDomain.addMonoidHom fun _ _ => Int.ofNat.inj

@[simp]
theorem trunc_C_mul_T (n : ℤ) (r : R) : trunc (C r * T n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  apply (toFinsuppIso R).injective
  simp only [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, Int.ofNat_eq_natCast,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  -- We need `erw` to see through the identification of `Finsupp` with `LaurentSeries`.
  erw [comapDomain.addMonoidHom_apply Int.ofNat_injective]
  split_ifs with n0
  · rw [toFinsupp_monomial]
    lift n to ℕ using n0
    apply comapDomain_single
  · rw [toFinsupp_inj]
    ext a
    have : a ≠ n := by lia
    simp only [coeff_ofFinsupp, comapDomain_apply, Int.ofNat_eq_natCast, coeff_zero,
      single_eq_of_ne this]

@[simp]
theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine fun f => f.induction_on' ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

@[simp]
theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : trunc (toLaurent f) = f :=
  leftInverse_trunc_toLaurent _

theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) :=
  leftInverse_trunc_toLaurent.injective

@[simp]
theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g :=
  ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩

theorem _root_.Polynomial.toLaurent_ne_zero {f : R[X]} : toLaurent f ≠ 0 ↔ f ≠ 0 :=
  map_ne_zero_iff _ Polynomial.toLaurent_injective

@[simp]
theorem _root_.Polynomial.toLaurent_eq_zero {f : R[X]} : toLaurent f = 0 ↔ f = 0 :=
  map_eq_zero_iff _ Polynomial.toLaurent_injective

theorem exists_T_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), toLaurent f' = f * T n := by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, mul_T_assoc,
        neg_add_cancel, T_zero, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_elim]
theorem induction_on_mul_T {motive : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
    (mul_T : ∀ (f : R[X]) (n : ℕ), motive (toLaurent f * T (-n))) : motive f := by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f, ← T_zero, ← Nat.cast_zero, ← Nat.sub_self n, Nat.cast_sub rfl.le, T_sub,
    ← mul_assoc, ← hf]
  exact mul_T ..

/-- Suppose that `Q` is a statement about Laurent polynomials such that

* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;
  it follow that `Q` is true on all Laurent polynomials. -/
theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
    (Qf : ∀ f : R[X], Q (toLaurent f)) (QT : ∀ f, Q (f * T 1) → Q f) : Q f := by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa using hn

section Support

set_option backward.isDefEq.respectTransparency false in
theorem support_C_mul_T (a : R) (n : ℤ) : Finsupp.support (C a * T n) ⊆ {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_subset

set_option backward.isDefEq.respectTransparency false in
theorem support_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    Finsupp.support (C a * T n) = {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_ne_zero _ a0

set_option backward.isDefEq.respectTransparency false in
/-- The support of a polynomial `f` is a finset in `ℕ`. The lemma `toLaurent_support f`
shows that the support of `f.toLaurent` is the same finset, but viewed in `ℤ` under the natural
inclusion `ℕ ↪ ℤ`. -/
theorem toLaurent_support (f : R[X]) : f.toLaurent.support = f.support.map Nat.castEmbedding := by
  generalize hd : f.support = s
  revert f
  refine Finset.induction_on s ?_ ?_ <;> clear s
  · intro f hf
    rw [Finset.map_empty, Finsupp.support_eq_empty, toLaurent_eq_zero]
    exact Polynomial.support_eq_empty.mp hf
  · intro a s as hf f fs
    have : (erase a f).toLaurent.support = s.map Nat.castEmbedding := by
      refine hf (f.erase a) ?_
      simp only [fs, Finset.erase_eq_of_notMem as, Polynomial.support_erase,
        Finset.erase_insert_eq_erase]
    rw [← monomial_add_erase f a, Finset.map_insert, ← this, map_add, Polynomial.toLaurent_C_mul_T,
      support_add_eq, Finset.insert_eq]
    · congr
      exact support_C_mul_T_of_ne_zero (Polynomial.mem_support_iff.mp (by simp [fs])) _
    · rw [this]
      exact Disjoint.mono_left (support_C_mul_T _ _) (by simpa)

end Support

section Degrees

/-- The degree of a Laurent polynomial takes values in `WithBot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its support of `f`,
or `⊥`, if `f = 0`. -/
def degree (f : R[T;T⁻¹]) : WithBot ℤ :=
  f.support.max

@[simp]
theorem degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, degree_zero]⟩
  ext n
  simp only [coe_zero, Pi.zero_apply]
  simp_rw [degree, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne,
    WithBot.coe_ne_bot, imp_false, not_not] at h
  exact h n

section ExactDegrees

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : degree (C a * T n) = n := by
  rw [degree, support_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton

theorem degree_C_mul_T_ite [DecidableEq R] (n : ℤ) (a : R) :
    degree (C a * T n) = if a = 0 then ⊥ else ↑n := by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, degree_zero, degree_C_mul_T, Ne,
      not_false_iff]

@[simp]
theorem degree_T [Nontrivial R] (n : ℤ) : (T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (T n), ← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0)

theorem degree_C {a : R} (a0 : a ≠ 0) : (C a).degree = 0 := by
  rw [← mul_one (C a), ← T_zero]
  exact degree_C_mul_T 0 a a0

theorem degree_C_ite [DecidableEq R] (a : R) : (C a).degree = if a = 0 then ⊥ else 0 := by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne, not_false_iff]

end ExactDegrees

section DegreeBounds

theorem degree_C_mul_T_le (n : ℤ) (a : R) : degree (C a * T n) ≤ n := by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le

theorem degree_T_le (n : ℤ) : (T n : R[T;T⁻¹]).degree ≤ n :=
  (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))

theorem degree_C_le (a : R) : (C a).degree ≤ 0 :=
  (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

end DegreeBounds

end Degrees

instance : Module R[X] R[T;T⁻¹] :=
  Module.compHom _ Polynomial.toLaurent

instance (R : Type*) [Semiring R] : IsScalarTower R[X] R[X] R[T;T⁻¹] where
  smul_assoc x y z := by rw [smul_eq_mul, mul_smul]

end Semiring

section CommSemiring

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

instance algebraPolynomial (R : Type*) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] where
  algebraMap := Polynomial.toLaurent
  commutes' := fun f l => by simp [mul_comm]
  smul_def' := fun _ _ => rfl

theorem algebraMap_X_pow (n : ℕ) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n :=
  Polynomial.toLaurent_X_pow n

@[simp]
theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f :=
  rfl

instance isLocalization : IsLocalization.Away (X : R[X]) R[T;T⁻¹] :=
  { map_units := fun ⟨t, ht⟩ => by
      obtain ⟨n, rfl⟩ := ht
      rw [algebraMap_eq_toLaurent, toLaurent_X_pow]
      exact isUnit_T ↑n
    surj f := by
      induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
      have : X ^ n ∈ Submonoid.powers (X : R[X]) := ⟨n, rfl⟩
      refine ⟨(f, ⟨_, this⟩), ?_⟩
      simp only [algebraMap_eq_toLaurent, toLaurent_X_pow, mul_T_assoc, neg_add_cancel, T_zero,
        mul_one]
    exists_of_eq := fun {f g} => by
      rw [algebraMap_eq_toLaurent, algebraMap_eq_toLaurent, Polynomial.toLaurent_inj]
      rintro rfl
      exact ⟨1, rfl⟩ }

theorem mk'_mul_T (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) * T n =
      toLaurent p := by
  rw [← toLaurent_X_pow, ← algebraMap_eq_toLaurent, IsLocalization.mk'_spec,
    algebraMap_eq_toLaurent]

@[simp]
theorem mk'_eq (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) =
      toLaurent p * T (-n) := by
  rw [← IsUnit.mul_left_inj (isUnit_T n), mul_T_assoc, neg_add_cancel, T_zero, mul_one]
  exact mk'_mul_T p n

theorem mk'_one_X_pow (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X^n, n, rfl⟩ : Submonoid.powers (X : R[X])) = T (-n) := by
  rw [mk'_eq 1 n, toLaurent_one, one_mul]

@[simp]
theorem mk'_one_X :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨X, 1, pow_one X⟩ : Submonoid.powers (X : R[X])) = T (-1) := by
  convert mk'_one_X_pow 1
  exact (pow_one X).symm

/-- Given a ring homomorphism `f : R →+* S` and a unit `x` in `S`, the induced homomorphism
`R[T;T⁻¹] →+* S` sending `T` to `x` and `T⁻¹` to `x⁻¹`. -/
def eval₂ : R[T;T⁻¹] →+* S :=
  IsLocalization.lift (M := Submonoid.powers (X : R[X])) (g := Polynomial.eval₂RingHom f x) <| by
    rintro ⟨y, n, rfl⟩
    simpa only [coe_eval₂RingHom, eval₂_X_pow] using x.isUnit.pow n

@[simp]
theorem eval₂_toLaurent (p : R[X]) : eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p := by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent, IsLocalization.lift_eq, coe_eval₂RingHom]

theorem eval₂_T_n (n : ℕ) : eval₂ f x (T n) = x ^ n := by
  rw [← Polynomial.toLaurent_X_pow, eval₂_toLaurent, eval₂_X_pow]

theorem eval₂_T_neg_n (n : ℕ) : eval₂ f x (T (-n)) = x⁻¹ ^ n := by
  rw [← mk'_one_X_pow]
  unfold eval₂
  rw [IsLocalization.lift_mk'_spec, map_one, coe_eval₂RingHom, eval₂_X_pow, ← mul_pow,
    Units.mul_inv, one_pow]

@[simp]
theorem eval₂_T (n : ℤ) : eval₂ f x (T n) = (x ^ n).val := by
  by_cases! hn : 0 ≤ n
  · lift n to ℕ using hn
    apply eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [eval₂_T_neg_n, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]

@[simp]
theorem eval₂_C (r : R) : eval₂ f x (C r) = f r := by
  rw [← toLaurent_C, eval₂_toLaurent, Polynomial.eval₂_C]

theorem eval₂_C_mul_T_n (r : R) (n : ℕ) : eval₂ f x (C r * T n) = f r * x ^ n := by
  rw [← Polynomial.toLaurent_C_mul_T, eval₂_toLaurent, eval₂_monomial]

theorem eval₂_C_mul_T_neg_n (r : R) (n : ℕ) : eval₂ f x (C r * T (-n)) = f r * x⁻¹ ^ n := by
  rw [map_mul, eval₂_T_neg_n, eval₂_C]

@[simp]
theorem eval₂_C_mul_T (r : R) (n : ℤ) : eval₂ f x (C r * T n) = f r * (x ^ n).val := by
  simp

end CommSemiring

section Inversion

variable {R : Type*} [CommSemiring R]

/-- The map which substitutes `T ↦ T⁻¹` into a Laurent polynomial. -/
def invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] := AddMonoidAlgebra.domCongr R R <| AddEquiv.neg _

@[simp] lemma invert_T (n : ℤ) : invert (T n : R[T;T⁻¹]) = T (-n) :=
  AddMonoidAlgebra.domCongr_single ..

@[simp] lemma invert_apply (f : R[T;T⁻¹]) (n : ℤ) : invert f n = f (-n) := by simp [invert]

@[simp] lemma invert_comp_C : invert ∘ (@C R _) = C := by ext; simp

@[simp] lemma invert_C (t : R) : invert (C t) = C t := by ext; simp

lemma involutive_invert : Involutive (invert (R := R)) := fun _ ↦ by ext; simp

@[simp] lemma invert_symm : (invert (R := R)).symm = invert := rfl

lemma toLaurent_reverse (p : R[X]) :
    toLaurent p.reverse = invert (toLaurent p) * (T p.natDegree) := by
  nontriviality R
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC _ _ _ _ ih => simp [add_mul, ← ih]
  | MX _ hp => simpa [natDegree_mul_X hp]

end Inversion

section Smeval

section SMulWithZero

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

/-- Evaluate a Laurent polynomial at a unit, using scalar multiplication. -/
def smeval : S := Finsupp.sum f fun n r => r • (x ^ n).val

theorem smeval_eq_sum : f.smeval x = Finsupp.sum f fun n r => r • (x ^ n).val := rfl

theorem smeval_congr : f = g → x = y → f.smeval x = g.smeval y := by rintro rfl rfl; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem smeval_zero : (0 : R[T;T⁻¹]).smeval x = (0 : S) := by
  simp only [smeval_eq_sum, Finsupp.sum_zero_index]

theorem smeval_single (n : ℤ) (r : R) : smeval (.single n r) x = r • (x ^ n).val := by
  simp only [smeval_eq_sum]
  rw [Finsupp.sum_single_index (zero_smul R (x ^ n).val)]

@[simp]
theorem smeval_C_mul_T_n (n : ℤ) (r : R) : (C r * T n).smeval x = r • (x ^ n).val := by
  rw [← single_eq_C_mul_T, smeval_single]

@[simp]
theorem smeval_C (r : R) : (C r).smeval x = r • 1 := by
  rw [← single_eq_C, smeval_single x (0 : ℤ) r, zpow_zero, Units.val_one]

end SMulWithZero

section MulActionWithZero

variable [Semiring R] [AddCommMonoid S] [MulActionWithZero R S] [Monoid S] (f g : R[T;T⁻¹])
  (x y : Sˣ)

@[simp]
theorem smeval_T_pow (n : ℤ) (x : Sˣ) : (T n : R[T;T⁻¹]).smeval x = (x ^ n).val := by
  rw [T, smeval_single, one_smul]

@[simp]
theorem smeval_one : (1 : R[T;T⁻¹]).smeval x = 1 := by
  rw [← T_zero, smeval_T_pow 0 x, zpow_zero, Units.val_eq_one]

end MulActionWithZero

section Module

variable [Semiring R] [AddCommMonoid S] [Module R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem smeval_add : (f + g).smeval x = f.smeval x + g.smeval x := by
  simp only [smeval_eq_sum]
  rw [Finsupp.sum_add_index (fun n _ => zero_smul R (x ^ n).val) (fun n _ r r' => add_smul r r' _)]

@[simp]
theorem smeval_C_mul (r : R) : (C r * f).smeval x = r • (f.smeval x) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, smeval_add, smeval_add, smul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← map_mul, smeval_C_mul_T_n, smeval_C_mul_T_n, mul_smul]

variable (R) in
/-- Evaluation as an `R`-linear map. -/
@[simps]
def leval : R[T;T⁻¹] →ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := smeval_add f g x
  map_smul' r f := by simp [smul_eq_C_mul]

end Module

end Smeval

end LaurentPolynomial
