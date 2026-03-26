/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Multivariate Laurent polynomials

This file defines `MvLaurentPolynomial σ R`, the type of multivariate Laurent polynomials
with coefficients in a commutative semiring `R` and variables indexed by `σ`.

The exponent vectors live in `σ →₀ ℤ`, so negative exponents are allowed.
The implementation is `AddMonoidAlgebra R (σ →₀ ℤ)`.

## Definitions

Let `R` be a commutative semiring and let `σ` be an arbitrary type.

* `MvLaurentPolynomial σ R` : the type of multivariate Laurent polynomials in variables indexed by
  `σ` and coefficients in `R`
* `MvLaurentPolynomial.monomial d r` : the Laurent monomial with exponent vector `d` and
  coefficient `r`
* `MvLaurentPolynomial.C r` : the constant Laurent polynomial with value `r`
* `MvLaurentPolynomial.X n` : the Laurent monomial corresponding to the variable `n`
* `MvLaurentPolynomial.coeff d p` : the coefficient of the monomial `d` in `p`
* `MvPolynomial.toMvLaurent` : the natural inclusion from multivariate polynomials to
  multivariate Laurent polynomials

-/

@[expose] public section

open Function Finsupp AddMonoidAlgebra

noncomputable section

variable {R : Type*} {S : Type*} {σ : Type*}

/-- Multivariate Laurent polynomials over `R` in variables indexed by `σ`. -/
abbrev MvLaurentPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℤ)

namespace MvLaurentPolynomial

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {p q : MvLaurentPolynomial σ R}

@[ext]
theorem ext {p q : MvLaurentPolynomial σ R} (h : ∀ d, p d = q d) : p = q :=
  Finsupp.ext h

/-- The coefficient of the monomial `d` in the multivariate Laurent polynomial `p`. -/
def coeff (d : σ →₀ ℤ) (p : MvLaurentPolynomial σ R) : R :=
  p d

/-- The finite support of a multivariate Laurent polynomial. -/
def support (p : MvLaurentPolynomial σ R) : Finset (σ →₀ ℤ) :=
  Finsupp.support p

/-- `monomial d r` is the Laurent monomial with coefficient `r` and exponent vector `d`. -/
def monomial (d : σ →₀ ℤ) : R →ₗ[R] MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.lsingle d

theorem one_def : (1 : MvLaurentPolynomial σ R) = monomial 0 1 :=
  rfl

theorem single_eq_monomial (d : σ →₀ ℤ) (r : R) :
    (Finsupp.single d r : MvLaurentPolynomial σ R) = monomial d r :=
  rfl

theorem mul_def : p * q = p.sum fun d r ↦ q.sum fun e s ↦ monomial (d + e) (r * s) :=
  AddMonoidAlgebra.mul_def ..

/-- `C r` is the constant Laurent polynomial with value `r`. -/
def C : R →+* MvLaurentPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

@[simp]
theorem algebraMap_eq : algebraMap R (MvLaurentPolynomial σ R) = C :=
  rfl

variable {R σ}

@[simp]
theorem algebraMap_apply [Algebra R S] (r : R) :
    algebraMap R (MvLaurentPolynomial σ S) r = C (algebraMap R S r) :=
  rfl

/-- `X n` is the Laurent monomial with exponent vector `Finsupp.single n 1`. -/
def X (n : σ) : MvLaurentPolynomial σ R :=
  monomial (Finsupp.single n 1) 1

theorem monomial_left_injective {r : R} (hr : r ≠ 0) :
    Function.Injective fun d : σ →₀ ℤ ↦ monomial d r :=
  Finsupp.single_left_injective hr

@[simp]
theorem monomial_left_inj {d e : σ →₀ ℤ} {r : R} (hr : r ≠ 0) :
    monomial d r = monomial e r ↔ d = e :=
  Finsupp.single_left_inj hr

theorem C_apply (r : R) : (C r : MvLaurentPolynomial σ R) = monomial 0 r :=
  rfl

@[simp]
theorem C_0 : (C (0 : R) : MvLaurentPolynomial σ R) = 0 :=
  map_zero _

@[simp]
theorem C_1 : (C (1 : R) : MvLaurentPolynomial σ R) = 1 :=
  rfl

theorem C_mul_monomial (r s : R) (d : σ →₀ ℤ) :
    C r * monomial d s = monomial d (r * s) := by
  have h := AddMonoidAlgebra.single_mul_single (0 : σ →₀ ℤ) d r s
  rw [zero_add] at h
  rw [C_apply, monomial, monomial]
  exact h

@[simp]
theorem C_add (r s : R) : (C (r + s) : MvLaurentPolynomial σ R) = C r + C s :=
  Finsupp.single_add _ _ _

@[simp]
theorem C_mul (r s : R) : (C (r * s) : MvLaurentPolynomial σ R) = C r * C s := by
  simpa [C_apply] using (C_mul_monomial r s (0 : σ →₀ ℤ)).symm

@[simp]
theorem C_pow (r : R) (n : ℕ) : (C (r ^ n) : MvLaurentPolynomial σ R) = C r ^ n :=
  map_pow _ _ _

theorem C_injective : Function.Injective (C : R → MvLaurentPolynomial σ R) :=
  Finsupp.single_injective _

@[simp]
theorem C_inj (r s : R) : (C r : MvLaurentPolynomial σ R) = C s ↔ r = s :=
  C_injective.eq_iff

@[simp]
theorem C_eq_zero {r : R} : (C r : MvLaurentPolynomial σ R) = 0 ↔ r = 0 :=
  ⟨fun h ↦ C_injective <| by simpa using h, fun h ↦ by simp [h]⟩

theorem C_ne_zero {r : R} : (C r : MvLaurentPolynomial σ R) ≠ 0 ↔ r ≠ 0 :=
  C_eq_zero.ne

theorem C_mul' (r : R) (p : MvLaurentPolynomial σ R) : C r * p = r • p :=
  (Algebra.smul_def r p).symm

theorem smul_eq_C_mul (p : MvLaurentPolynomial σ R) (r : R) : r • p = C r * p :=
  (C_mul' r p).symm

theorem C_eq_smul_one (r : R) :
    (C r : MvLaurentPolynomial σ R) = r • (1 : MvLaurentPolynomial σ R) := by
  rw [← C_mul' r 1, mul_one]

theorem smul_monomial {T : Type*} [SMulZeroClass T R] (t : T) (d : σ →₀ ℤ) (r : R) :
    t • monomial d r = monomial d (t • r) :=
  Finsupp.smul_single _ _ _

theorem X_injective [Nontrivial R] : Function.Injective (X : σ → MvLaurentPolynomial σ R) :=
  (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]
theorem X_inj [Nontrivial R] (m n : σ) : X m = (X n : MvLaurentPolynomial σ R) ↔ m = n :=
  X_injective.eq_iff

theorem monomial_pow (d : σ →₀ ℤ) (r : R) (n : ℕ) :
    monomial d r ^ n = monomial (n • d) (r ^ n) :=
  AddMonoidAlgebra.single_pow ..

theorem X_pow_eq_monomial (n : σ) (e : ℕ) :
    X n ^ e = monomial (Finsupp.single n (e : ℤ)) (1 : R) := by
  simp [X, monomial_pow]

@[simp]
theorem monomial_mul {d e : σ →₀ ℤ} {r s : R} :
    monomial d r * monomial e s = monomial (d + e) (r * s) :=
  AddMonoidAlgebra.single_mul_single ..

theorem monomial_add_single (d : σ →₀ ℤ) (n : σ) (e : ℕ) (r : R) :
    monomial (d + Finsupp.single n (e : ℤ)) r = monomial d r * X n ^ e := by
  rw [X_pow_eq_monomial, monomial_mul, mul_one]

theorem monomial_single_add (d : σ →₀ ℤ) (n : σ) (e : ℕ) (r : R) :
    monomial (Finsupp.single n (e : ℤ) + d) r = X n ^ e * monomial d r := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

theorem C_mul_X_pow_eq_monomial (n : σ) (r : R) (e : ℕ) :
    C r * X n ^ e = monomial (Finsupp.single n (e : ℤ)) r := by
  rw [← zero_add (Finsupp.single n (e : ℤ)), monomial_add_single, C_apply]

theorem C_mul_X_eq_monomial (n : σ) (r : R) :
    C r * X n = monomial (Finsupp.single n 1) r := by
  simpa using C_mul_X_pow_eq_monomial n r 1

@[simp]
theorem monomial_zero {d : σ →₀ ℤ} : monomial d (0 : R) = 0 :=
  Finsupp.single_zero _

@[simp]
theorem monomial_zero' : (monomial (0 : σ →₀ ℤ) : R → MvLaurentPolynomial σ R) = C :=
  rfl

@[simp]
theorem monomial_eq_zero {d : σ →₀ ℤ} {r : R} : monomial d r = 0 ↔ r = 0 :=
  Finsupp.single_eq_zero

theorem isUnit_monomial (d : σ →₀ ℤ) : IsUnit (monomial d (1 : R) : MvLaurentPolynomial σ R) :=
  ⟨⟨monomial d 1, monomial (-d) 1, by simp, by simp⟩, rfl⟩

@[simp]
theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] {d : σ →₀ ℤ} {r : R}
    {f : (σ →₀ ℤ) → R → A} (h0 : f d 0 = 0) :
    sum (monomial d r) f = f d r :=
  Finsupp.sum_single_index h0

@[simp]
theorem sum_C {A : Type*} [AddCommMonoid A] {f : (σ →₀ ℤ) → R → A} (r : R) (h0 : f 0 0 = 0) :
    sum (C r) f = f 0 r :=
  sum_monomial_eq h0

theorem support_monomial {d : σ →₀ ℤ} {r : R} [Decidable (r = 0)] :
    (monomial d r : MvLaurentPolynomial σ R).support = if r = 0 then ∅ else {d} := by
  by_cases hr : r = 0
  · simp [support, monomial, hr]
  · simpa [support, monomial, hr] using (Finsupp.support_single_ne_zero d hr)

theorem support_monomial_subset (d : σ →₀ ℤ) (r : R) :
    (monomial d r : MvLaurentPolynomial σ R).support ⊆ {d} := by
  by_cases hr : r = 0
  · subst r
    intro e he
    have h0 : coeff e (0 : MvLaurentPolynomial σ R) ≠ 0 := by
      simpa [support, coeff, monomial_zero] using he
    exact (h0 rfl).elim
  · classical
    simp [support_monomial, hr]

@[simp]
theorem coeff_zero (d : σ →₀ ℤ) : coeff d (0 : MvLaurentPolynomial σ R) = 0 :=
  rfl

@[simp]
theorem coeff_monomial (d e : σ →₀ ℤ) [Decidable (e = d)] (r : R) :
    coeff d (monomial e r : MvLaurentPolynomial σ R) = if e = d then r else 0 := by
  rw [coeff, monomial, AddMonoidAlgebra.lsingle_apply, Finsupp.single_apply]

@[simp]
theorem coeff_C (d : σ →₀ ℤ) [Decidable (0 = d)] (r : R) :
    coeff d (C r : MvLaurentPolynomial σ R) = if 0 = d then r else 0 := by
  rw [C_apply, coeff_monomial]

theorem coeff_X' (n : σ) (d : σ →₀ ℤ) [Decidable (Finsupp.single n 1 = d)] :
    coeff d (X n : MvLaurentPolynomial σ R) = if Finsupp.single n 1 = d then 1 else 0 := by
  rw [X, coeff_monomial]

@[simp]
theorem coeff_X (n : σ) :
    coeff (Finsupp.single n 1) (X n : MvLaurentPolynomial σ R) = 1 := by
  classical
  simp [coeff_X']

@[simp]
theorem coeff_mul_monomial (m : σ →₀ ℤ) (s : σ →₀ ℤ) (r : R) (p : MvLaurentPolynomial σ R) :
    coeff (m + s) (p * monomial s r) = coeff m p * r :=
  AddMonoidAlgebra.mul_single_apply_aux fun _ _ ↦ add_left_inj _

@[simp]
theorem coeff_monomial_mul (m : σ →₀ ℤ) (s : σ →₀ ℤ) (r : R) (p : MvLaurentPolynomial σ R) :
    coeff (s + m) (monomial s r * p) = r * coeff m p :=
  AddMonoidAlgebra.single_mul_apply_aux fun _ _ ↦ add_right_inj _

theorem coeff_mul_monomial' (m : σ →₀ ℤ) (s : σ →₀ ℤ) (r : R) (p : MvLaurentPolynomial σ R) :
    coeff m (p * monomial s r) = coeff (m - s) p * r := by
  simpa [sub_eq_add_neg, add_assoc] using coeff_mul_monomial (m - s) s r p

theorem coeff_monomial_mul' (m : σ →₀ ℤ) (s : σ →₀ ℤ) (r : R) (p : MvLaurentPolynomial σ R) :
    coeff m (monomial s r * p) = r * coeff (m - s) p := by
  simpa [sub_eq_add_neg, add_assoc] using coeff_monomial_mul (m - s) s r p

@[simp]
theorem mem_support_iff {p : MvLaurentPolynomial σ R} {d : σ →₀ ℤ} :
    d ∈ p.support ↔ p.coeff d ≠ 0 := by
  simp [support, coeff]

theorem notMem_support_iff {p : MvLaurentPolynomial σ R} {d : σ →₀ ℤ} :
    d ∉ p.support ↔ p.coeff d = 0 := by
  simp [support, coeff]

@[simp]
theorem support_zero : (0 : MvLaurentPolynomial σ R).support = ∅ :=
  rfl

@[simp]
theorem support_eq_empty {p : MvLaurentPolynomial σ R} : p.support = ∅ ↔ p = 0 :=
  Finsupp.support_eq_empty

@[simp]
theorem support_X [Nontrivial R] (n : σ) :
    (X n : MvLaurentPolynomial σ R).support = {Finsupp.single n 1} :=
  Finsupp.support_single_ne_zero _ one_ne_zero

theorem eq_zero_iff {p : MvLaurentPolynomial σ R} : p = 0 ↔ ∀ d, coeff d p = 0 := by
  constructor
  · intro hp d
    subst hp
    exact coeff_zero d
  · intro hp
    ext d
    simpa [coeff] using hp d

theorem ne_zero_iff {p : MvLaurentPolynomial σ R} : p ≠ 0 ↔ ∃ d, coeff d p ≠ 0 := by
  rw [Ne, eq_zero_iff]
  push_neg
  rfl

@[simp]
theorem support_nonempty {p : MvLaurentPolynomial σ R} : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]

theorem exists_coeff_ne_zero {p : MvLaurentPolynomial σ R} (hp : p ≠ 0) :
    ∃ d, coeff d p ≠ 0 :=
  ne_zero_iff.mp hp

@[simp]
theorem X_ne_zero [Nontrivial R] (n : σ) :
    X n ≠ (0 : MvLaurentPolynomial σ R) := by
  rw [ne_zero_iff]
  exact ⟨Finsupp.single n 1, by simp⟩

theorem sum_def {A : Type*} [AddCommMonoid A] {p : MvLaurentPolynomial σ R}
    {f : (σ →₀ ℤ) → R → A} :
    p.sum f = ∑ d ∈ p.support, f d (p.coeff d) := by
  simp [support, coeff, Finsupp.sum]

section AsSum

@[simp]
theorem support_sum_monomial_coeff (p : MvLaurentPolynomial σ R) :
    (∑ d ∈ p.support, monomial d (coeff d p)) = p :=
  Finsupp.sum_single p

theorem as_sum (p : MvLaurentPolynomial σ R) :
    p = ∑ d ∈ p.support, monomial d (coeff d p) :=
  (support_sum_monomial_coeff p).symm

end AsSum

/-- To prove something about multivariate Laurent polynomials, it suffices to prove it for
monomials and to show that it is preserved by addition. -/
@[elab_as_elim]
theorem induction_on' {P : MvLaurentPolynomial σ R → Prop} (p : MvLaurentPolynomial σ R)
    (monomial : ∀ (d : σ →₀ ℤ) (r : R), P (MvLaurentPolynomial.monomial d r))
    (add : ∀ p q : MvLaurentPolynomial σ R, P p → P q → P (p + q)) : P p :=
  Finsupp.induction p
    (suffices P (MvLaurentPolynomial.monomial 0 0) by
      rwa [monomial_zero] at this
    show P (MvLaurentPolynomial.monomial 0 0) from monomial 0 0)
    fun _ _ _ _ha _hb hp ↦ add _ _ (monomial _ _) hp

end CommSemiring

end MvLaurentPolynomial

namespace MvPolynomial

section CommSemiring

variable [CommSemiring R]

/-- The natural inclusion from multivariate polynomials to multivariate Laurent polynomials. -/
def toMvLaurent : MvPolynomial σ R →+* MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.mapDomainRingHom R <| Finsupp.mapRange.addMonoidHom (Int.ofNatHom : ℕ →+ ℤ)

/-- The natural inclusion from multivariate polynomials to multivariate Laurent polynomials as an
`R`-algebra homomorphism. -/
def toMvLaurentAlg : MvPolynomial σ R →ₐ[R] MvLaurentPolynomial σ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R <| Finsupp.mapRange.addMonoidHom (Int.ofNatHom : ℕ →+ ℤ)

@[simp]
theorem coe_toMvLaurentAlg :
    ((toMvLaurentAlg : MvPolynomial σ R →ₐ[R] MvLaurentPolynomial σ R) :
      MvPolynomial σ R → MvLaurentPolynomial σ R) = toMvLaurent :=
  rfl

theorem toMvLaurentAlg_apply (p : MvPolynomial σ R) : toMvLaurentAlg p = toMvLaurent p :=
  rfl

@[simp]
theorem toMvLaurent_monomial (d : σ →₀ ℕ) (r : R) :
    toMvLaurent (monomial d r) = MvLaurentPolynomial.monomial (d.mapRange Int.ofNat (by simp)) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp]
theorem toMvLaurent_C (r : R) :
    toMvLaurent (C r : MvPolynomial σ R) = MvLaurentPolynomial.C r := by
  change
    AddMonoidAlgebra.mapDomain (Finsupp.mapRange.addMonoidHom (Int.ofNatHom : ℕ →+ ℤ))
      (Finsupp.single 0 r) = MvLaurentPolynomial.C r
  rw [AddMonoidAlgebra.mapDomain_single]
  simp [MvLaurentPolynomial.C_apply, MvLaurentPolynomial.monomial]

@[simp]
theorem toMvLaurent_X (n : σ) :
    toMvLaurent (X n : MvPolynomial σ R) = MvLaurentPolynomial.X n := by
  simp [MvPolynomial.X, MvLaurentPolynomial.X, toMvLaurent_monomial]

theorem toMvLaurent_injective :
    Function.Injective (toMvLaurent : MvPolynomial σ R →+* MvLaurentPolynomial σ R) :=
  AddMonoidAlgebra.mapDomain_injective
    (Finsupp.mapRange_injective Int.ofNat (by simp) Int.ofNat_injective)

theorem toMvLaurent_inj (p q : MvPolynomial σ R) : toMvLaurent p = toMvLaurent q ↔ p = q :=
  toMvLaurent_injective.eq_iff

theorem toMvLaurent_eq_zero {p : MvPolynomial σ R} : toMvLaurent p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ toMvLaurent_injective

theorem toMvLaurent_ne_zero {p : MvPolynomial σ R} : toMvLaurent p ≠ 0 ↔ p ≠ 0 :=
  map_ne_zero_iff _ toMvLaurent_injective

end CommSemiring

end MvPolynomial

namespace MvLaurentPolynomial

section CommSemiring

variable [CommSemiring R]

instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvLaurentPolynomial σ R) where
  __ := MvPolynomial.toMvLaurent.toAlgebra

@[simp]
theorem algebraMap_eq_toMvLaurent (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvLaurentPolynomial σ R) p = MvPolynomial.toMvLaurent p :=
  rfl

end CommSemiring

end MvLaurentPolynomial
