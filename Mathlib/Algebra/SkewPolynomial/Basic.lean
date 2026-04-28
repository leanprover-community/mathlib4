/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.SkewMonoidAlgebra.Single
public import Mathlib.Algebra.SkewMonoidAlgebra.Support
/-!
# Univariate skew polynomials

Given a ring `R` and an endomorphism `φ` on `R` the skew polynomials over `R`
are polynomials
$$\sum_{i= 0}^n a_iX^n, n\geq 0, a_i\in R$$
where the addition is the usual addition of polynomials
$$\sum_{i= 0}^n a_iX^n + \sum_{i= 0}^n b_iX^n= \sum_{i= 0}^n (a_i + b_i)X^n.$$
The multiplication, however, is determined by
$$Xa = \varphi (a)X$$
by extending it to all polynomials in the obvious way.

Skew polynomials are represented as `SkewMonoidAlgebra R (Multiplicative ℕ)`,
where `R` is usually at least a Semiring. In this file, we define `SkewPolynomial`
and provide basic instances.

**Note**: To register the endomorphism `φ` see notation below.

## Notation

The endomorphism `φ` is implemented using some action of `Multiplicative ℕ` on `R`.
From this action, `φ` is an `abbrev` denoting $(\text{ofAdd } 1) \cdot a := \varphi(a)$.

Users that want to work with a specific map `φ` should introduce an an action of
`Multiplicative ℕ` on `R`. Specifying that this action is a `MulSemiringAction` amounts
to saying that `φ` is an endomorphism.

Furthermore, with this notation `φ^[n](a) = (ofAdd n) • a`, see `φ_iterate_apply`.

## Main definitions

* `monomial n a` is the skew polynomial `a X ^ n`. Note that `monomial n` is defined as an
  `R`-linear map.
* `C a` is the constant skew polynomial `a`. Note that `C` is defined as a additive homomorphism.
* `CRingHom a` is the constant skew polynomial `a`, as a ring homomorphism. This requires
  to assume `[MulSemiringAction (Multiplicative ℕ) R]`.
* `X` is the skew polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `coeff p n` is the coefficient of `X ^ n` in `p`.
* `p.erase n` is the skew polynomial `p` in which one removes the `c X ^ n` term.
* `p.erase n a` is the skew polynomial obtained by replacing the coefficient of degree `n` by
  a given value `a : R`.  If `a = 0`, this is equal to `p.erase n` If `p.natDegree < n` and `a ≠ 0`,
  this increases the degree of `p` to `n`.

## Implementation notes

The implementation uses `Multiplicative ℕ` instead of `ℕ` as some notion
of `AddSkewMonoidAlgebra` like the current implementation of `Polynomials` in Mathlib.

This decision was made because we use the type class `MulSemiringAction` to specify the properties
the action needs to respect for associativity. There is no version of this in Mathlib that
uses an acting `AddMonoid M` and so we need to use `Multiplicative ℕ` for the action.

For associativity to hold, there should be an instance of
`MulSemiringAction (Multiplicative ℕ) R` present in the context.
For example, in the context of $\mathbb{F}_q$-linear polynomials, this can be the
$q$-th Frobenius endomorphism - so $\varphi(a) = a^q$.

## Reference

The definition is inspired by Chapter 3 of [Papikian2023].

## Tags

Skew Polynomials, Twisted Polynomials.

Note that [ore33] proposes a more general definition of skew polynomial ring, where the
multiplication is determined by  $Xa = \varphi (a)X + δ (a)$, where `ϕ` is as above and
`δ` is a derivation.

-/

@[expose] public section

noncomputable section

open Function Multiplicative SkewMonoidAlgebra

/-- The skew polynomials over `R` is the type of univariate polynomials over `R`
endowed with a skewed convolution product. -/
def SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative ℕ)

namespace SkewPolynomial

variable {R : Type*} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : SkewPolynomial R}

instance : Inhabited (SkewPolynomial R) := SkewMonoidAlgebra.instInhabited

instance : AddCommMonoid (SkewPolynomial R) := SkewMonoidAlgebra.instAddCommMonoid

instance instSemiring [MulSemiringAction (Multiplicative ℕ) R] : Semiring (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSemiring

lemma zero_def : (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative ℕ)) := rfl

variable {S S₁ S₂ : Type*}

instance [Semiring S] [Module S R] : Module S (SkewPolynomial R) :=
  SkewMonoidAlgebra.instModule

instance [Semiring S₁] [Semiring S₂] [Module S₁ R] [Module S₂ R]
    [SMulCommClass S₁ S₂ R] : SMulCommClass S₁ S₂ (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSMulCommClass

instance [SMulZeroClass S R] : SMulZeroClass S (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSMulZeroClass

instance [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ (SkewPolynomial R) :=
  SkewMonoidAlgebra.instIsScalarTower

instance [Subsingleton R] : Unique (SkewPolynomial R) :=
  SkewMonoidAlgebra.instUniqueOfSubsingleton

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support (p : SkewPolynomial R) : Finset ℕ :=
  Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

/-- Though `SkewPolynomial.support` is not defeq to `SkewMonoidAlgebra.support` we can
relate them using the following lemma. -/
lemma support_eq_skewMonoidAlgebra_support (p : SkewPolynomial R) :
    p.support = Finset.map (Multiplicative.toAdd (α := ℕ)) (SkewMonoidAlgebra.support p) := by
  simp only [support]

@[simp] lemma support_zero : (0 : SkewPolynomial R).support = ∅ := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 := by simp [support]

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by simp

lemma support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

/-- `coeff p n` is the coefficient of `X ^ n` in `p`. -/
def coeff (p : SkewPolynomial R) : ℕ → R := fun n ↦ (SkewMonoidAlgebra.coeff p (ofAdd n))

@[simp]
lemma mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  simp [support, coeff]

lemma notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

/-- `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`. -/
def sum {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) : S :=
  SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r)

/-- For a skew polynomial `p`, `p.sum f` can be written in terms of `SkewMonoidAlgebra.sum p`. -/
lemma sum_def' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r) :=
  rfl

lemma sum_def {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) := by
  rw [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  simp only [toFinsupp_apply]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a)
  · intro; aesop (add norm coeff)
  · aesop (add norm coeff)
  · simp [coeff]

lemma sum_sum_index {R' P : Type*} [AddCommMonoid P] [Semiring R']
    {f : SkewPolynomial R} {g : ℕ → R → SkewPolynomial R'} {h : ℕ → R' → P}
    (h_zero : ∀ (a : ℕ), h a 0 = 0)
    (h_add : ∀ (a : ℕ) (b₁ b₂ : R'), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun (a : ℕ) (b : R) => sum (g a b) h := by
  simp only [sum_def', SkewMonoidAlgebra.sum_def]
  erw [SkewMonoidAlgebra.toFinsupp_sum']
  rw [Finsupp.sum_sum_index (fun a ↦ h_zero (toAdd a)) (fun n ↦ h_add (toAdd n))]

@[simp]
lemma sum_zero {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R} :
    (f.sum fun (_ : ℕ) _ => (0 : N)) = 0 :=
  SkewMonoidAlgebra.sum_zero

section Monomial

/-- `monomial s a` is the monomial `a * X ^ s`. -/
def monomial (n : ℕ) : R →ₗ[R] SkewPolynomial R := lsingle (ofAdd n)

lemma monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 := single_zero _

lemma monomial_zero_one [MulSemiringAction (Multiplicative ℕ) R] : monomial (0 : ℕ) (1 : R) = 1 :=
  rfl

lemma monomial_def (n : ℕ) (a : R) : monomial n a = single (ofAdd n) a := rfl

lemma monomial_add (n : ℕ) (r s : R) :
    monomial n (r + s) = monomial n r + monomial n s :=
  single_add ..

lemma smul_monomial {S} [Semiring S] [Module S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  smul_single ..

lemma sum_monomial (f : SkewPolynomial R) : f.sum (fun (a : ℕ) ↦ monomial a) = f :=
 SkewMonoidAlgebra.sum_single _

@[simp]
lemma sum_monomial_index {N} [AddCommMonoid N] {n : ℕ} {b : R} {h : ℕ → R → N}
    (h_zero : h n 0 = 0) : (monomial n b).sum h = h n b :=
  SkewMonoidAlgebra.sum_single_index h_zero

lemma monomial_injective (n : ℕ) : Function.Injective (monomial n : R → SkewPolynomial R) := by
  intro a b h
  simp only [monomial_def] at h
  exact single_injective (ofAdd n) h

@[simp]
lemma monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)

lemma monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← toFinsupp_single, toFinsupp_inj]
  rfl -- abuses ℕ ≃ Multiplicative ℕ

end Monomial
section phi

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- Ring homomorphism associated to the twist of the skew polynomial ring.
The multiplication in a skew polynomial ring is given by `xr = φ(r)x`. -/
abbrev φ := MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1)

theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1) := rfl

lemma φ_iterate_apply (n : ℕ) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

end phi

lemma monomial_mul_monomial [MulSemiringAction (Multiplicative ℕ) R] (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s)) := by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

lemma mul_def {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative ℕ) R] : f * g =
    f.sum fun (a₁ : ℕ) b₁ => g.sum fun (a₂ : ℕ) b₂ => monomial (a₁ + a₂) (b₁ * (φ^[a₁] b₂)) := by
  simp_rw [φ_iterate_apply]
  rfl

section Constant

/-- `C a` is the constant SkewPolynomial `a`. `C` is provided as an additive homomorphism. -/
def C : R →+ SkewPolynomial R := SkewMonoidAlgebra.singleAddHom 1

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := single_zero _

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp]
lemma sum_C_index {a} {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a := sum_single_index h

section RingHom

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- `CRingHom a` is the constant SkewPolynomial `a`, as a ring homomorphism. This requires
`[MulSemiringAction (Multiplicative ℕ) R]`. -/
def CRingHom : R →+* SkewPolynomial R := SkewMonoidAlgebra.singleOneRingHom

lemma CRingHom_eq_C : CRingHom a = C a := rfl

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := CRingHom.map_mul a b

lemma C_pow : C (a ^ n) = C a ^ n := CRingHom.map_pow a n

lemma C_eq_natCast (n : ℕ) : C (n : R) = (n : SkewPolynomial R) := map_natCast CRingHom n

@[simp]
lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]
lemma monomial_mul_C : monomial n a * C b = monomial n (a * (⇑φ)^[n] b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

end RingHom

end Constant

section Variable

/-- `X` is the SkewPolynomial variable (aka indeterminate). -/
def X : SkewPolynomial R := monomial 1 1

lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

variable [MulSemiringAction (Multiplicative ℕ) R]

lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero      => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ', ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial]
    simp [add_comm]

lemma X_mul : X * p = sum p (fun a b ↦ monomial a (φ b)) * X := by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp), sum_sum_index (by simp) (by simp)]
  simp [add_comm]

lemma X_pow_mul {n : ℕ} : X ^ n * p = sum p (fun (a : ℕ) b ↦ monomial a (φ^[n] b)) * X ^ n := by
  induction n generalizing p with
  | zero      => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ, sum_sum_index (by simp) (by simp)]
    simp

@[simp]
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [X, monomial_mul_monomial, iterate_map_one, mul_one]

@[simp]
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X ^ k = monomial (n+k) r := by
  induction k with
  | zero      => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

@[simp]
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) (φ r) := by
  simp [X_mul]

@[simp]
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n+k) (φ^[k] r) := by
  simp [X_pow_mul]

end Variable

section Coefficient

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
  SkewMonoidAlgebra.coeff_single_apply

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : SkewPolynomial R) n = 0 := rfl

@[simp] lemma coeff_one_zero [MulSemiringAction (Multiplicative ℕ) R] :
    coeff (1 : SkewPolynomial R) 0 = 1 := coeff_monomial

lemma coeff_one [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) :
    coeff (1 : SkewPolynomial R) n = if 0 = n then 1 else 0 := by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this, coeff_monomial]

@[simp] lemma coeff_X_one : coeff (X : SkewPolynomial R) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : SkewPolynomial R) 0 = 0 := coeff_monomial

@[simp] lemma coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 := by simp [coeff_monomial]

lemma coeff_X : coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : SkewPolynomial R) n = 0 := by
  rw [coeff_X, if_neg hn.symm]

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert coeff_monomial using 2; simp [eq_comm]

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[simp]
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
lemma coeff_natCast_ite [MulSemiringAction (Multiplicative ℕ) R] :
    (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m 0 := by
  simp [← C_eq_natCast, coeff_C]

@[simp]
lemma coeff_ofNat_zero [MulSemiringAction (Multiplicative ℕ) R] (a : ℕ) [a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) 0 = ofNat(a) := by simp [OfNat.ofNat]

@[simp]
lemma coeff_ofNat_succ [MulSemiringAction (Multiplicative ℕ) R] (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

lemma C_mul_X_pow_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] :
    ∀ {n : ℕ}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial,
      iterate_map_one, mul_one]

lemma C_mul_X_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] : C a * X = monomial 1 a := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]

lemma C_injective : Injective (C : R → SkewPolynomial R) := monomial_injective 0

@[simp] lemma C_inj : C a = C b ↔ a = b :=
  ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj

end Coefficient

lemma Nontrivial.of_polynomial_ne [MulSemiringAction (Multiplicative ℕ) R] (h : p ≠ q) :
    Nontrivial R :=
  ⟨⟨0, 1, fun h01 : 0 = 1 ↦ h <|
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

lemma ext_iff {p q : SkewPolynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
  SkewMonoidAlgebra.ext_iff

@[ext] lemma ext {p q : SkewPolynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
  SkewMonoidAlgebra.ext

@[ext] lemma addHom_ext' {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  SkewMonoidAlgebra.addHom_ext' h

lemma addHom_ext {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  SkewMonoidAlgebra.addHom_ext h

@[ext] lemma linearMap_ext' {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : SkewPolynomial R →ₗ[R] M} (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
    f = g :=
  SkewMonoidAlgebra.lhom_ext' h

lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : SkewPolynomial R) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Support

lemma support_monomial (n) {a : R} (H : a ≠ 0) : (monomial n a).support = singleton n := by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, coeff_single, Pi.single_apply, H]

lemma support_monomial' (n) {a : R} : (monomial n a).support ⊆ singleton n := by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset

lemma support_C {a : R} (h : a ≠ 0) : (C a).support = singleton 0 := support_monomial 0 h

lemma support_C_subset (a : R) : (C a).support ⊆ singleton 0 := support_monomial' 0

lemma support_C_mul_X [MulSemiringAction (Multiplicative ℕ) R] {c : R} (h : c ≠ 0) :
    support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]

lemma support_C_mul_X' [MulSemiringAction (Multiplicative ℕ) R] (c : R) :
    support (C c * X) ⊆ singleton 1 := by
  simpa [C_mul_X_eq_monomial] using support_monomial' 1

lemma support_C_mul_X_pow [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) {c : R} (h : c ≠ 0) :
    support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]

lemma support_C_mul_X_pow' [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) (c : R) :
    support (C c * X ^ n) ⊆ singleton n := by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial' n

open Finset
lemma support_binomial' [MulSemiringAction (Multiplicative ℕ) R] (k m : ℕ) (x y : R) :
    support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow' m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

lemma support_trinomial' [MulSemiringAction (Multiplicative ℕ) R] (k m n : ℕ) (x y z : R) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
  support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow' m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((support_C_mul_X_pow' n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

end Support

lemma X_pow_eq_monomial (n) [MulSemiringAction (Multiplicative ℕ) R] :
    X ^ n = monomial n (1 : R) := by
  induction n with
  | zero      => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ', hn, X, monomial_mul_monomial]
    simp [add_comm]

lemma smul_X_eq_monomial {n} [MulSemiringAction (Multiplicative ℕ) R] :
    a • X ^ n = monomial n (a : R) := by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp_all only [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n  := by rw [X_pow_eq_monomial]; rfl

lemma support_X_pow (H : ¬ (1 : R) = 0) (n : ℕ) [MulSemiringAction (Multiplicative ℕ) R] :
    (X ^ n : SkewPolynomial R).support = singleton n := by
  convert support_monomial n H
  exact X_pow_eq_monomial n

lemma support_X_empty (H : (1 : R) = 0) : (X : SkewPolynomial R).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

lemma support_X (H : ¬ (1 : R) = 0) [MulSemiringAction (Multiplicative ℕ) R] :
    (X : SkewPolynomial R).support = singleton 1 := by
  rw [← pow_one X, support_X_pow H 1]

lemma monomial_left_inj {R : Type*} [Semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
    (monomial i a) = (monomial j a) ↔ i = j :=
  SkewMonoidAlgebra.single_left_inj ha

lemma nat_cast_mul {R : Type*} [Semiring R] (n : ℕ) (p : SkewPolynomial R)
    [MulSemiringAction (Multiplicative ℕ) R] : (n : SkewPolynomial R) * p = n • p :=
  (nsmul_eq_mul _ _).symm
section sum

lemma sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : SkewPolynomial R} (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) {s : Finset ℕ} (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) := by
  rw [sum_def , Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

@[simp]
lemma sum_zero_index {S : Type*} [AddCommMonoid S] (f : ℕ → R → S) :
    (0 : SkewPolynomial R).sum f = 0 := by
  simp [sum_def', zero_def]

@[simp]
lemma sum_X_index {S : Type*} [AddCommMonoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (X : SkewPolynomial R).sum f = f 1 1 :=
  sum_monomial_index hf

lemma sum_add_index {S : Type*} [AddCommMonoid S] (p q : SkewPolynomial R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ ↦ hf (toAdd n)) (fun n _ ↦ h_add (toAdd n))

lemma sum_add' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f g : ℕ → R → S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [sum_def, Finset.sum_add_distrib]

lemma sum_add {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

lemma sum_smul_index {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (b : R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b * a) :=
  Finsupp.sum_smul_index hf

lemma sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : SkewPolynomial R)
    (b : T) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) :=
  Finsupp.sum_smul_index' hf

protected lemma smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : SkewPolynomial R)
    (b : T) (f : ℕ → R → S) : b • p.sum f = p.sum fun n a => b • f n a :=
  Finsupp.smul_sum

end sum

lemma induction {motive : SkewPolynomial R → Prop} (p : SkewPolynomial R) (h0 : motive 0)
  (ha : ∀ (n : ℕ) (r : R) (q : SkewPolynomial R), n ∉ q.support → r ≠ 0 → motive q →
    motive (SkewPolynomial.monomial n r + q)) : motive p := by
  apply SkewMonoidAlgebra.induction <;> aesop

@[simp]
lemma coeff_add (p q : SkewPolynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  simp only [coeff]
  exact SkewMonoidAlgebra.coeff_add p q n

end Semiring

section Ring

variable [Ring R]

lemma sum_neg {S : Type*} [Ring S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    (p.sum fun n x => - f n x) = - p.sum f := by
  simp [sum_def, Finset.sum_neg_distrib]

lemma sum_sub {S : Type*} [Ring S] (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x - g n x) = p.sum f - p.sum g := by
  simp only [sub_eq_add_neg, sum_add, sum_neg]

variable [MulSemiringAction (Multiplicative ℕ) R]

instance instRing : Ring (SkewPolynomial R) := SkewMonoidAlgebra.instRing

@[simp]
lemma coeff_neg (p : SkewPolynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := by
  simp only [coeff, ← add_eq_zero_iff_eq_neg, ← SkewMonoidAlgebra.coeff_add]
  convert coeff_zero (ofAdd n)
  exact neg_add_cancel p

@[simp]
lemma coeff_sub (p q : SkewPolynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_cancel, monomial_zero_right]

@[simp] lemma support_neg {p : SkewPolynomial R} : (-p).support = p.support := by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p

lemma monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, monomial_add, monomial_neg, sub_eq_add_neg]

lemma C_eq_intCast (n : ℤ) : C (n : R) = n := by simp [← CRingHom_eq_C]

lemma C_neg : C (-a) = -C a :=
  RingHom.map_neg CRingHom a

lemma C_sub : C (a - b) = C a - C b :=
  RingHom.map_sub CRingHom a b

end Ring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R]

instance instNontrivial : Nontrivial (SkewPolynomial R) :=
  SkewMonoidAlgebra.instNontrivialOfNonempty

lemma X_ne_zero : (X : SkewPolynomial R) ≠ 0 := mt (congr_arg (fun p ↦ coeff p 1)) (by simp)

end NontrivialSemiring

section erase

variable [Semiring R]

/-- `erase p n` is the polynomial `p` in which the `X ^ n` term has been erased. -/
def erase (n : ℕ) (p : SkewPolynomial R) : SkewPolynomial R :=
  SkewMonoidAlgebra.erase (ofAdd n) p

@[simp]
lemma support_erase (p : SkewPolynomial R) (n : ℕ) :
    support (p.erase n) = (support p).erase n := by
  simp [support_eq_skewMonoidAlgebra_support, erase]

lemma monomial_add_erase (p : SkewPolynomial R) (n : ℕ) :
    monomial n (coeff p n) + p.erase n = p := by
  simp only [coeff, monomial_def, erase]
  erw [SkewMonoidAlgebra.single_add_erase]

lemma coeff_erase (p : SkewPolynomial R) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]
lemma erase_zero (n : ℕ) : (0 : SkewPolynomial R).erase n = 0 := by
  simp [erase, zero_def]

@[simp]
lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 := by
  simp [erase, monomial_def, zero_def]

@[simp]
lemma erase_same (p : SkewPolynomial R) (n : ℕ) : coeff (p.erase n) n = 0 := by
    simp [coeff_erase]

@[simp]
lemma erase_ne (p : SkewPolynomial R) (n i : ℕ) (h : i ≠ n) :
    coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

end erase

section update

variable [Semiring R]

/-- Replace the coefficient of a `p : SkewPolynomial R` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`. -/
def update (p : SkewPolynomial R) (n : ℕ) (a : R) : SkewPolynomial R :=
  SkewMonoidAlgebra.update p (ofAdd n) a

lemma update_def (p : SkewPolynomial R) (n : ℕ) (a : R) :
    p.update n a = SkewMonoidAlgebra.update p (ofAdd n) a := rfl

lemma coeff_update (p : SkewPolynomial R) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a :=
  SkewMonoidAlgebra.coeff_update _ _ _

lemma coeff_update_apply (p : SkewPolynomial R) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i :=
  SkewMonoidAlgebra.coeff_update_apply _ _ _ _

@[simp]
lemma coeff_update_same (p : SkewPolynomial R) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, if_pos rfl]

lemma coeff_update_ne (p : SkewPolynomial R) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
lemma update_zero_eq_erase (p : SkewPolynomial R) (n : ℕ) : p.update n 0 = p.erase n := by
  ext
  rw [coeff_update_apply, coeff_erase]

lemma support_update (p : SkewPolynomial R) (n : ℕ) (a : R) [DecidableEq R] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs with ha
  · simp
  · simp

lemma support_update_zero (p : SkewPolynomial R) (n : ℕ) :
    support (p.update n 0) = p.support.erase n := by
  simp

lemma support_update_ne_zero (p : SkewPolynomial R) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end update

end SkewPolynomial
