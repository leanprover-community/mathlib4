/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Regular.Pow
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Order
import Mathlib.Order.SymmDiff

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `MvPolynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `MvPolynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`
* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`
* `C a` : the constant polynomial with value `a`
* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.
* `coeff s p` : the coefficient of `s` in `p`.

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `MvPolynomial σ R` is `(σ →₀ ℕ) →₀ R`; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
def MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

section Instances

instance decidableEqMvPolynomial [CommSemiring R] [DecidableEq σ] [DecidableEq R] :
    DecidableEq (MvPolynomial σ R) :=
  Finsupp.instDecidableEq

instance commSemiring [CommSemiring R] : CommSemiring (MvPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

instance inhabited [CommSemiring R] : Inhabited (MvPolynomial σ R) :=
  ⟨0⟩

instance distribuMulAction [Monoid R] [CommSemiring S₁] [DistribMulAction R S₁] :
    DistribMulAction R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.distribMulAction

instance smulZeroClass [CommSemiring S₁] [SMulZeroClass R S₁] :
    SMulZeroClass R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.smulZeroClass

instance faithfulSMul [CommSemiring S₁] [SMulZeroClass R S₁] [FaithfulSMul R S₁] :
    FaithfulSMul R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.faithfulSMul

instance module [Semiring R] [CommSemiring S₁] [Module R S₁] : Module R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.module

instance isScalarTower [CommSemiring S₂] [SMul R S₁] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [IsScalarTower R S₁ S₂] : IsScalarTower R S₁ (MvPolynomial σ S₂) :=
  AddMonoidAlgebra.isScalarTower

instance smulCommClass [CommSemiring S₂] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [SMulCommClass R S₁ S₂] : SMulCommClass R S₁ (MvPolynomial σ S₂) :=
  AddMonoidAlgebra.smulCommClass

instance isCentralScalar [CommSemiring S₁] [SMulZeroClass R S₁] [SMulZeroClass Rᵐᵒᵖ S₁]
    [IsCentralScalar R S₁] : IsCentralScalar R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.isCentralScalar

instance algebra [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] :
    Algebra R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.algebra

instance isScalarTower_right [CommSemiring S₁] [DistribSMul R S₁] [IsScalarTower R S₁ S₁] :
    IsScalarTower R (MvPolynomial σ S₁) (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.isScalarTower_self _

instance smulCommClass_right [CommSemiring S₁] [DistribSMul R S₁] [SMulCommClass R S₁ S₁] :
    SMulCommClass R (MvPolynomial σ S₁) (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.smulCommClass_self _

/-- If `R` is a subsingleton, then `MvPolynomial σ R` has a unique element -/
instance unique [CommSemiring R] [Subsingleton R] : Unique (MvPolynomial σ R) :=
  AddMonoidAlgebra.unique

end Instances

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s` -/
def monomial (s : σ →₀ ℕ) : R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.lsingle s

theorem one_def : (1 : MvPolynomial σ R) = monomial 0 1 := rfl

theorem single_eq_monomial (s : σ →₀ ℕ) (a : R) : Finsupp.single s a = monomial s a :=
  rfl

theorem mul_def : p * q = p.sum fun m a => q.sum fun n b => monomial (m + n) (a * b) :=
  AddMonoidAlgebra.mul_def

/-- `C a` is the constant polynomial with value `a` -/
def C : R →+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

@[simp]
theorem algebraMap_eq : algebraMap R (MvPolynomial σ R) = C :=
  rfl

variable {R σ}

@[simp]
theorem algebraMap_apply [Algebra R S₁] (r : R) :
    algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) :=
  rfl

/-- `X n` is the degree `1` monomial $X_n$. -/
def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1

theorem monomial_left_injective {r : R} (hr : r ≠ 0) :
    Function.Injective fun s : σ →₀ ℕ => monomial s r :=
  Finsupp.single_left_injective hr

@[simp]
theorem monomial_left_inj {s t : σ →₀ ℕ} {r : R} (hr : r ≠ 0) :
    monomial s r = monomial t r ↔ s = t :=
  Finsupp.single_left_inj hr

theorem C_apply : (C a : MvPolynomial σ R) = monomial 0 a :=
  rfl

@[simp]
theorem C_0 : C 0 = (0 : MvPolynomial σ R) := map_zero _

@[simp]
theorem C_1 : C 1 = (1 : MvPolynomial σ R) :=
  rfl

theorem C_mul_monomial : C a * monomial s a' = monomial s (a * a') := by
  -- Porting note: this `change` feels like defeq abuse, but I can't find the appropriate lemmas
  change AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _
  simp [single_mul_single]

@[simp]
theorem C_add : (C (a + a') : MvPolynomial σ R) = C a + C a' :=
  Finsupp.single_add _ _ _

@[simp]
theorem C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a' :=
  C_mul_monomial.symm

@[simp]
theorem C_pow (a : R) (n : ℕ) : (C (a ^ n) : MvPolynomial σ R) = C a ^ n :=
  map_pow _ _ _

theorem C_injective (σ : Type*) (R : Type*) [CommSemiring R] :
    Function.Injective (C : R → MvPolynomial σ R) :=
  Finsupp.single_injective _

theorem C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] :
    Function.Surjective (C : R → MvPolynomial σ R) := by
  refine fun p => ⟨p.toFun 0, Finsupp.ext fun a => ?_⟩
  simp only [C_apply, ← single_eq_monomial, (Finsupp.ext isEmptyElim (α := σ) : a = 0),
    single_eq_same]
  rfl

@[simp]
theorem C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s : R) :
    (C r : MvPolynomial σ R) = C s ↔ r = s :=
  (C_injective σ R).eq_iff

@[simp] lemma C_eq_zero : (C a : MvPolynomial σ R) = 0 ↔ a = 0 := by rw [← map_zero C, C_inj]

lemma C_ne_zero : (C a : MvPolynomial σ R) ≠ 0 ↔ a ≠ 0 :=
  C_eq_zero.ne

instance nontrivial_of_nontrivial (σ : Type*) (R : Type*) [CommSemiring R] [Nontrivial R] :
    Nontrivial (MvPolynomial σ R) :=
  inferInstanceAs (Nontrivial <| AddMonoidAlgebra R (σ →₀ ℕ))

instance infinite_of_infinite (σ : Type*) (R : Type*) [CommSemiring R] [Infinite R] :
    Infinite (MvPolynomial σ R) :=
  Infinite.of_injective C (C_injective _ _)

instance infinite_of_nonempty (σ : Type*) (R : Type*) [Nonempty σ] [CommSemiring R]
    [Nontrivial R] : Infinite (MvPolynomial σ R) :=
  Infinite.of_injective ((fun s : σ →₀ ℕ => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
    <| (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)

instance [CommSemiring R] [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) :=
  inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ..))

instance [CommSemiring R] [IsCancelAdd R] [IsCancelMulZero R] :
    IsCancelMulZero (MvPolynomial σ R) :=
  inferInstanceAs (IsCancelMulZero (AddMonoidAlgebra ..))

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance [CommSemiring R] [IsCancelAdd R] [IsDomain R] : IsDomain (MvPolynomial σ R) where

theorem C_eq_coe_nat (n : ℕ) : (C ↑n : MvPolynomial σ R) = n := by
  induction n <;> simp [*]

theorem C_mul' : MvPolynomial.C a * p = a • p :=
  (Algebra.smul_def a p).symm

theorem smul_eq_C_mul (p : MvPolynomial σ R) (a : R) : a • p = C a * p :=
  C_mul'.symm

theorem C_eq_smul_one : (C a : MvPolynomial σ R) = a • (1 : MvPolynomial σ R) := by
  rw [← C_mul', mul_one]

theorem smul_monomial {S₁ : Type*} [SMulZeroClass S₁ R] (r : S₁) :
    r • monomial s a = monomial s (r • a) :=
  Finsupp.smul_single _ _ _

theorem X_injective [Nontrivial R] : Function.Injective (X : σ → MvPolynomial σ R) :=
  (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]
theorem X_inj [Nontrivial R] (m n : σ) : X m = (X n : MvPolynomial σ R) ↔ m = n :=
  X_injective.eq_iff

theorem monomial_pow : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow e

@[simp]
theorem monomial_mul {s s' : σ →₀ ℕ} {a b : R} :
    monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single

variable (σ R)

/-- `fun s ↦ monomial s 1` as a homomorphism. -/
def monomialOneHom : Multiplicative (σ →₀ ℕ) →* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _

variable {σ R}

@[simp]
theorem monomialOneHom_apply : monomialOneHom R σ s = (monomial s 1 : MvPolynomial σ R) :=
  rfl

theorem X_pow_eq_monomial : X n ^ e = monomial (Finsupp.single n e) (1 : R) := by
  simp [X, monomial_pow]

theorem monomial_add_single : monomial (s + Finsupp.single n e) a = monomial s a * X n ^ e := by
  rw [X_pow_eq_monomial, monomial_mul, mul_one]

theorem monomial_single_add : monomial (Finsupp.single n e + s) a = X n ^ e * monomial s a := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

theorem C_mul_X_pow_eq_monomial {s : σ} {a : R} {n : ℕ} :
    C a * X s ^ n = monomial (Finsupp.single s n) a := by
  rw [← zero_add (Finsupp.single s n), monomial_add_single, C_apply]

theorem C_mul_X_eq_monomial {s : σ} {a : R} : C a * X s = monomial (Finsupp.single s 1) a := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp]
theorem monomial_zero {s : σ →₀ ℕ} : monomial s (0 : R) = 0 :=
  Finsupp.single_zero _

@[simp]
theorem monomial_zero' : (monomial (0 : σ →₀ ℕ) : R → MvPolynomial σ R) = C :=
  rfl

@[simp]
theorem monomial_eq_zero {s : σ →₀ ℕ} {b : R} : monomial s b = 0 ↔ b = 0 :=
  Finsupp.single_eq_zero

@[simp]
theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A}
    (w : b u 0 = 0) : sum (monomial u r) b = b u r :=
  Finsupp.sum_single_index w

@[simp]
theorem sum_C {A : Type*} [AddCommMonoid A] {b : (σ →₀ ℕ) → R → A} (w : b 0 0 = 0) :
    sum (C a) b = b 0 a :=
  sum_monomial_eq w

theorem monomial_sum_one {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) :
    (monomial (∑ i ∈ s, f i) 1 : MvPolynomial σ R) = ∏ i ∈ s, monomial (f i) 1 :=
  map_prod (monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

theorem monomial_sum_index {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) (a : R) :
    monomial (∑ i ∈ s, f i) a = C a * ∏ i ∈ s, monomial (f i) 1 := by
  rw [← monomial_sum_one, C_mul', ← (monomial _).map_smul, smul_eq_mul, mul_one]

theorem monomial_finsupp_sum_index {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → σ →₀ ℕ)
    (a : R) : monomial (f.sum g) a = C a * f.prod fun a b => monomial (g a b) 1 :=
  monomial_sum_index _ _ _

theorem monomial_eq_monomial_iff {α : Type*} (a₁ a₂ : α →₀ ℕ) (b₁ b₂ : R) :
    monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 :=
  Finsupp.single_eq_single_iff _ _ _ _

theorem monomial_eq : monomial s a = C a * (s.prod fun n e => X n ^ e : MvPolynomial σ R) := by
  simp only [X_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]

@[simp]
lemma prod_X_pow_eq_monomial : ∏ x ∈ s.support, X x ^ s x = monomial s (1 : R) := by
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod]

@[elab_as_elim]
theorem induction_on_monomial {motive : MvPolynomial σ R → Prop}
    (C : ∀ a, motive (C a))
    (mul_X : ∀ p n, motive p → motive (p * X n)) : ∀ s a, motive (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℕ _ _ s
  · change motive (monomial 0 a)
    exact C a
  · intro n e p _hpn _he ih
    have : ∀ e : ℕ, motive (monomial p a * X n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [pow_succ, (mul_assoc _ _ _).symm, mul_X, e_ih]
    simp [add_comm, monomial_add_single, this]

/-- Analog of `Polynomial.induction_on'`.
To prove something about mv_polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials. -/
@[elab_as_elim]
theorem induction_on' {P : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (monomial : ∀ (u : σ →₀ ℕ) (a : R), P (monomial u a))
    (add : ∀ p q : MvPolynomial σ R, P p → P q → P (p + q)) : P p :=
  Finsupp.induction p
    (suffices P (MvPolynomial.monomial 0 0) by rwa [monomial_zero] at this
    show P (MvPolynomial.monomial 0 0) from monomial 0 0)
    fun _ _ _ _ha _hb hPf => add _ _ (monomial _ _) hPf

/--
Similar to `MvPolynomial.induction_on` but only a weak form of `h_add` is required.
In particular, this version only requires us to show
that `motive` is closed under addition of nontrivial monomials not present in the support.
-/
@[elab_as_elim]
theorem monomial_add_induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.support → b ≠ 0 → motive f → motive ((monomial a b) + f)) :
    motive p :=
  Finsupp.induction p (C_0.rec <| C 0) monomial_add

@[deprecated (since := "2025-03-11")]
alias induction_on''' := monomial_add_induction_on

/--
Similar to `MvPolynomial.induction_on` but only a yet weaker form of `h_add` is required.
In particular, this version only requires us to show
that `motive` is closed under addition of monomials not present in the support
for which `motive` is already known to hold.
-/
theorem induction_on'' {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.support → b ≠ 0 → motive f → motive (monomial a b) →
          motive ((monomial a b) + f))
    (mul_X : ∀ (p : MvPolynomial σ R) (n : σ), motive p → motive (p * MvPolynomial.X n)) :
    motive p :=
  monomial_add_induction_on p C fun a b f ha hb hf =>
    monomial_add a b f ha hb hf <| induction_on_monomial C mul_X a b

/--
Analog of `Polynomial.induction_on`.
If a property holds for any constant polynomial
and is preserved under addition and multiplication by variables
then it holds for all multivariate polynomials.
-/
@[recursor 5]
theorem induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (C : ∀ a, motive (C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (mul_X : ∀ p n, motive p → motive (p * X n)) : motive p :=
  induction_on'' p C (fun a b f _ha _hb hf hm => add (monomial a b) f hm hf) mul_X

theorem ringHom_ext {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : ∀ r, f (C r) = g (C r)) (hX : ∀ i, f (X i) = g (X i)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intro x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `Finsupp.mulHom_ext'` needs to have increased priority
    apply MonoidHom.ext_mnat
    exact hX _

/-- See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem ringHom_ext' {A : Type*} [Semiring A] {f g : MvPolynomial σ R →+* A}
    (hC : f.comp C = g.comp C) (hX : ∀ i, f (X i) = g (X i)) : f = g :=
  ringHom_ext (RingHom.ext_iff.1 hC) hX

theorem hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ R →+* S₂) (hC : f.comp C = g.comp C)
    (hX : ∀ n : σ, f (X n) = g (X n)) (p : MvPolynomial σ R) : f p = g p :=
  RingHom.congr_fun (ringHom_ext' hC hX) p

theorem is_id (f : MvPolynomial σ R →+* MvPolynomial σ R) (hC : f.comp C = C)
    (hX : ∀ n : σ, f (X n) = X n) (p : MvPolynomial σ R) : f p = p :=
  hom_eq_hom f (RingHom.id _) hC hX p

@[ext 1100]
theorem algHom_ext' {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    {f g : MvPolynomial σ A →ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) =
        g.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (h₂ : ∀ i, f (X i) = g (X i)) : f = g :=
  AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

@[ext 1200]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : MvPolynomial σ R →ₐ[R] A}
    (hf : ∀ i : σ, f (X i) = g (X i)) : f = g :=
  AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun X : σ => MonoidHom.ext_mnat (hf X))

@[simp]
theorem algHom_C {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R →ₐ[R] A) (r : R) :
    f (C r) = algebraMap R A r :=
  f.commutes r

@[simp]
theorem adjoin_range_X : Algebra.adjoin R (range (X : σ → MvPolynomial σ R)) = ⊤ := by
  set S := Algebra.adjoin R (range (X : σ → MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin <| mem_range_self _)

@[ext]
theorem linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : MvPolynomial σ R →ₗ[R] M}
    (h : ∀ s, f ∘ₗ monomial s = g ∘ₗ monomial s) : f = g :=
  Finsupp.lhom_ext' h

section Support

/-- The finite set of all `m : σ →₀ ℕ` such that `X^m` has a non-zero coefficient. -/
def support (p : MvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  Finsupp.support p

theorem finsupp_support_eq_support (p : MvPolynomial σ R) : Finsupp.support p = p.support :=
  rfl

theorem support_monomial [h : Decidable (a = 0)] :
    (monomial s a).support = if a = 0 then ∅ else {s} := by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl

theorem support_monomial_subset : (monomial s a).support ⊆ {s} :=
  support_single_subset

theorem support_add [DecidableEq σ] : (p + q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_add

theorem support_X [Nontrivial R] : (X n : MvPolynomial σ R).support = {Finsupp.single n 1} := by
  classical rw [X, support_monomial, if_neg]; exact one_ne_zero

theorem support_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (X s ^ n : MvPolynomial σ R).support = {Finsupp.single s n} := by
  classical
    rw [X_pow_eq_monomial, support_monomial, if_neg (one_ne_zero' R)]

@[simp]
theorem support_zero : (0 : MvPolynomial σ R).support = ∅ :=
  rfl

theorem support_smul {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial σ R} :
    (a • f).support ⊆ f.support :=
  Finsupp.support_smul

theorem support_sum {α : Type*} [DecidableEq σ] {s : Finset α} {f : α → MvPolynomial σ R} :
    (∑ x ∈ s, f x).support ⊆ s.biUnion fun x => (f x).support :=
  Finsupp.support_finset_sum

end Support

section Coeff

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
def coeff (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  @DFunLike.coe ((σ →₀ ℕ) →₀ R) _ _ _ p m

@[simp]
theorem mem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∈ p.support ↔ p.coeff m ≠ 0 := by
  simp [support, coeff]

theorem notMem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∉ p.support ↔ p.coeff m = 0 :=
  by simp

@[deprecated (since := "2025-05-23")] alias not_mem_support_iff := notMem_support_iff

theorem sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ →₀ ℕ) → R → A} :
    p.sum b = ∑ m ∈ p.support, b m (p.coeff m) := by simp [support, Finsupp.sum, coeff]

theorem support_mul [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p * q).support ⊆ p.support + q.support :=
  AddMonoidAlgebra.support_mul p q

lemma disjoint_support_monomial {a : σ →₀ ℕ} {p : MvPolynomial σ R} {s : R}
    (ha : a ∉ p.support) (hs : s ≠ 0) : Disjoint (monomial a s).support p.support := by
  classical
  simpa [support_monomial, hs] using notMem_support_iff.mp ha

@[ext]
theorem ext (p q : MvPolynomial σ R) : (∀ m, coeff m p = coeff m q) → p = q :=
  Finsupp.ext

@[simp]
theorem coeff_add (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p + q) = coeff m p + coeff m q :=
  add_apply p q m

@[simp]
theorem coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m : σ →₀ ℕ) (C : S₁) (p : MvPolynomial σ R) :
    coeff m (C • p) = C • coeff m p :=
  smul_apply C p m

@[simp]
theorem coeff_zero (m : σ →₀ ℕ) : coeff m (0 : MvPolynomial σ R) = 0 :=
  rfl

@[simp]
theorem coeff_zero_X (i : σ) : coeff 0 (X i : MvPolynomial σ R) = 0 :=
  single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

@[simp]
theorem coeff_mapRange (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) (m) :
    coeff m (mapRange g hg φ) = g (coeff m φ) := by
  simp [mapRange, coeff]

/-- `MvPolynomial.coeff m` but promoted to an `AddMonoidHom`. -/
@[simps]
def coeffAddMonoidHom (m : σ →₀ ℕ) : MvPolynomial σ R →+ R where
  toFun := coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m

variable (R) in
/-- `MvPolynomial.coeff m` but promoted to a `LinearMap`. -/
@[simps]
def lcoeff (m : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] R where
  toFun := coeff m
  map_add' := coeff_add m
  map_smul' := coeff_smul m

theorem coeff_sum {X : Type*} (s : Finset X) (f : X → MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, coeff m (f x) :=
  map_sum (@coeffAddMonoidHom R σ _ _) _ s

theorem monic_monomial_eq (m) :
    monomial m (1 : R) = (m.prod fun n e => X n ^ e : MvPolynomial σ R) := by simp [monomial_eq]

@[simp]
theorem coeff_monomial [DecidableEq σ] (m n) (a) :
    coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0 :=
  Finsupp.single_apply

@[simp]
theorem coeff_C [DecidableEq σ] (m) (a) :
    coeff m (C a : MvPolynomial σ R) = if 0 = m then a else 0 :=
  Finsupp.single_apply

lemma eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynomial σ R) :
    p = C (p.coeff 0) := by
  obtain ⟨x, rfl⟩ := C_surjective σ p
  simp

theorem coeff_one [DecidableEq σ] (m) : coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0 :=
  coeff_C m 1

@[simp]
theorem coeff_zero_C (a) : coeff 0 (C a : MvPolynomial σ R) = a :=
  single_eq_same

@[simp]
theorem coeff_zero_one : coeff 0 (1 : MvPolynomial σ R) = 1 :=
  coeff_zero_C 1

theorem coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : ℕ) :
    coeff m (X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 else 0 := by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _

theorem coeff_X' [DecidableEq σ] (i : σ) (m) :
    coeff m (X i : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0 := by
  rw [← coeff_X_pow, pow_one]

@[simp]
theorem coeff_X (i : σ) : coeff (Finsupp.single i 1) (X i : MvPolynomial σ R) = 1 := by
  classical rw [coeff_X', if_pos rfl]

@[simp]
theorem coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : coeff m (C a * p) = a * coeff m p := by
  classical
  rw [mul_def, sum_C]
  · simp +contextual [sum_def, coeff_sum]
  simp

theorem coeff_mul [DecidableEq σ] (p q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (p * q) = ∑ x ∈ Finset.antidiagonal n, coeff x.1 p * coeff x.2 q :=
  AddMonoidAlgebra.mul_apply_antidiagonal p q _ _ Finset.mem_antidiagonal

@[simp]
theorem coeff_mul_monomial (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (m + s) (p * monomial s r) = coeff m p * r :=
  AddMonoidAlgebra.mul_single_apply_aux p r fun _a _ => add_left_inj _

@[simp]
theorem coeff_monomial_mul (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (s + m) (monomial s r * p) = r * coeff m p :=
  AddMonoidAlgebra.single_mul_apply_aux p r fun _a _ => add_right_inj _

@[simp]
theorem coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (m + Finsupp.single s 1) (p * X s) = coeff m p :=
  (coeff_mul_monomial _ _ _ _).trans (mul_one _)

@[simp]
theorem coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) :
    coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p :=
  (coeff_monomial_mul _ _ _ _).trans (one_mul _)

lemma coeff_single_X_pow [DecidableEq σ] (s s' : σ) (n n' : ℕ) :
    (X (R := R) s ^ n).coeff (Finsupp.single s' n')
    = if s = s' ∧ n = n' ∨ n = 0 ∧ n' = 0 then 1 else 0 := by
  simp only [coeff_X_pow, single_eq_single_iff]

@[simp]
lemma coeff_single_X [DecidableEq σ] (s s' : σ) (n : ℕ) :
    (X s).coeff (R := R) (Finsupp.single s' n) = if n = 1 ∧ s = s' then 1 else 0 := by
  simpa [eq_comm, and_comm] using coeff_single_X_pow s s' 1 n

@[simp]
theorem support_mul_X (s : σ) (p : MvPolynomial σ R) :
    (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_mul_single p _ (by simp) _

@[simp]
theorem support_X_mul (s : σ) (p : MvPolynomial σ R) :
    (X s * p).support = p.support.map (addLeftEmbedding (Finsupp.single s 1)) :=
  AddMonoidAlgebra.support_single_mul p _ (by simp) _

@[simp]
theorem support_smul_eq {S₁ : Type*} [Semiring S₁] [Module S₁ R] [NoZeroSMulDivisors S₁ R] {a : S₁}
    (h : a ≠ 0) (p : MvPolynomial σ R) : (a • p).support = p.support :=
  Finsupp.support_smul_eq h

theorem support_sdiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support \ q.support ⊆ (p + q).support := by
  intro m hm
  simp only [Classical.not_not, mem_support_iff, Finset.mem_sdiff, Ne] at hm
  simp [hm.2, hm.1]

open scoped symmDiff in
theorem support_symmDiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support ∆ q.support ⊆ (p + q).support := by
  rw [symmDiff_def, Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact support_sdiff_support_subset_support_add q p

theorem coeff_mul_monomial' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (p * monomial s r) = if s ≤ m then coeff (m - s) p * r else 0 := by
  classical
  split_ifs with h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : ∃ j ∈ support p, j + s = m := by
      simpa [Finset.mem_add]
        using Finset.add_subset_add_left support_monomial_subset <| support_mul _ _ h
    exact le_add_left le_rfl

theorem coeff_monomial_mul' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (monomial s r * p) = if s ≤ m then r * coeff (m - s) p else 0 := by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm, mul_comm r]
  exact coeff_mul_monomial' _ _ _ _

theorem coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (p * X s) = if s ∈ m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]

theorem coeff_X_mul' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (X s * p) = if s ∈ m.support then coeff (m - Finsupp.single s 1) p else 0 := by
  refine (coeff_monomial_mul' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    one_mul]

theorem eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ ∀ d, coeff d p = 0 := by
  rw [MvPolynomial.ext_iff]
  simp only [coeff_zero]

theorem ne_zero_iff {p : MvPolynomial σ R} : p ≠ 0 ↔ ∃ d, coeff d p ≠ 0 := by
  rw [Ne, eq_zero_iff]
  push_neg
  rfl

@[simp]
theorem X_ne_zero [Nontrivial R] (s : σ) :
    X (R := R) s ≠ 0 := by
  rw [ne_zero_iff]
  use Finsupp.single s 1
  simp only [coeff_X, ne_eq, one_ne_zero, not_false_eq_true]

@[simp]
theorem support_eq_empty {p : MvPolynomial σ R} : p.support = ∅ ↔ p = 0 :=
  Finsupp.support_eq_empty

@[simp]
lemma support_nonempty {p : MvPolynomial σ R} : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]

theorem exists_coeff_ne_zero {p : MvPolynomial σ R} (h : p ≠ 0) : ∃ d, coeff d p ≠ 0 :=
  ne_zero_iff.mp h

theorem C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose C hc using h
    classical
      let c' : (σ →₀ ℕ) → R := fun i => if i ∈ φ.support then C i else 0
      let ψ : MvPolynomial σ R := ∑ i ∈ φ.support, monomial i (c' i)
      use ψ
      apply MvPolynomial.ext
      intro i
      simp only [ψ, c', coeff_C_mul, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [notMem_support_iff] at hi
        rwa [mul_zero]

@[simp] lemma isRegular_X : IsRegular (X n : MvPolynomial σ R) := by
  suffices IsLeftRegular (X n : MvPolynomial σ R) from
    ⟨this, this.right_of_commute <| Commute.all _⟩
  intro P Q (hPQ : (X n) * P = (X n) * Q)
  ext i
  rw [← coeff_X_mul i n P, hPQ, coeff_X_mul i n Q]

@[simp] lemma isRegular_X_pow (k : ℕ) : IsRegular (X n ^ k : MvPolynomial σ R) := isRegular_X.pow k

@[simp] lemma isRegular_prod_X (s : Finset σ) :
    IsRegular (∏ n ∈ s, X n : MvPolynomial σ R) :=
  IsRegular.prod fun _ _ ↦ isRegular_X

/-- The finset of nonzero coefficients of a multivariate polynomial. -/
def coeffs (p : MvPolynomial σ R) : Finset R :=
  letI := Classical.decEq R
  Finset.image p.coeff p.support

@[simp]
lemma coeffs_zero : coeffs (0 : MvPolynomial σ R) = ∅ :=
  rfl

lemma coeffs_one : coeffs (1 : MvPolynomial σ R) ⊆ {1} := by
  classical
    rw [coeffs, Finset.image_subset_iff]
    simp_all [coeff_one]

@[nontriviality]
lemma coeffs_eq_empty_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : p.coeffs = ∅ := by
  simpa [coeffs] using Subsingleton.eq_zero p

@[simp]
lemma coeffs_one_of_nontrivial [Nontrivial R] : coeffs (1 : MvPolynomial σ R) = {1} := by
  apply Finset.Subset.antisymm coeffs_one
  simp only [coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩

lemma mem_coeffs_iff {p : MvPolynomial σ R} {c : R} :
    c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]

lemma coeff_mem_coeffs {p : MvPolynomial σ R} (m : σ →₀ ℕ)
    (h : p.coeff m ≠ 0) : p.coeff m ∈ p.coeffs :=
  letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (mem_support_iff.mpr h)

lemma zero_notMem_coeffs (p : MvPolynomial σ R) : 0 ∉ p.coeffs := by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := mem_coeffs_iff.mp hz
  exact (mem_support_iff.mp hnsupp) hn.symm

@[deprecated (since := "2025-05-23")] alias zero_not_mem_coeffs := zero_notMem_coeffs

lemma coeffs_C [DecidableEq R] (r : R) : (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r} := by
  classical
  aesop (add simp mem_coeffs_iff)

lemma coeffs_C_subset (r : R) : (C (σ := σ) r).coeffs ⊆ {r} := by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]
lemma coeffs_mul_X (p : MvPolynomial σ R) (n : σ) : (p * X n).coeffs = p.coeffs := by
  classical
  aesop (add simp mem_coeffs_iff)

@[simp]
lemma coeffs_X_mul (p : MvPolynomial σ R) (n : σ) : (X n * p).coeffs = p.coeffs := by
  classical
  aesop (add simp mem_coeffs_iff)

lemma coeffs_add [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.support q.support) :
    (p + q).coeffs = p.coeffs ∪ q.coeffs := by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ →₀ ℕ) (hne : p.coeff n ≠ 0) : q.coeff n = 0 :=
    notMem_support_iff.mp <| h.notMem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ →₀ ℕ) (hne : q.coeff n ≠ 0) : p.coeff n = 0 :=
    notMem_support_iff.mp <| h.notMem_of_mem_right_finset (mem_support_iff.mpr hne)
  have hor (n) (h : ¬coeff n p + coeff n q = 0) : coeff n p ≠ 0 ∨ coeff n q ≠ 0 := by
    by_cases hp : coeff n p = 0 <;> simp_all
  refine ⟨fun ⟨n, hn1, hn2⟩ ↦ ?_, ?_⟩
  · obtain (h | h) := hor n hn1
    · exact Or.inl ⟨n, by simp [h, hn2, hl n h]⟩
    · exact Or.inr ⟨n, by simp [h, hn2, hr n h]⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨n, by simp [hl n hn, hn]⟩
    · exact ⟨n, by simp [hr n hn, hn]⟩

end Coeff

section ConstantCoeff

/-- `constantCoeff p` returns the constant term of the polynomial `p`, defined as `coeff 0 p`.
This is a ring homomorphism.
-/
def constantCoeff : MvPolynomial σ R →+* R where
  toFun := coeff 0
  map_one' := by simp
  map_mul' := by classical simp [coeff_mul]
  map_zero' := coeff_zero _
  map_add' := coeff_add _

theorem constantCoeff_eq : (constantCoeff : MvPolynomial σ R → R) = coeff 0 :=
  rfl

variable (σ) in
@[simp]
theorem constantCoeff_C (r : R) : constantCoeff (C r : MvPolynomial σ R) = r := by
  classical simp [constantCoeff_eq]

variable (R) in
@[simp]
theorem constantCoeff_X (i : σ) : constantCoeff (X i : MvPolynomial σ R) = 0 := by
  simp [constantCoeff_eq]

@[simp]
theorem constantCoeff_smul {R : Type*} [SMulZeroClass R S₁] (a : R) (f : MvPolynomial σ S₁) :
    constantCoeff (a • f) = a • constantCoeff f :=
  rfl

theorem constantCoeff_monomial [DecidableEq σ] (d : σ →₀ ℕ) (r : R) :
    constantCoeff (monomial d r) = if d = 0 then r else 0 := by
  rw [constantCoeff_eq, coeff_monomial]

variable (σ R)

@[simp]
theorem constantCoeff_comp_C : constantCoeff.comp (C : R →+* MvPolynomial σ R) = RingHom.id R := by
  ext x
  exact constantCoeff_C σ x

theorem constantCoeff_comp_algebraMap :
    constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R :=
  constantCoeff_comp_C _ _

end ConstantCoeff

section AsSum

@[simp]
theorem support_sum_monomial_coeff (p : MvPolynomial σ R) :
    (∑ v ∈ p.support, monomial v (coeff v p)) = p :=
  Finsupp.sum_single p

theorem as_sum (p : MvPolynomial σ R) : p = ∑ v ∈ p.support, monomial v (coeff v p) :=
  (support_sum_monomial_coeff p).symm

end AsSum

section coeffsIn
variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

section Module
variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

variable (σ M) in
/-- The `R`-submodule of multivariate polynomials whose coefficients lie in a `R`-submodule `M`. -/
@[simps]
def coeffsIn : Submodule R (MvPolynomial σ S) where
  carrier := {p | ∀ i, p.coeff i ∈ M}
  add_mem' := by simp+contextual [add_mem]
  zero_mem' := by simp
  smul_mem' := by simp+contextual [Submodule.smul_mem]

lemma mem_coeffsIn : p ∈ coeffsIn σ M ↔ ∀ i, p.coeff i ∈ M := .rfl

@[simp]
lemma monomial_mem_coeffsIn : monomial i x ∈ coeffsIn σ M ↔ x ∈ M := by
  classical
  simp only [mem_coeffsIn, coeff_monomial]
  exact ⟨fun h ↦ by simpa using h i, fun hs j ↦ by split <;> simp [hs]⟩

@[simp]
lemma C_mem_coeffsIn : C x ∈ coeffsIn σ M ↔ x ∈ M := by simpa using monomial_mem_coeffsIn (i := 0)

@[simp]
lemma one_coeffsIn : 1 ∈ coeffsIn σ M ↔ 1 ∈ M := by simpa using C_mem_coeffsIn (x := (1 : S))

@[simp]
lemma mul_monomial_mem_coeffsIn : p * monomial i 1 ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  classical
  simp only [mem_coeffsIn, coeff_mul_monomial']
  constructor
  · rintro hp j
    simpa using hp (j + i)
  · rintro hp i
    split <;> simp [hp]

@[simp]
lemma monomial_mul_mem_coeffsIn : monomial i 1 * p ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  simp [mul_comm]

@[simp]
lemma mul_X_mem_coeffsIn : p * X s ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by
  simpa [-mul_monomial_mem_coeffsIn] using mul_monomial_mem_coeffsIn (i := .single s 1)

@[simp]
lemma X_mul_mem_coeffsIn : X s * p ∈ coeffsIn σ M ↔ p ∈ coeffsIn σ M := by simp [mul_comm]

variable (M) in
lemma coeffsIn_eq_span_monomial : coeffsIn σ M = .span R {monomial i m | (m ∈ M) (i : σ →₀ ℕ)} := by
  classical
  refine le_antisymm ?_ <| Submodule.span_le.2 ?_
  · rintro p hp
    rw [p.as_sum]
    exact sum_mem fun i hi ↦ Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]

lemma coeffsIn_le {N : Submodule R (MvPolynomial σ S)} :
    coeffsIn σ M ≤ N ↔ ∀ m ∈ M, ∀ i, monomial i m ∈ N := by
  simp [coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_swap (α := MvPolynomial σ S)]

lemma mem_coeffsIn_iff_coeffs_subset : p ∈ coeffsIn σ M ↔ (p.coeffs : Set S) ⊆ M := by
  simp only [mem_coeffsIn, coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ ↦ h x, fun h i ↦ ?_⟩
  by_cases hp : i ∈ p.support
  · exact h hp
  · convert M.zero_mem
    simpa using hp

end Module

section Algebra
variable [Algebra R S] {M : Submodule R S}

lemma coeffsIn_mul (M N : Submodule R S) : coeffsIn σ (M * N) = coeffsIn σ M * coeffsIn σ N := by
  classical
  refine le_antisymm (coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s, ← monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] using add_mem hx hy
  · rw [Submodule.mul_le]
    intro x hx y hy k
    rw [MvPolynomial.coeff_mul]
    exact sum_mem fun c hc ↦ Submodule.mul_mem_mul (hx _) (hy _)

lemma coeffsIn_pow : ∀ {n}, n ≠ 0 → ∀ M : Submodule R S, coeffsIn σ (M ^ n) = coeffsIn σ M ^ n
  | 1, _, M => by simp
  | n + 2, _, M => by rw [pow_succ, coeffsIn_mul, coeffsIn_pow, ← pow_succ]; exact n.succ_ne_zero

lemma le_coeffsIn_pow : ∀ {n}, coeffsIn σ M ^ n ≤ coeffsIn σ (M ^ n)
  | 0 => by simpa using ⟨1, map_one _⟩
  | n + 1 => (coeffsIn_pow n.succ_ne_zero _).ge

end Algebra
end coeffsIn

end CommSemiring

end MvPolynomial
