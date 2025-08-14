/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Ring.Action.Rat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FastInstance

/-!
# Theory of univariate polynomials

This file defines `Polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (fun n x ↦ f n x + g n x) = p.sum f + p.sum g`.
* Notation to refer to `Polynomial R`, as `R[X]` or `R[t]`.

## Implementation

Polynomials are defined using `R[ℕ]`, where `R` is a semiring.
The variable `X` commutes with every polynomial `p`: lemma `X_mul` proves the identity
`X * p = p * X`.  The relationship to `R[ℕ]` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `AddMonoidAlgebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `R[X]` and `R[ℕ]` is
done through `ofFinsupp` and `toFinsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `R[ℕ]`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `Polynomial.toFinsuppIso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

noncomputable section

/-- `Polynomial R` is the type of univariate polynomials over `R`,
denoted as `R[X]` within the `Polynomial` namespace.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

theorem forall_iff_forall_finsupp (P : R[X] → Prop) :
    (∀ p, P p) ↔ ∀ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : R[X] → Prop) :
    (∃ p, P p) ↔ ∃ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by constructor

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {R : Type u} [Ring R] : R[X] → R[X]
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance zero : Zero R[X] :=
  ⟨⟨0⟩⟩

instance one : One R[X] :=
  ⟨⟨1⟩⟩

instance add' : Add R[X] :=
  ⟨add⟩

instance neg' {R : Type u} [Ring R] : Neg R[X] :=
  ⟨neg⟩

instance sub {R : Type u} [Ring R] : Sub R[X] :=
  ⟨fun a b => a + -b⟩

instance mul' : Mul R[X] :=
  ⟨mul⟩

-- If the private definitions are accidentally exposed, simplify them away.
@[simp] theorem add_eq_add : add p q = p + q := rfl
@[simp] theorem mul_eq_mul : mul p q = p * q := rfl

instance instNSMul : SMul ℕ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

instance smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul r p := ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

instance {S : Type*} [Zero S] [SMulZeroClass S R] [NoZeroSMulDivisors S R] :
    NoZeroSMulDivisors S R[X] where
  eq_zero_or_eq_zero_of_smul_eq_zero eq :=
    (eq_zero_or_eq_zero_of_smul_eq_zero <| congr_arg toFinsupp eq).imp id (congr_arg ofFinsupp)

-- to avoid a bug in the `ring` tactic
instance (priority := 1) pow : Pow R[X] ℕ where pow p n := npowRec n p

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 :=
  rfl

@[simp]
theorem ofFinsupp_one : (⟨1⟩ : R[X]) = 1 :=
  rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add_def]

@[simp]
theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
  show _ = neg _ by rw [neg_def]

@[simp]
theorem ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofFinsupp_add, ofFinsupp_neg]
  rfl

@[simp]
theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by rw [mul_def]

@[simp]
theorem ofFinsupp_nsmul (a : ℕ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem ofFinsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]
theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 :=
  rfl

@[simp]
theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 :=
  rfl

@[simp]
theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp := by
  cases a
  rw [← ofFinsupp_neg]

@[simp]
theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg, ← toFinsupp_neg, ← toFinsupp_add]
  rfl

@[simp]
theorem toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_mul]

@[simp]
theorem toFinsupp_nsmul (a : ℕ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  cases a
  rw [← ofFinsupp_pow]

theorem _root_.IsSMulRegular.polynomial {S : Type*} [SMulZeroClass S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| ha.finsupp (Polynomial.ofFinsupp.inj h)

theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] → AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]
theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

/-- A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]

instance inhabited : Inhabited R[X] :=
  ⟨0⟩

instance instNatCast : NatCast R[X] where natCast n := ofFinsupp n

@[simp]
theorem ofFinsupp_natCast (n : ℕ) : (⟨n⟩ : R[X]) = n := rfl

@[simp]
theorem toFinsupp_natCast (n : ℕ) : (n : R[X]).toFinsupp = n := rfl

@[simp]
theorem ofFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n) := rfl

@[simp]
theorem toFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]).toFinsupp = ofNat(n) := rfl

instance semiring : Semiring R[X] :=
  fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ => rfl

instance distribSMul {S} [DistribSMul S R] : DistribSMul S R[X] :=
  fast_instance% Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

instance distribMulAction {S} [Monoid S] [DistribMulAction S R] : DistribMulAction S R[X] :=
  fast_instance% Function.Injective.distribMulAction
    ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

instance faithfulSMul {S} [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul {_s₁ _s₂} h :=
    eq_of_smul_eq_smul fun a : ℕ →₀ R => congr_arg toFinsupp (h ⟨a⟩)

instance module {S} [Semiring S] [Module S R] : Module S R[X] :=
  fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

instance smulCommClass {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
    SMulCommClass S₁ S₂ R[X] :=
  ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩

instance isScalarTower {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X] :=
  ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩

instance isScalarTower_right {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalarTower α K K] :
    IsScalarTower α K[X] K[X] :=
  ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩

instance isCentralScalar {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
    IsCentralScalar S R[X] :=
  ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

instance unique [Subsingleton R] : Unique R[X] :=
  { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      apply congr_arg ofFinsupp
      simp [eq_iff_true_of_subsingleton] }

variable (R)

/-- Ring isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps apply symm_apply]
def toFinsuppIso : R[X] ≃+* R[ℕ] where
  toFun := toFinsupp
  invFun := ofFinsupp
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add

instance [DecidableEq R] : DecidableEq R[X] :=
  @Equiv.decidableEq R[X] _ (toFinsuppIso R).toEquiv (Finsupp.instDecidableEq)

/-- Linear isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
def toFinsuppIsoLinear : R[X] ≃ₗ[R] R[ℕ] where
  __ := toFinsuppIso R
  map_smul' _ _ := rfl

end AddMonoidAlgebra

theorem ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[ℕ]) :
    (⟨∑ i ∈ s, f i⟩ : R[X]) = ∑ i ∈ s, ⟨f i⟩ :=
  map_sum (toFinsuppIso R).symm f s

theorem toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i : R[X]).toFinsupp = ∑ i ∈ s, (f i).toFinsupp :=
  map_sum (toFinsuppIso R) f s

/-- The set of all `n` such that `X^n` has a non-zero coefficient. -/
def support : R[X] → Finset ℕ
  | ⟨p⟩ => p.support

@[simp]
theorem support_ofFinsupp (p) : support (⟨p⟩ : R[X]) = p.support := by rw [support]

theorem support_toFinsupp (p : R[X]) : p.toFinsupp.support = p.support := by rw [support]

@[simp]
theorem support_zero : (0 : R[X]).support = ∅ :=
  rfl

@[simp]
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [support]

@[simp] lemma support_nonempty : p.support.Nonempty ↔ p ≠ 0 :=
  Finset.nonempty_iff_ne_empty.trans support_eq_empty.not

theorem card_support_eq_zero : #p.support = 0 ↔ p = 0 := by simp

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] where
  toFun t := ⟨Finsupp.single n t⟩
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp`.
  map_add' x y := by simp; rw [ofFinsupp_add]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [← ofFinsupp_smul]`.
  map_smul' r x := by simp; rw [← ofFinsupp_smul, smul_single']

@[simp]
theorem toFinsupp_monomial (n : ℕ) (r : R) : (monomial n r).toFinsupp = Finsupp.single n r := by
  simp [monomial]

@[simp]
theorem ofFinsupp_single (n : ℕ) (r : R) : (⟨Finsupp.single n r⟩ : R[X]) = monomial n r := by
  simp [monomial]

@[simp]
theorem monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 :=
  (monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl

-- TODO: can't we just delete this one?
theorem monomial_add (n : ℕ) (r s : R) : monomial n (r + s) = monomial n r + monomial n s :=
  (monomial n).map_add _ _

theorem monomial_mul_monomial (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * s) :=
  toFinsupp_injective <| by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r ^ k = monomial (n * k) (r ^ k) := by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]

theorem smul_monomial {S} [SMulZeroClass S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  toFinsupp_injective <| AddMonoidAlgebra.smul_single _ _ _

theorem monomial_injective (n : ℕ) : Function.Injective (monomial n : R → R[X]) :=
  (toFinsuppIso R).symm.injective.comp (single_injective n)

@[simp]
theorem monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

theorem monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← toFinsupp_inj, toFinsupp_monomial, toFinsupp_monomial, Finsupp.single_eq_single_iff]

theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support] using Finsupp.support_add

/-- `C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]
theorem monomial_zero_left (a : R) : monomial 0 a = C a :=
  rfl

@[simp]
theorem toFinsupp_C (a : R) : (C a).toFinsupp = single 0 a :=
  rfl

theorem C_0 : C (0 : R) = 0 := by simp

theorem C_1 : C (1 : R) = 1 :=
  rfl

theorem C_mul : C (a * b) = C a * C b :=
  C.map_mul a b

theorem C_add : C (a + b) = C a + C b :=
  C.map_add a b

@[simp]
theorem smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r

theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n

theorem C_eq_natCast (n : ℕ) : C (n : R) = (n : R[X]) :=
  map_natCast C n

@[simp]
theorem C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]
theorem monomial_mul_C : monomial n a * C b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] :=
  monomial 1 1

theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl

theorem monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]
theorem toFinsupp_X : X.toFinsupp = Finsupp.single 1 (1 : R) :=
  rfl

theorem X_ne_C [Nontrivial R] (a : R) : X ≠ C a := by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
theorem X_mul : X * p = p * X := by
  rcases p with ⟨⟩
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.mul_apply, add_comm]

theorem X_pow_mul {n : ℕ} : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ]

/-- Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `Polynomial.X_mul`. -/
@[simp]
theorem X_mul_C (r : R) : X * C r = C r * X :=
  X_mul

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`. -/
@[simp]
theorem X_pow_mul_C (r : R) (n : ℕ) : X ^ n * C r = C r * X ^ n :=
  X_pow_mul

theorem X_pow_mul_assoc {n : ℕ} : p * X ^ n * q = p * q * X ^ n := by
  rw [mul_assoc, X_pow_mul, ← mul_assoc]

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`. -/
@[simp]
theorem X_pow_mul_assoc_C {n : ℕ} (r : R) : p * X ^ n * C r = p * C r * X ^ n :=
  X_pow_mul_assoc

theorem commute_X (p : R[X]) : Commute X p :=
  X_mul

theorem commute_X_pow (p : R[X]) (n : ℕ) : Commute (X ^ n) p :=
  X_pow_mul

@[simp]
theorem monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [X, monomial_mul_monomial, mul_one]

@[simp]
theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) :
    monomial n r * X ^ k = monomial (n + k) r := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]
theorem X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n + 1) r := by
  rw [X_mul, monomial_mul_X]

@[simp]
theorem X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n + k) r := by
  rw [X_pow_mul, monomial_mul_X_pow]

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
def coeff : R[X] → ℕ → R
  | ⟨p⟩ => p

@[simp]
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p := by rw [coeff]

theorem coeff_injective : Injective (coeff : R[X] → ℕ → R) := by
  rintro ⟨p⟩ ⟨q⟩
  simp only [coeff, DFunLike.coe_fn_eq, imp_self, ofFinsupp.injEq]

@[simp]
theorem coeff_inj : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff

theorem toFinsupp_apply (f : R[X]) (i) : f.toFinsupp i = f.coeff i := by cases f; rfl

theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 := by
  simp [coeff, Finsupp.single_apply]

@[simp]
theorem coeff_monomial_same (n : ℕ) (c : R) : (monomial n c).coeff n = c :=
  Finsupp.single_eq_same

theorem coeff_monomial_of_ne {m n : ℕ} (c : R) (h : n ≠ m) : (monomial n c).coeff m = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
theorem coeff_zero (n : ℕ) : coeff (0 : R[X]) n = 0 :=
  rfl

theorem coeff_one {n : ℕ} : coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]
theorem coeff_one_zero : coeff (1 : R[X]) 0 = 1 := by
  simp [coeff_one]

@[simp]
theorem coeff_X_one : coeff (X : R[X]) 1 = 1 :=
  coeff_monomial

@[simp]
theorem coeff_X_zero : coeff (X : R[X]) 0 = 0 :=
  coeff_monomial

@[simp]
theorem coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

theorem coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 :=
  coeff_monomial

theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : R[X]) n = 0 := by
  rw [coeff_X, if_neg hn.symm]

@[simp]
theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  rcases p with ⟨⟩
  simp

theorem notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

@[deprecated (since := "2025-05-23")] alias not_mem_support_iff := notMem_support_iff

theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial

theorem coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[simp]
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
theorem coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0 := by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[simp]
theorem coeff_ofNat_zero (a : ℕ) [a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) 0 = ofNat(a) :=
  coeff_monomial

@[simp]
theorem coeff_ofNat_succ (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : R[X]) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

theorem C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial, mul_one]

@[simp high]
theorem toFinsupp_C_mul_X_pow (a : R) (n : ℕ) :
    Polynomial.toFinsupp (C a * X ^ n) = Finsupp.single n a := by
  rw [C_mul_X_pow_eq_monomial, toFinsupp_monomial]

theorem C_mul_X_eq_monomial : C a * X = monomial 1 a := by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]
theorem toFinsupp_C_mul_X (a : R) : Polynomial.toFinsupp (C a * X) = Finsupp.single 1 a := by
  rw [C_mul_X_eq_monomial, toFinsupp_monomial]

theorem C_injective : Injective (C : R → R[X]) :=
  monomial_injective 0

@[simp]
theorem C_inj : C a = C b ↔ a = b :=
  C_injective.eq_iff

@[simp]
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  C_injective.eq_iff' (map_zero C)

theorem C_ne_zero : C a ≠ 0 ↔ a ≠ 0 :=
  C_eq_zero.not

theorem subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R :=
  ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩

theorem Nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R :=
  (subsingleton_or_nontrivial R).resolve_left fun _hI => h <| Subsingleton.elim _ _

theorem forall_eq_iff_forall_eq : (∀ f g : R[X], f = g) ↔ ∀ a b : R, a = b := by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨f : ℕ →₀ R⟩
  rcases q with ⟨g : ℕ →₀ R⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]
theorem ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
  ext_iff.2

/-- Monomials generate the additive monoid of polynomials. -/
theorem addSubmonoid_closure_setOf_eq_monomial :
    AddSubmonoid.closure { p : R[X] | ∃ n a, p = monomial n a } = ⊤ := by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv, ←
    Finsupp.add_closure_setOf_eq_single, AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOf_eq_monomial <| by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]
theorem addHom_ext' {M : Type*} [AddZeroClass M] {f g : R[X] →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  addHom_ext fun n => DFunLike.congr_fun (h n)

@[ext high]
theorem lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] →ₗ[R] M}
    (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext fun n => LinearMap.congr_fun (h n)

-- this has the same content as the subsingleton
theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Fewnomials

theorem support_monomial (n) {a : R} (H : a ≠ 0) : (monomial n a).support = singleton n := by
  rw [← ofFinsupp_single, support]; exact Finsupp.support_single_ne_zero _ H

theorem support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n := by
  rw [← ofFinsupp_single, support]
  exact Finsupp.support_single_subset

theorem support_C {a : R} (h : a ≠ 0) : (C a).support = singleton 0 :=
  support_monomial 0 h

theorem support_C_subset (a : R) : (C a).support ⊆ singleton 0 :=
  support_monomial' 0 a

theorem support_C_mul_X {c : R} (h : c ≠ 0) : Polynomial.support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]

theorem support_C_mul_X' (c : R) : Polynomial.support (C c * X) ⊆ singleton 1 := by
  simpa only [C_mul_X_eq_monomial] using support_monomial' 1 c

theorem support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) :
    Polynomial.support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]

theorem support_C_mul_X_pow' (n : ℕ) (c : R) : Polynomial.support (C c * X ^ n) ⊆ singleton n := by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial' n c

open Finset

theorem support_binomial' (k m : ℕ) (x y : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow' m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

theorem support_trinomial' (k m n : ℕ) (x y z : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
  support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow' m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((support_C_mul_X_pow' n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

end Fewnomials

theorem X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R) := by
  induction n with
  | zero => rw [pow_zero, monomial_zero_one]
  | succ n hn => rw [pow_succ, hn, X, monomial_mul_monomial, one_mul]

@[simp high]
theorem toFinsupp_X_pow (n : ℕ) : (X ^ n).toFinsupp = Finsupp.single n (1 : R) := by
  rw [X_pow_eq_monomial, toFinsupp_monomial]

theorem smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R) := by
  rw [X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]

theorem support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (X ^ n : R[X]).support = singleton n := by
  convert support_monomial n H
  exact X_pow_eq_monomial n

theorem support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

theorem support_X (H : ¬(1 : R) = 0) : (X : R[X]).support = singleton 1 := by
  rw [← pow_one X, support_X_pow H 1]

theorem monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} :
    monomial i a = monomial j a ↔ i = j := by
  simp only [← ofFinsupp_single, ofFinsupp.injEq, Finsupp.single_left_inj ha]

theorem binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
    C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n := by
  simp_rw [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, toFinsupp_add, toFinsupp_monomial]
  exact Finsupp.single_add_single_eq_single_add_single hu hv

theorem natCast_mul (n : ℕ) (p : R[X]) : (n : R[X]) * p = n • p :=
  (nsmul_eq_mul _ _).symm

/-- Summing the values of a function applied to the coefficients of a polynomial -/
def sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) : S :=
  ∑ n ∈ p.support, f n (p.coeff n)

theorem sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) :=
  rfl

theorem sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) {s : Finset ℕ} (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

/-- Expressing the product of two polynomials as a double sum. -/
theorem mul_eq_sum_sum :
    p * q = ∑ i ∈ p.support, q.sum fun j a => (monomial (i + j)) (p.coeff i * a) := by
  apply toFinsupp_injective
  rcases p with ⟨⟩; rcases q with ⟨⟩
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]
theorem sum_zero_index {S : Type*} [AddCommMonoid S] (f : ℕ → R → S) : (0 : R[X]).sum f = 0 := by
  simp [sum]

@[simp]
theorem sum_monomial_index {S : Type*} [AddCommMonoid S] {n : ℕ} (a : R) (f : ℕ → R → S)
    (hf : f n 0 = 0) : (monomial n a : R[X]).sum f = f n a :=
  Finsupp.sum_single_index hf

@[simp]
theorem sum_C_index {a} {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
    (C a).sum f = f 0 a :=
  sum_monomial_index a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp]
theorem sum_X_index {S : Type*} [AddCommMonoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (X : R[X]).sum f = f 1 1 :=
  sum_monomial_index 1 f hf

theorem sum_add_index {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ from add_def p q]
  exact Finsupp.sum_add_index (fun i _ ↦ hf i) (fun a _ b₁ b₂ ↦ h_add a b₁ b₂)

theorem sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [sum_def, Finset.sum_add_distrib]

theorem sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

theorem sum_smul_index {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b * a) :=
  Finsupp.sum_smul_index hf

theorem sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
    (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) :=
  Finsupp.sum_smul_index' hf

protected theorem smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a => b • f n a :=
  Finsupp.smul_sum

@[simp]
theorem sum_monomial_eq : ∀ p : R[X], (p.sum fun n a => monomial n a) = p
  | ⟨_p⟩ => (ofFinsupp_sum _ _).symm.trans (congr_arg _ <| Finsupp.sum_single _)

theorem sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a => C a * X ^ n) = p := by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]
protected theorem induction_on {motive : R[X] → Prop} (p : R[X]) (C : ∀ a, motive (C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (monomial : ∀ (n : ℕ) (a : R),
      motive (Polynomial.C a * X ^ n) → motive (Polynomial.C a * X ^ (n + 1))) : motive p := by
  have A : ∀ {n : ℕ} {a}, motive (Polynomial.C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact C a
    | succ n ih => exact monomial _ _ ih
  have B : ∀ s : Finset ℕ, motive (s.sum fun n : ℕ => Polynomial.C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (support p)

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {motive : R[X] → Prop} (p : R[X])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (monomial : ∀ (n : ℕ) (a : R), motive (monomial n a)) : motive p :=
  Polynomial.induction_on p (monomial 0) add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact monomial _ _

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
irreducible_def erase (n : ℕ) : R[X] → R[X]
  | ⟨p⟩ => ⟨p.erase n⟩

@[simp]
theorem toFinsupp_erase (p : R[X]) (n : ℕ) : toFinsupp (p.erase n) = p.toFinsupp.erase n := by
  rcases p with ⟨⟩
  simp only [erase_def]

@[simp]
theorem ofFinsupp_erase (p : R[ℕ]) (n : ℕ) :
    (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X]).erase n := by
  rcases p with ⟨⟩
  simp only [erase_def]

@[simp]
theorem support_erase (p : R[X]) (n : ℕ) : support (p.erase n) = (support p).erase n := by
  rcases p with ⟨⟩
  simp only [support, erase_def, Finsupp.support_erase]

theorem monomial_add_erase (p : R[X]) (n : ℕ) : monomial n (coeff p n) + p.erase n = p :=
  toFinsupp_injective <| by
    rcases p with ⟨⟩
    rw [toFinsupp_add, toFinsupp_monomial, toFinsupp_erase, coeff]
    exact Finsupp.single_add_erase _ _

theorem coeff_erase (p : R[X]) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  rcases p with ⟨⟩
  simp only [erase_def, coeff]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[simp]
theorem erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 :=
  toFinsupp_injective <| by simp

@[simp]
theorem erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
  toFinsupp_injective <| by simp

@[simp]
theorem erase_same (p : R[X]) (n : ℕ) : coeff (p.erase n) n = 0 := by simp [coeff_erase]

@[simp]
theorem erase_ne (p : R[X]) (n i : ℕ) (h : i ≠ n) : coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

section Update

/-- Replace the coefficient of a `p : R[X]` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`. -/
def update (p : R[X]) (n : ℕ) (a : R) : R[X] :=
  Polynomial.ofFinsupp (p.toFinsupp.update n a)

theorem coeff_update (p : R[X]) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by
  ext
  cases p
  simp only [coeff, update, Function.update_apply, coe_update]

theorem coeff_update_apply (p : R[X]) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i := by
  rw [coeff_update, Function.update_apply]

@[simp]
theorem coeff_update_same (p : R[X]) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, if_pos rfl]

theorem coeff_update_ne (p : R[X]) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, if_neg h]

@[simp]
theorem update_zero_eq_erase (p : R[X]) (n : ℕ) : p.update n 0 = p.erase n := by
  ext
  rw [coeff_update_apply, coeff_erase]

theorem support_update (p : R[X]) (n : ℕ) (a : R) [Decidable (a = 0)] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  classical
    cases p
    simp only [support, update, Finsupp.support_update]
    congr

theorem support_update_zero (p : R[X]) (n : ℕ) : support (p.update n 0) = p.support.erase n := by
  rw [update_zero_eq_erase, support_erase]

theorem support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, if_neg ha]

end Update

/-- The finset of nonzero coefficients of a polynomial. -/
def coeffs (p : R[X]) : Finset R :=
  letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support

@[simp]
theorem coeffs_zero : coeffs (0 : R[X]) = ∅ :=
  rfl

theorem mem_coeffs_iff {p : R[X]} {c : R} : c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]

theorem coeffs_one : coeffs (1 : R[X]) ⊆ {1} := by
  classical
  simp_rw [coeffs, Finset.image_subset_iff]
  simp_all [coeff_one]

theorem coeff_mem_coeffs (p : R[X]) (n : ℕ) (h : p.coeff n ≠ 0) : p.coeff n ∈ p.coeffs := by
  classical
  simp only [coeffs, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

@[simp]
theorem coeffs_empty_iff (p : R[X]) : coeffs p = ∅ ↔ p = 0 := by
  refine ⟨?_, fun h ↦ by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [mem_support_iff] at hn
  rw [← nonempty_iff_ne_empty]
  exact ⟨p.coeff n, coeff_mem_coeffs p n hn⟩

theorem coeffs_monomial (n : ℕ) {c : R} (hc : c ≠ 0) : (monomial n c).coeffs = {c} := by
  rw [coeffs, support_monomial n hc]
  simp

end Semiring

section CommSemiring

variable [CommSemiring R]

instance commSemiring : CommSemiring R[X] :=
  fast_instance% { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

end CommSemiring

section Ring

variable [Ring R]

instance instZSMul : SMul ℤ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

@[simp]
theorem ofFinsupp_zsmul (a : ℤ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem toFinsupp_zsmul (a : ℤ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

instance instIntCast : IntCast R[X] where intCast n := ofFinsupp n

@[simp]
theorem ofFinsupp_intCast (z : ℤ) : (⟨z⟩ : R[X]) = z := rfl

@[simp]
theorem toFinsupp_intCast (z : ℤ) : (z : R[X]).toFinsupp = z := rfl

instance ring : Ring R[X] :=
  fast_instance% Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ => toFinsupp_nsmul _ _)
      (fun _ _ => toFinsupp_zsmul _ _) toFinsupp_pow (fun _ => rfl) fun _ => rfl

@[simp]
theorem coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n := by
  rcases p with ⟨⟩
  rw [← ofFinsupp_neg, coeff, coeff, Finsupp.neg_apply]

@[simp]
theorem coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  rw [← ofFinsupp_sub, coeff, coeff, coeff, Finsupp.sub_apply]

@[simp]
theorem monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -monomial n a := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_cancel, monomial_zero_right]

theorem monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, monomial_add, monomial_neg, sub_eq_add_neg]

@[simp]
theorem support_neg {p : R[X]} : (-p).support = p.support := by
  rcases p with ⟨⟩
  rw [← ofFinsupp_neg, support, support, Finsupp.support_neg]

theorem C_eq_intCast (n : ℤ) : C (n : R) = n := by simp

theorem C_neg : C (-a) = -C a :=
  RingHom.map_neg C a

theorem C_sub : C (a - b) = C a - C b :=
  RingHom.map_sub C a b

end Ring

instance commRing [CommRing R] : CommRing R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }

section Semiring

variable [Semiring R]

instance nontrivial [Nontrivial R] : Nontrivial R[X] := by
  have h : Nontrivial R[ℕ] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : R[X]) ≠ 0 :=
  mt (congr_arg fun p => coeff p 1) (by simp)

instance [NoZeroDivisors R] : NoZeroDivisors R[X] :=
  (toFinsuppIso R).injective.noZeroDivisors _ (map_zero _) (map_mul _)

instance [IsCancelAdd R] [IsLeftCancelMulZero R] : IsLeftCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

instance [IsCancelAdd R] [IsRightCancelMulZero R] : IsRightCancelMulZero R[X] :=
  (toFinsuppIso R).injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R[X] where

instance [IsCancelAdd R] [IsDomain R] : IsDomain R[X] where

end Semiring

section DivisionSemiring
variable [DivisionSemiring R]

lemma nnqsmul_eq_C_mul (q : ℚ≥0) (f : R[X]) : q • f = Polynomial.C (q : R) * f := by
  rw [← NNRat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionSemiring

section DivisionRing

variable [DivisionRing R]

theorem qsmul_eq_C_mul (a : ℚ) (f : R[X]) : a • f = Polynomial.C (a : R) * f := by
  rw [← Rat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionRing

@[simp]
theorem nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R :=
  ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

section repr

variable [Semiring R]

protected instance repr [Repr R] [DecidableEq R] : Repr R[X] :=
  ⟨fun p prec =>
    let termPrecAndReprs : List (WithTop ℕ × Lean.Format) :=
      List.map (fun
        | 0 => (max_prec, "C " ++ reprArg (coeff p 0))
        | 1 => if coeff p 1 = 1
          then (⊤, "X")
          else (70, "C " ++ reprArg (coeff p 1) ++ " * X")
        | n =>
          if coeff p n = 1
          then (80, "X ^ " ++ Nat.repr n)
          else (70, "C " ++ reprArg (coeff p n) ++ " * X ^ " ++ Nat.repr n))
      (p.support.sort (· ≤ ·))
    match termPrecAndReprs with
    | [] => "0"
    | [(tprec, t)] => if prec ≥ tprec then Lean.Format.paren t else t
    | ts =>
      -- multiple terms, use `+` precedence
      (if prec ≥ 65 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep (ts.map Prod.snd) (" +" ++ Lean.Format.line)))⟩

end repr

end Polynomial
