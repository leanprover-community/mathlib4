/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.HahnSeries

/-!
# Vertex algebras

In this file we introduce vertex algebras using Hahn series.

## Definitions

* VertexOperator : This is an `R`-linear map from an `R`-module `V` to `HahnSeries ℤ V`.
* NonAssocNonUnitalVertexAlgebra : This is an `R`-module `V` with multiplication `V ⊗ V → V((z))`.
* Borcherds identity sums: These are more or less composites of vertex operators.
* Various identities: Borcherds, commutator, locality, associativity, skew-symmetry.
* NonUnitalVertexAlgebra: A NonAssocNonUnitalVertexAlgebra satisfying Borcherds identity.
* VertexAlgebra: A NonUnitalVertexAlgebra with One, satisfying a right identity rule.

## Main results

* Vertex operators form an `R`-module.

We postpone the proofs of equivalences of various identities to Mathlib.Algebra.Vertex.Basic.

## To do:

* Clean up instances - apparently Mathlib.Logic.Equiv.TransferInstance can help.  Maybe just use
abbrev.

* One (VertexOperator R V) instance with identity field.

* residue products, order of associativity, weak associativity

* Divided power derivatives of fields

* Fix locality and weak associativity defs

* cofiniteness conditions?

## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118

-/

set_option autoImplicit false

universe u v

variable {V : Type*} {R : Type*}

section VertexOperator

/-- A vertex operator over a semiring `R` is an `R`-linear map from an `R`-module `V` to Laurent
series with coefficients in `V`. -/
@[ext]
structure VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
/-- The underlying structure map of a vertex operator. -/
  toMap : V →ₗ[R] HahnSeries ℤ V

namespace VertexAlg

theorem VertexOperator_equiv_LinearMap (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] : VertexOperator R V ≃ (V →ₗ[R] HahnSeries ℤ V) := by
  use VertexOperator.toMap
  exact fun a ↦ { toMap := a }
  exact congrFun rfl
  exact congrFun rfl

instance LinearMapClass (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    LinearMapClass (VertexOperator R V) R V (HahnSeries ℤ V) where
  coe f := f.toMap
  coe_injective' f g h := by
    rw [@VertexOperator.ext_iff]
    rw [@LinearMap.ext_iff]
    intro x
    exact congrFun h x
  map_add := by
    intros
    simp only [map_add]
  map_smulₛₗ := by
    intros
    simp only [map_smul, RingHom.id_apply]

/-!
example {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm

LinearMap instances:
* `LinearMap.AddCommGroup` and `LinearMap.addCommGroup`: the elementwise addition structures
  corresponding to addition in the codomain
* `LinearMap.distribMulAction` and `LinearMap.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.

-/

/-- The coefficient of a vertex operator, viewed as a formal power series with coefficients in
linear endomorphisms. -/
def coeff [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V :=
  {
    toFun := fun (x : V) => (A.toMap x).coeff n
    map_add' := by simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
    map_smul' := by simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
  }

/-- We write `index` instead of `coefficient of a vertex operator under normalized indexing`.
Alternative suggestions welcome. -/
def index [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := coeff A (-n-1)

theorem index_eq_coeff_neg [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V)
    (n : ℤ) : index A n = coeff A (-n-1) := rfl

/-- The normal convention for the normalized coefficient of a vertex operator is either `Aₙ` or
`A(n)`.  Either choice seems to break things. -/
scoped[VertexAlg] notation A "⁅" n "⁆" => index A n

instance [CommRing R] [AddCommGroup V] [Module R V] : Zero (VertexOperator R V) :=
-- How do I use Equiv.zero_def (VertexOperator_equiv_LinearMap R V)???
  {
  zero :=
    {
    toMap :=
      {
        toFun := fun (_ : V) => (0 : HahnSeries ℤ V)
        map_add' := by simp only [add_zero, forall_const]
        map_smul' := by simp only [RingHom.id_apply, smul_zero, forall_const]
      }
    }
  }

/-!
instance [AddCommGroup R] : AddCommGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      apply add_comm }
-/

@[simp] lemma zero_toFun [CommRing R] [AddCommGroup V] [Module R V] (x : V) :
  (0 : VertexOperator R V).toMap x = 0 := rfl

@[simp] lemma zero_coeff [CommRing R] [AddCommGroup V] [Module R V] (n : ℤ) :
    coeff (0 : VertexOperator R V) n = 0 := by
  exact rfl

@[simp] lemma zero_index [CommRing R] [AddCommGroup V] [Module R V] (n : ℤ) :
    (0 : VertexOperator R V) ⁅n⁆ = 0 := by
  exact rfl

instance [CommRing R] [AddCommGroup V] [Module R V] : Add (VertexOperator R V) :=--inferInstance?
  {
    add := fun A B =>
      {
      toMap :=
        {
        toFun := fun x => A.toMap x + B.toMap x
        map_add' := by
          intros
          simp only [map_add]
          rw [@add_add_add_comm]
        map_smul' := by
          simp only [map_smul, RingHom.id_apply, smul_add, forall_const]
        }
      }
  }

@[simp] lemma add_toMap_eq [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)
  (x : V): (A + B).toMap x = A.toMap x + B.toMap x := rfl

@[simp] lemma add_coeff_eq [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)
  (n : ℤ) : coeff (A + B) n = coeff A n + coeff B n := by exact rfl

@[simp] lemma add_index_eq [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)
  (n : ℤ) : (A + B) ⁅n⁆ = A ⁅n⁆ + B ⁅n⁆ := by exact rfl

noncomputable instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) :=
  {
    one :=
    {
      toMap := -- can I use HahnSeries.single.addMonoidHom ???
      {
        toFun := fun x => HahnSeries.single 0 x
        map_add' := by
          intro x y
          unfold HahnSeries.single Pi.single Function.update
          simp only [eq_rec_constant, Pi.zero_apply, dite_eq_ite, ZeroHom.coe_mk,
            HahnSeries.ext_iff, HahnSeries.add_coeff']
          refine Function.funext_iff.mpr ?_
          intro a
          cases a with
          | ofNat n =>
            cases n with
            | zero =>
              simp only [Nat.zero_eq, Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, ite_true, Pi.add_apply]
            | succ n =>
              simp only [Int.ofNat_eq_coe, Nat.cast_succ, Pi.add_apply]
              exact ite_add_zero
          | negSucc _ =>
            simp_all only [Int.negSucc_ne_zero, ite_false, Pi.add_apply, add_zero]
        map_smul' := by
          intro r x
          unfold HahnSeries.single Pi.single Function.update
          simp only [eq_rec_constant, Pi.zero_apply, dite_eq_ite, ZeroHom.coe_mk, RingHom.id_apply]
          aesop
      }
    }
  }

/-!
This should be V →ₗ[R] HahnSeries Γ V !!!

variable [PartialOrder Γ] [Semiring R] {V : Type*} [AddCommMonoid V] [Module R V]

@[simps]
def single.linearMap (a : Γ) : R →ₗ[R] HahnSeries Γ R :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

-/
instance [CommRing R] [AddCommGroup V] [Module R V] : Neg (VertexOperator R V) :=
  {
    neg := fun A =>
    {
    toMap :=
      {
      toFun := fun x => - A.toMap x
      map_add' := by
        intros
        simp only [map_add, neg_add_rev]
        rw [add_comm]
      map_smul' := by
        intros
        simp only [map_smul, RingHom.id_apply, smul_neg]
      }
    }
  }

@[simp] lemma neg_toMap_eq [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V)
    (x : V): (-A).toMap x = - A.toMap x := rfl

-- can I use LinearMap.AddCommGroup here?  On Zulip, Equiv was recommended.
instance [CommRing R] [AddCommGroup V] [Module R V] : AddCommGroup (VertexOperator R V) :=
  {
    add_assoc := by
      intros
      ext x n
      simp only [add_toMap_eq, HahnSeries.add_coeff, add_assoc]
    zero_add := by
      intros
      ext x n
      simp only [add_toMap_eq, zero_toFun, HahnSeries.add_coeff, HahnSeries.zero_coeff, zero_add]
    add_zero := by
      intros
      ext x n
      simp only [add_toMap_eq, zero_toFun, HahnSeries.add_coeff, HahnSeries.zero_coeff, add_zero]
    add_comm := by
      intros
      ext x n
      simp only [add_toMap_eq, HahnSeries.add_coeff, add_comm]
    add_left_neg := by
      intros
      ext x n
      simp only [add_toMap_eq, neg_toMap_eq, add_left_neg, HahnSeries.zero_coeff, zero_toFun]
  }

instance [CommRing R] [AddCommGroup V] [Module R V] : SMul R (VertexOperator R V) :=
  { smul := fun r A =>
    {toMap :=
      {
        toFun := fun x => r • A.toMap x
        map_add' := by
          intros
          ext n
          simp only [map_add, smul_add, HahnSeries.add_coeff', Pi.add_apply, HahnSeries.smul_coeff]
        map_smul' := by
          intros
          ext n
          simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply]
          rw [@smul_algebra_smul_comm]
      }
    }
  }

@[simp] lemma smul_toMap_eq [CommRing R] [AddCommGroup V] [Module R V] (r : R)
    (A : VertexOperator R V) (x : V): (r • A).toMap x = r • A.toMap x := rfl

@[simp] lemma smul_coeff_eq [CommRing R] [AddCommGroup V] [Module R V] (r : R)
  (A : VertexOperator R V) (n : ℤ) : coeff (r • A) n = r • coeff A n := by exact rfl

@[simp] lemma smul_index_eq [CommRing R] [AddCommGroup V] [Module R V] (r : R)
  (A : VertexOperator R V) (n : ℤ) : (r • A) ⁅n⁆ = r • (A ⁅n⁆) := by exact rfl

instance [CommRing R] [AddCommGroup V] [Module R V] : Module R (VertexOperator R V) :=
  {
    smul := VertexAlg.instSMulVertexOperator.smul
    one_smul := by
      intros
      ext x n
      simp only [smul_toMap_eq, one_smul]
    mul_smul := by
      intros
      ext x n
      simp only [smul_toMap_eq, HahnSeries.smul_coeff, mul_smul]
    smul_zero := by
      intros
      ext x n
      simp only [smul_toMap_eq, zero_toFun, smul_zero, HahnSeries.zero_coeff]
    smul_add := by
      intros
      ext x n
      simp only [smul_toMap_eq, add_toMap_eq, smul_add, HahnSeries.add_coeff', Pi.add_apply,
        HahnSeries.smul_coeff]
    add_smul := by
      intros
      ext x n
      simp only [smul_toMap_eq, HahnSeries.smul_coeff, add_toMap_eq, HahnSeries.add_coeff',
        Pi.add_apply, add_smul]
    zero_smul := by
      intros
      ext x n
      simp only [smul_toMap_eq, zero_smul, HahnSeries.zero_coeff, zero_toFun]
  }

/-- Locality to order `≤ n` means `(x-y)^N[A(x),B(y)] = 0` for `N ≥ n`.  We may want to write this
in terms of composition of endomorphisms. -/
def isLocalToOrderLeq (R: Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (A B : VertexOperator R V) (n : ℕ) : Prop := ∀ (k l : ℤ) (x : V), Finset.sum
    (Finset.antidiagonal n) (fun m => (-1)^(m.1) • (Nat.choose n m.1) •
    coeff A (k + m.1) (coeff B (l + m.2) x)) = Finset.sum (Finset.antidiagonal n)
    (fun m => (-1)^(m.1) • (Nat.choose n m.1) • coeff B (l + m.1) (coeff A (k + m.2) x))

/-- Two fields are local if they are local to order `≤ n` for some `n`. -/
def isLocal (R: Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (A B : VertexOperator R V) : Prop := ∃(n : ℕ), isLocalToOrderLeq R V A B n



/-!

Put Hasse derivatives of Hahn Series in the Binomial Ring file?
We need exponents in a partially ordered binomial ring.
The `k`th Hasse derivative of a HahnSeries `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
Coefficient function is
Need to show that support is pwo.

Then, define `hasseDeriv k A` for Vertex operator `A` as `v ↦ hasseDeriv k (A v)`.

/--
It satisfies `k! * (hasseDeriv k f) = derivative^[k] f`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  lsum fun i => monomial (i - k) ∘ₗ DistribMulAction.toLinearMap R R (i.choose k)


/-- The `k`th Hasse derivative of a vertex operator `∑ A_i X^i` is `∑ (i.choose k) A_i X^(i-k)`.
It satisfies `k! * (hasseDeriv k f) = derivative^[k] f`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  lsum fun i => monomial (i - k) ∘ₗ DistribMulAction.toLinearMap R R (i.choose k)


divided-power derivatives of fields
maybe need divided-power derivatives of formal power series with exponents in a binomial ring?

open BigOperators Polynomial

open Function

open Nat hiding nsmul_eq_mul

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
def hasseDeriv (k : ℕ) : R[X] →ₗ[R] R[X] :=
  lsum fun i => monomial (i - k) ∘ₗ DistribMulAction.toLinearMap R R (i.choose k)

theorem hasseDeriv_apply :
    hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  dsimp [hasseDeriv]
  congr; ext; congr
  apply nsmul_eq_mul
#align polynomial.hasse_deriv_apply Polynomial.hasseDeriv_apply

theorem hasseDeriv_coeff (n : ℕ) :
    (hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [hasseDeriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n + k), coeff_monomial]
  · simp only [if_true, add_tsub_cancel_right, eq_self_iff_true]
  · intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · push_neg at hik
      rw [if_neg]
      contrapose! hink
      exact (tsub_eq_iff_eq_add_of_le hik).mp hink
  · intro h
    simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]
#align polynomial.hasse_deriv_coeff Polynomial.hasseDeriv_coeff

theorem hasseDeriv_zero' : hasseDeriv 0 f = f := by
  simp only [hasseDeriv_apply, tsub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    sum_monomial_eq]
#align polynomial.hasse_deriv_zero' Polynomial.hasseDeriv_zero'

@[simp]
theorem hasseDeriv_zero : @hasseDeriv R _ 0 = LinearMap.id :=
  LinearMap.ext <| hasseDeriv_zero'
#align polynomial.hasse_deriv_zero Polynomial.hasseDeriv_zero

theorem hasseDeriv_eq_zero_of_lt_natDegree (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    hasseDeriv n p = 0 := by
  rw [hasseDeriv_apply, sum_def]
  refine' Finset.sum_eq_zero fun x hx => _
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]
#align polynomial.hasse_deriv_eq_zero_of_lt_nat_degree Polynomial.hasseDeriv_eq_zero_of_lt_natDegree

theorem hasseDeriv_one' : hasseDeriv 1 f = derivative f := by
  simp only [hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]
#align polynomial.hasse_deriv_one' Polynomial.hasseDeriv_one'

@[simp]
theorem hasseDeriv_one : @hasseDeriv R _ 1 = derivative :=
  LinearMap.ext <| hasseDeriv_one'
#align polynomial.hasse_deriv_one Polynomial.hasseDeriv_one

@[simp]
theorem hasseDeriv_monomial (n : ℕ) (r : R) :
    hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · rw [if_pos hnik, if_pos, ← hnik]
    apply tsub_eq_of_eq_add_rev
    rwa [add_comm]
  · rw [if_neg hnik, mul_zero]
    by_cases hkn : k ≤ n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · push_neg at hkn
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self]
#align polynomial.hasse_deriv_monomial Polynomial.hasseDeriv_monomial

theorem hasseDeriv_C (r : R) (hk : 0 < k) : hasseDeriv k (C r) = 0 := by
  rw [← monomial_zero_left, hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]
set_option linter.uppercaseLean3 false in
#align polynomial.hasse_deriv_C Polynomial.hasseDeriv_C

theorem hasseDeriv_apply_one (hk : 0 < k) : hasseDeriv k (1 : R[X]) = 0 := by
  rw [← C_1, hasseDeriv_C k _ hk]
#align polynomial.hasse_deriv_apply_one Polynomial.hasseDeriv_apply_one

theorem hasseDeriv_X (hk : 1 < k) : hasseDeriv k (X : R[X]) = 0 := by
  rw [← monomial_one_one_eq_X, hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]
set_option linter.uppercaseLean3 false in
#align polynomial.hasse_deriv_X Polynomial.hasseDeriv_X

theorem factorial_smul_hasseDeriv : ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k] := by
  induction' k with k ih
  · rw [hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  ext f n : 2
  rw [iterate_succ_apply', ← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    hasseDeriv_coeff, ← @choose_symm_add _ k]
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ]
  rw [← (cast_commute (n + 1) (f.coeff (n + k + 1))).eq]
  simp only [← mul_assoc]
  norm_cast
  congr 2
  rw [mul_comm (k+1) _, mul_assoc, mul_assoc]
  congr 1
  have : n + k + 1 = n + (k + 1) := by apply add_assoc
  rw [← choose_symm_of_eq_add this, choose_succ_right_eq, mul_comm]
  congr
  rw [add_assoc, add_tsub_cancel_left]
#align polynomial.factorial_smul_hasse_deriv Polynomial.factorial_smul_hasseDeriv

theorem hasseDeriv_comp (k l : ℕ) :
    (@hasseDeriv R _ k).comp (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) := by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases hikl : i < k + l
  · rw [choose_eq_zero_of_lt hikl, mul_zero]
    by_cases hil : i < l
    · rw [choose_eq_zero_of_lt hil, mul_zero]
    · push_neg at hil
      rw [← tsub_lt_iff_right hil] at hikl
      rw [choose_eq_zero_of_lt hikl, zero_mul]
  push_neg at hikl
  apply @cast_injective ℚ
  have h1 : l ≤ i := le_of_add_le_right hikl
  have h2 : k ≤ i - l := le_tsub_of_add_le_right hikl
  have h3 : k ≤ k + l := le_self_add
  push_cast
  rw [cast_choose ℚ h1, cast_choose ℚ h2, cast_choose ℚ h3, cast_choose ℚ hikl]
  rw [show i - (k + l) = i - l - k by rw [add_comm]; apply tsub_add_eq_tsub_tsub]
  simp only [add_tsub_cancel_left]
  field_simp; ring
#align polynomial.hasse_deriv_comp Polynomial.hasseDeriv_comp

/-- The left sum of the `m`-th residue product `A(z)_n B(z)`, given by the residue of
`(x-y)^m A(x)B(y)` at `|x| > |y|`. -/
def res_prod_left (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  {
    toMap :=
    {
      toFun := sorry
      map_add' := sorry
      map_smul' := sorry
    }
  }

/-- The right sum of the `m`-th residue product `A(z)_n B(z)`, given by the residue of
`(x-y)^m B(y)A(x)` at `|y| > |x|`. -/
def res_prod_right (A B : VertexOperator R V) (m : ℤ)

residue products: to show that the residue product is a vertex operator, we need
-- residue products, order of associativity (uses residue products)

-/

end VertexAlg

end VertexOperator

/-- A non-associative non-unital vertex algebra over a commutative ring `R` is an `R`-module `V`
with a multiplication that takes values in Laurent series with coefficients in `V`. -/
class NonAssocNonUnitalVertexAlgebra (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] extends
    Module R V where
  /-- The multiplication operation in a vertex algebra. -/
  Y: V →ₗ[R] VertexOperator R V

section NonAssocNonUnitalVertexAlgebra

namespace VertexAlg

variable [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]

/-- The multiplication in a vertex algebra. -/
def Y (R : Type*) {V : Type*} [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V] :
    V →ₗ[R] VertexOperator R V := NonAssocNonUnitalVertexAlgebra.Y

theorem Y_add_left_eq (a b : V) : Y R (a + b) = (Y R a) + (Y R b) := by simp only [map_add]

theorem Y_smul_left_eq (r : R) (a : V) : Y R (r • a) = r • Y R a := by simp only [map_smul]

theorem coeff_add_left_eq (a b c : V) (n : ℤ) :
    coeff (Y R (a + b)) n c = coeff (Y R a) n c + coeff (Y R b) n c := by
  simp only [map_add, add_coeff_eq, LinearMap.add_apply]

theorem index_add_left_eq (a b c : V) (n : ℤ) :
    index (Y R (a + b)) n c = index (Y R a) n c + index (Y R b) n c := by
  simp only [map_add, add_index_eq, LinearMap.add_apply]

-- theorem coeff_smul_left_eq
-- theorem index_smul_left_eq

--scoped[VertexAlg] notation a "(" n ")" => index (Y R a) n --seems to fail for any bracket choice.

/-- The order is the smallest integer `n` such that `a ⁅-n-1⁆ b ≠ 0` if `Y a b` is nonzero, and zero
otherwise.  In particular, `a ⁅n⁆ b = 0` for `n ≥ -order a b`. -/
noncomputable def order (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) : ℤ := HahnSeries.order (Y R a b)

theorem coeff_zero_if_lt_order (a b : V) (n : ℤ) (h: n < order R a b) : coeff (Y R a) n b = 0 := by
  rw [order] at h
  simp only [coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_nonzero_at_order (a b : V) (h: Y R a b ≠ 0) : coeff (Y R a) (order R a b) b ≠ 0 := by
  rw [order, coeff]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_order_ne_zero h

theorem index_zero_if_neg_order_leq (a b : V) (n : ℤ) (h: - order R a b ≤ n) :
    index (Y R a) n b = 0 := by
  rw [index_eq_coeff_neg]
  refine coeff_zero_if_lt_order a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem index_nonzero_at_neg_order_minus_one (a b : V) (h: Y R a b ≠ 0) :
    index (Y R a) (-order R a b - 1) b ≠ 0 := by
  rw [index_eq_coeff_neg, neg_sub, sub_neg_eq_add, add_sub_cancel']
  exact coeff_nonzero_at_order a b h

-- Reminder: a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The first sum in the Borcherds identity, giving coefficients of `(a(x)b)(z)c` near `z=y-x`. -/
noncomputable def Borcherds_sum_1 (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-t - order R a b)))
    (fun i ↦ (Ring.choose r i) • index (Y R (index (Y R a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving coefficients of `a(y)b(z)c` near `x=y-z`. -/
noncomputable def Borcherds_sum_2 (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order R b c)))
    (fun i ↦ (-1)^i • (Ring.choose t i) • index (Y R a) (r+t-i) (index (Y R b) (s+i) c))

/-- The third sum in the Borcherds identity, giving coefficients of `b(z)a(y)c` near `-x = z-y`. -/
noncomputable def Borcherds_sum_3 (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order R a c)))
    (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • index (Y R b) (s+t-i) (index (Y R a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable def Borcherds_id (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t

/-- The associativity property of vertex algebras. -/
def associativity (R : Type*) [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) : Prop := ((Y R) (((Y R) a⁅t⁆) b)⁅s⁆) c = Finset.sum (Finset.range
    (Int.toNat (-s - order R b c))) (fun i ↦ (-1)^i • (Ring.choose (t : ℤ)  i) •
    index (Y R a) (t-i) (index (Y R b) (s+i) c)) + Finset.sum (Finset.range (Int.toNat
    (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • index (Y R b) (s+t-i)
    (index (Y R a) i c))

/-- The commutator formula for vertex algebras. -/
def commutator_formula (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s : ℤ) : Prop :=
  index (Y R a) r (index (Y R b) s c) - index (Y R b) s (index (Y R a) r c) =
  Finset.sum (Finset.range (Int.toNat (- order R a b))) (fun i ↦ (Ring.choose r i) •
  index (Y R (index (Y R a) i b)) (r+s-i) c)

/-- The locality property, asserting that `(x-y)^N Y(a,x)Y(b,y) = (x-y)^N Y(b,y)Y(a,x)` for
sufficiently large `N`.  That is, the vertex operators commute up to finite order poles on the
diagonal. -/
def locality (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t = 0

-- locality and weak associativity need to be changed to the vertex operator definitions.

/-- The weak associativity property for vertex algebras. -/
def weak_associativity (R : Type*) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t: ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t

end VertexAlg

end NonAssocNonUnitalVertexAlgebra

section Unital

namespace VertexAlg

/-- A field is creative with respect to the unit vector `1` if evaluating at `1` yields a regular
series. -/
def creative [CommRing R] [AddCommGroupWithOne V] [Module R V] (A : VertexOperator R V) : Prop :=
  0 ≤ HahnSeries.order (A.toMap 1)

/-- The state attached to a creative field is its `z^0`-coefficient at `1`. -/
def state [CommRing R] [AddCommGroupWithOne V] [Module R V] (A : VertexOperator R V) : V :=
  coeff A 0 1

/-- A divided-power system of translation operators.  `T 1` is often written `T`. -/
def T (R: Type*) [CommRing R] [AddCommGroupWithOne V] [NonAssocNonUnitalVertexAlgebra R V]
    (n : ℕ) : Module.End R V :=
  {
    toFun := fun (x : V) => coeff (Y R x) n 1
    map_add' := by intros; funext; simp only [map_add, add_coeff_eq, LinearMap.add_apply]
    map_smul' := by intros; funext; simp only [map_smul, smul_coeff_eq, LinearMap.smul_apply,
      RingHom.id_apply]
  }

/-- The skew-symmetry property for vertex algebras: `Y(u,z)v = exp(Tz)Y(v,-z)u`. -/
def skew_symmetry (R : Type*) [CommRing R] [AddCommGroupWithOne V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) (n : ℤ) : Prop :=
  index (Y R b) n a = Finset.sum (Finset.range (Int.toNat (-n - order R a b)))
    (fun i ↦ (-1:ℤˣ)^(n + i + 1) • T R i (index (Y R a) (n+i) b))

/-- A field is translation covariant with respect to a divided-power system of endomorphisms that
stabilizes identity if left translation satisfies the Leibniz rule.  We omit conditions on `f`. -/
def translation_covariance (R : Type*) [CommRing R] [AddCommGroupWithOne V]
    [NonAssocNonUnitalVertexAlgebra R V] (A : VertexOperator R V) (f : ℕ → Module.End R V) : Prop :=
  ∀(i : ℕ) (n : ℤ), f i * coeff A n = Finset.sum (Finset.antidiagonal i)
  fun m => (-1 : ℤˣ) ^ m.fst • Ring.choose n m.fst • (coeff A (n - m.fst) * T R m.snd)

end VertexAlg

end Unital

/-- A vertex algebra over a commutative ring `R` is an `R`-module `V` with a distinguished unit
element `1`, together with a multiplication operation that takes values in Laurent series with
coefficients in `V`, such that `a(z) 1 ∈ a + zV[[z]]` for all `a ∈ V` -/
class VertexAlgebra (R : Type*) (V : Type*) [CommRing R] [AddCommGroupWithOne V] extends
    NonAssocNonUnitalVertexAlgebra R V where
  /-- The Borcherds identity holds. -/
  Borcherds_id : ∀ (a b c : V) (r s t : ℤ), VertexAlg.Borcherds_id R a b c r s t
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), VertexAlg.order R a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), VertexAlg.coeff (Y a) 0 1 = a

section VertexAlgebra

namespace VertexAlg

theorem Borcherds_identity (R : Type*) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_id R a b c r s t := VertexAlgebra.Borcherds_id a b c r s t

theorem unit_comm (R : Type*) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
    order R a 1 = 0 := VertexAlgebra.unit_comm a

theorem unit_right (R : Type*) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
    coeff (Y R a) 0 1 = a := VertexAlgebra.unit_right a

-- cofiniteness?

end VertexAlg
