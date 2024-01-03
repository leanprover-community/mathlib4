/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.LaurentSeries

/-!
# Vertex algebras

In this file we introduce vertex algebras using Laurent series.

## Definitions

* VertexOperator : This is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* HasseDerivative : This is a divided-power derivative.
* NonAssocNonUnitalVertexAlgebra : This is an `R`-module `V` with multiplication `V ⊗ V → V((z))`.
* Borcherds identity sums: These are more or less composites of vertex operators.
* Various identities: Borcherds, commutator, locality, associativity, skew-symmetry.
* NonUnitalVertexAlgebra: A NonAssocNonUnitalVertexAlgebra satisfying Borcherds identity.
* VertexAlgebra: A NonUnitalVertexAlgebra with One, satisfying a right identity rule.

## Main results

* Vertex operators form an `R`-module.

We postpone the proofs of equivalences of various identities to Mathlib.Algebra.Vertex.Basic.

## To do:

* residue products, order of associativity, weak associativity

* Fix locality and weak associativity defs

* cofiniteness conditions?

## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118

-/

set_option autoImplicit false

section VertexOperator

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a semiring `R` is an `R`-linear map from an `R`-module `V` to Laurent
series with coefficients in `V`. -/

abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := V →ₗ[R] LaurentSeries V

namespace VertexAlg

--theorem VertexOperator_add (A B : VertexOperator R V) (x : V) : (A + B) x = (A x) + (B x) := rfl

/-- The coefficient of a vertex operator, viewed as a formal power series with coefficients in
linear endomorphisms. -/
def coeff [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V :=
  {
    toFun := fun (x : V) => (A x).coeff n
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

noncomputable instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) :=
  {
    one := HahnSeries.single.linearMap 0
  }

theorem one : (1 : VertexOperator R V) = HahnSeries.single.linearMap 0 := by
  exact rfl

theorem one_coeff_ite (x : V) (n : ℤ) : @coeff R V _ _ _ 1 n x = if n = 0 then x else 0 := by
  rw [one]
  unfold HahnSeries.single.linearMap HahnSeries.single.addMonoidHom HahnSeries.single Pi.single
    Function.update
  simp_all only [eq_rec_constant, Pi.zero_apply, dite_eq_ite]
  exact rfl

theorem one_coeff_zero' (x : V) : @coeff R V _ _ _ 1 0 x = x := by
  rw [one_coeff_ite, if_pos rfl]

theorem one_coeff_ne (x : V) (n : ℤ) (hn : n ≠ 0): @coeff R V _ _ _ 1 n x = 0 := by
  rw [one_coeff_ite, if_neg hn]

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

/-- The `k`th Hasse derivative of a vertex operator `∑ A_i X^i` is `∑ (i.choose k) A_i X^(i-k)`.
That is, it sends a vector to the `k`th Hasse derivative of the corresponding Laurent series.
It satisfies `k! * (hasseDeriv k A) = derivative^[k] A`. -/
def hasseDeriv (k : ℕ) (A : VertexOperator R V) : VertexOperator R V :=
  {
    toFun := fun (x : V) => LaurentSeries.hasseDeriv k (A x)
    map_add' := by
      intros
      simp only [map_add, LaurentSeries.hasseDeriv_add]
    map_smul' := by
      intros
      simp only [map_smul, RingHom.id_apply, LaurentSeries.hasseDeriv_smul]
  }

theorem hasseDeriv_add (k : ℕ) (A B : VertexOperator R V) : hasseDeriv k (A + B) =
    hasseDeriv k A + hasseDeriv k B := by
  ext
  simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.add_coeff, hasseDeriv,
    LaurentSeries.hasseDeriv_add]

theorem hasseDeriv_smul (k : ℕ) (A : VertexOperator R V) (r : R) :
    hasseDeriv k (r • A) = r • hasseDeriv k A := by
  ext
  simp only [LinearMap.smul_apply, HahnSeries.smul_coeff, hasseDeriv, LaurentSeries.hasseDeriv_smul,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The Hasse derivative as a linear map on vertex operators. -/
def hasseDeriv.linearMap (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  {
    toFun := fun A => hasseDeriv k A
    map_add' := by
      intros
      simp only [hasseDeriv_add]
    map_smul' := by
      intros
      simp only [hasseDeriv_smul, RingHom.id_apply]
  }

theorem hasseDeriv_coeff (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    coeff (hasseDeriv k A) n = (Ring.choose (n + k) k) • coeff A (n + k) := by
  exact rfl

theorem hasseDeriv_index (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    index (hasseDeriv k A) n = (Ring.choose (-n - 1 + k) k) • index A (n - k) := by
  simp only [index_eq_coeff_neg, hasseDeriv_coeff]
  rw [show -n - 1 + k = -(n - k) - 1 by linarith]

theorem hasseDeriv_zero' (A : VertexOperator R V) : hasseDeriv 0 A = A := by
  ext x n
  simp only [hasseDeriv, LaurentSeries.hasseDeriv_zero', LinearMap.coe_mk, AddHom.coe_mk]

theorem hasseDeriv_zero : @hasseDeriv.linearMap R V _ _ _ 0 = LinearMap.id := by
  exact LinearMap.ext <| hasseDeriv_zero'

theorem hasseDeriv_one_coeff (A : VertexOperator R V) (n : ℤ) :
    coeff (hasseDeriv 1 A) n = (n + 1) • coeff A (n + 1) := by
  rw [hasseDeriv_coeff 1, Nat.cast_one, @Ring.choose_one_right ℤ _ _ _ _ _]

/-- The derivative of a vertex operator is the first Hasse derivative, taking `∑ A_n X^n` to
`∑ n A_n X^{n-1}`, or `∑ A_n X^{-n-1}` to `∑ (-n-1) A_{n-1} X^{-n-1}` -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V := hasseDeriv.linearMap 1

theorem hasseDeriv_one' (A : VertexOperator R V) : hasseDeriv 1 A = derivative A := by
  rw[derivative, hasseDeriv.linearMap, ← @LinearMap.toFun_eq_coe]

@[simp]
theorem hasseDeriv_one : hasseDeriv.linearMap 1 = @derivative R V _ _ _ := rfl

theorem hasseDeriv_apply_one (k : ℕ) (hk : 0 < k) : hasseDeriv k (1 : VertexOperator R V) = 0 := by
  ext x n
  rw [LinearMap.zero_apply, HahnSeries.zero_coeff, one]
  unfold HahnSeries.single.linearMap HahnSeries.single.addMonoidHom hasseDeriv
  simp only [ZeroHom.toFun_eq_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LaurentSeries.hasseDeriv_single, Ring.choose_zero_pos ℤ k hk, zero_smul,
    HahnSeries.single_eq_zero]
  exact rfl


/-!

@[simp]
theorem hasseDeriv_monomial (n : ℕ) (r : R) :
    hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by

theorem hasseDeriv_C (r : R) (hk : 0 < k) : hasseDeriv k (C r) = 0 := by

theorem hasseDeriv_X (hk : 1 < k) : hasseDeriv k (X : R[X]) = 0 := by

theorem factorial_smul_hasseDeriv : ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k] := by
  induction' k with k ih

theorem hasseDeriv_comp (k l : ℕ) :
    (@hasseDeriv R _ k).comp (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) := by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2


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

variable (R : Type*) {V : Type*} [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]

/-- The multiplication in a vertex algebra. -/
def Y : V →ₗ[R] VertexOperator R V := NonAssocNonUnitalVertexAlgebra.Y

theorem Y_coeff_add_left_eq (a b : V) (n : ℤ) :
    coeff (Y R a + Y R b) n = coeff (Y R a) n + coeff (Y R b) n := by exact rfl

theorem Y_index_add_left_eq (a b : V) (n : ℤ) :
    index (Y R a + Y R b) n = index (Y R a) n + index (Y R b) n := by exact rfl

theorem Y_coeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    coeff (Y R (r • a)) n = r • coeff (Y R a) n := by
  simp only [map_smul]
  exact rfl

theorem Y_index_smul_left_eq (r : R) (a : V) (n : ℤ) :
    index (Y R (r • a)) n = r • index (Y R a) n := by
  simp only [map_smul]
  exact rfl

theorem coeff_add_left_eq (a b c : V) (n : ℤ) :
    coeff (Y R (a + b)) n c = coeff (Y R a) n c + coeff (Y R b) n c := by
  rw [map_add, Y_coeff_add_left_eq, LinearMap.add_apply]

theorem index_add_left_eq (a b c : V) (n : ℤ) :
    index (Y R (a + b)) n c = index (Y R a) n c + index (Y R b) n c := by
  rw [map_add, Y_index_add_left_eq, LinearMap.add_apply]

theorem coeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    coeff (Y R (r • a)) n b = r • coeff (Y R a) n b := by
  rw [Y_coeff_smul_left_eq, LinearMap.smul_apply]

theorem index_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    index (Y R (r • a)) n b = r • index (Y R a) n b := by
  rw [Y_index_smul_left_eq, LinearMap.smul_apply]

--scoped[VertexAlg] notation a "(" n ")" => index (Y R a) n --seems to fail for any bracket choice.

/-- The order is the smallest integer `n` such that `a ⁅-n-1⁆ b ≠ 0` if `Y a b` is nonzero, and zero
otherwise.  In particular, `a ⁅n⁆ b = 0` for `n ≥ -order a b`. -/
noncomputable def order [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) : ℤ := HahnSeries.order (Y R a b)

theorem coeff_zero_if_lt_order (a b : V) (n : ℤ) (h: n < order R a b) :
    coeff (Y R a) n b = 0 := by
  rw [order] at h
  simp only [coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_nonzero_at_order (a b : V) (h: Y R a b ≠ 0) :
    coeff (Y R a) (order R a b) b ≠ 0 := by
  rw [order, coeff]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_order_ne_zero h

theorem index_zero_if_neg_order_leq (a b : V) (n : ℤ) (h: - order R a b ≤ n) :
    index (Y R a) n b = 0 := by
  rw [index_eq_coeff_neg]
  refine coeff_zero_if_lt_order R a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem index_nonzero_at_neg_order_minus_one (a b : V) (h: Y R a b ≠ 0) :
    index (Y R a) (-order R a b - 1) b ≠ 0 := by
  rw [index_eq_coeff_neg, neg_sub, sub_neg_eq_add, add_sub_cancel']
  exact coeff_nonzero_at_order R a b h

-- Reminder: a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The first sum in the Borcherds identity, giving coefficients of `(a(x)b)(z)c` near `z=y-x`. -/
noncomputable def Borcherds_sum_1 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-t - order R a b)))
    (fun i ↦ (Ring.choose r i) • index (Y R (index (Y R a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving coefficients of `a(y)b(z)c` near `x=y-z`. -/
noncomputable def Borcherds_sum_2 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order R b c)))
    (fun i ↦ (-1)^i • (Ring.choose t i) • index (Y R a) (r+t-i)
    (index (Y R b) (s+i) c))

/-- The third sum in the Borcherds identity, giving coefficients of `b(z)a(y)c` near `-x = z-y`. -/
noncomputable def Borcherds_sum_3 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order R a c)))
    (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • index (Y R b) (s+t-i)
    (index (Y R a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable def Borcherds_id [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t

/-- The associativity property of vertex algebras. -/
def associativity [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) : Prop := ((Y R) (((Y R) a⁅t⁆) b)⁅s⁆) c = Finset.sum (Finset.range
    (Int.toNat (-s - order R b c))) (fun i ↦ (-1)^i • (Ring.choose (t : ℤ)  i) •
    index (Y R a) (t-i) (index (Y R b) (s+i) c)) + Finset.sum (Finset.range (Int.toNat
    (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • index (Y R b) (s+t-i)
    (index (Y R a) i c))

/-- The commutator formula for vertex algebras. -/
def commutator_formula [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s : ℤ) : Prop :=
  index (Y R a) r (index (Y R b) s c) - index (Y R b) s (index (Y R a) r c) =
  Finset.sum (Finset.range (Int.toNat (- order R a b))) (fun i ↦ (Ring.choose r i) •
  index (Y R (index (Y R a) i b)) (r+s-i) c)

/-- The locality property, asserting that `(x-y)^N Y(a,x)Y(b,y) = (x-y)^N Y(b,y)Y(a,x)` for
sufficiently large `N`.  That is, the vertex operators commute up to finite order poles on the
diagonal. -/
def locality [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) : Prop := isLocal R V (Y R a) (Y R b)
-- was Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t = 0

-- weak associativity needs to be changed to the vertex operator definition.

/-- The weak associativity property for vertex algebras. -/
def weak_associativity [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t: ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t

end VertexAlg

end NonAssocNonUnitalVertexAlgebra

section Unital

namespace VertexAlg

variable (R : Type*) {V : Type*} [CommRing R] [AddCommGroupWithOne V] [Module R V]

/-- A field is creative with respect to the unit vector `1` if evaluating at `1` yields a regular
series. -/
def creative (A : VertexOperator R V) : Prop :=
  0 ≤ HahnSeries.order (A 1)

/-- The state attached to a creative field is its `z^0`-coefficient at `1`. -/
def state (A : VertexOperator R V) : V :=
  coeff A 0 1

/-- A divided-power system of translation operators.  `T 1` is often written `T`. -/
def T (R: Type*) [CommRing R] [AddCommGroupWithOne V] [NonAssocNonUnitalVertexAlgebra R V]
    (n : ℕ) : Module.End R V :=
  {
    toFun := fun (x : V) => coeff (Y R x) n 1
    map_add' := by intros; funext; simp only [coeff_add_left_eq]
    map_smul' := by intros; funext; simp only [coeff_smul_left_eq, RingHom.id_apply]
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

variable (R : Type*) {V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]

theorem Borcherds_identity (a b c : V) (r s t : ℤ) : Borcherds_id R a b c r s t :=
  VertexAlgebra.Borcherds_id a b c r s t

theorem unit_comm (a : V) : order R a 1 = 0 := VertexAlgebra.unit_comm a

theorem unit_right (a : V) : coeff (Y R a) 0 1 = a := VertexAlgebra.unit_right a

-- cofiniteness?

end VertexAlg
