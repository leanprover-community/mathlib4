/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Vertex.VertexOperator

/-!
# Vertex algebras
In this file we introduce a non-unital non-associative vertex algebra over a commutative ring `R` as
an `R`-module `V` with a left-multiplication operation `Y` to vertex operators in `V` over `R`.  We
may view `Y` as a bilinear map `V × V → V((z))`, or as a family of non-associative products
parametrized by `ℤ`.  The unit element is introduced with the `AddCommGroupWithOne` type, and the
Borcherds identity that defines vertex algebras is introduced in pieces for easier manipulation.
## Definitions
* NonAssocNonUnitalVertexAlgebra : This is an `R`-module `V` with multiplication `V ⊗ V → V((z))`.
* Borcherds identity sums: These are composites of vertex operators multiplied by binomial powers.
* Various identities: Borcherds, commutator, locality, associativity, skew-symmetry.
* VertexAlgebra: A NonUnitalVertexAlgebra with One, satisfying a right identity rule.
## Main results
We postpone the proofs of equivalences of various identities to Mathlib.Algebra.Vertex.Basic.
## To do:
* Refactor: remove non-unital non-associative vertex algebra.  Introduce Y by itself.
* Use formal series more, instead of combinatorial coefficient calculations.
*  order of associativity, weak associativity
* Fix weak associativity defs
* cofiniteness conditions?
## References
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118
-/

section NonAssocNonUnitalVertexAlgebra

/-- A non-associative non-unital vertex algebra over a commutative ring `R` is an `R`-module `V`
with a multiplication that takes values in Laurent series with coefficients in `V`. -/
class NonAssocNonUnitalVertexAlgebra (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] extends
    Module R V where
  /-- The multiplication operation in a vertex algebra. -/
  Y: V →ₗ[R] VertexOperator R V

namespace VertexAlg

variable (R : Type*) {V : Type*} [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]

/-- The multiplication in a vertex algebra. -/
def Y : V →ₗ[R] VertexOperator R V := NonAssocNonUnitalVertexAlgebra.Y

theorem Y_coeff_add_left_eq (a b : V) (n : ℤ) :
    coeff (Y R a + Y R b) n = coeff (Y R a) n + coeff (Y R b) n := by exact rfl

theorem Y_ncoef_add_left_eq (a b : V) (n : ℤ) :
    ncoef (Y R a + Y R b) n = ncoef (Y R a) n + ncoef (Y R b) n := by exact rfl

theorem Y_coeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    coeff (Y R (r • a)) n = r • coeff (Y R a) n := by
  simp only [map_smul]
  exact rfl

theorem Y_ncoef_smul_left_eq (r : R) (a : V) (n : ℤ) :
    ncoef (Y R (r • a)) n = r • ncoef (Y R a) n := by
  simp only [map_smul]
  exact rfl

theorem coeff_add_left_eq (a b c : V) (n : ℤ) :
    coeff (Y R (a + b)) n c = coeff (Y R a) n c + coeff (Y R b) n c := by
  rw [map_add, Y_coeff_add_left_eq, LinearMap.add_apply]

theorem ncoef_add_left_eq (a b c : V) (n : ℤ) :
    ncoef (Y R (a + b)) n c = ncoef (Y R a) n c + ncoef (Y R b) n c := by
  rw [map_add, Y_ncoef_add_left_eq, LinearMap.add_apply]

theorem coeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    coeff (Y R (r • a)) n b = r • coeff (Y R a) n b := by
  rw [Y_coeff_smul_left_eq, LinearMap.smul_apply]

theorem ncoef_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    ncoef (Y R (r • a)) n b = r • ncoef (Y R a) n b := by
  rw [Y_ncoef_smul_left_eq, LinearMap.smul_apply]

--scoped[VertexAlg] notation a "(" n ")" => ncoef (Y R a) n --seems to fail for any bracket choice.

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

theorem ncoef_zero_if_neg_order_leq (a b : V) (n : ℤ) (h: - order R a b ≤ n) :
    ncoef (Y R a) n b = 0 := by
  rw [ncoef]
  refine coeff_zero_if_lt_order R a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem ncoef_nonzero_at_neg_order_minus_one (a b : V) (h: Y R a b ≠ 0) :
    ncoef (Y R a) (-order R a b - 1) b ≠ 0 := by
  rw [ncoef, neg_sub, sub_neg_eq_add, add_sub_cancel']
  exact coeff_nonzero_at_order R a b h

-- Reminder: a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The first sum in the Borcherds identity, giving the `x^t z^s` coefficient of
`x^r (1 + z/x)^r (a(x)b)(z)c`. -/
noncomputable def Borcherds_sum_1 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-t - order R a b)))
    (fun i ↦ (Ring.choose r i) • ncoef (Y R (ncoef (Y R a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`y^t (1 - z/y)^t a(y)b(z)c`. -/
noncomputable def Borcherds_sum_2 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order R b c)))
    (fun i ↦ (-1)^i • (Ring.choose t i) • ncoef (Y R a) (r+t-i)
    (ncoef (Y R b) (s+i) c))

/-- The third sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`-(-y)^t (1 - y/z)^t b(z)a(y)c`. -/
noncomputable def Borcherds_sum_3 [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order R a c)))
    (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • ncoef (Y R b) (s+t-i)
    (ncoef (Y R a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable def Borcherds_id [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t

/-- The associativity property of vertex algebras. -/
def associativity [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (s t : ℤ) : Prop := ((Y R) (((Y R) a _[t]) b) _[s]) c = Finset.sum (Finset.range
    (Int.toNat (-s - order R b c))) (fun i ↦ (-1)^i • (Ring.choose (t : ℤ)  i) •
    ncoef (Y R a) (t-i) (ncoef (Y R b) (s+i) c)) + Finset.sum (Finset.range (Int.toNat
    (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • ncoef (Y R b) (s+t-i)
    (ncoef (Y R a) i c))

/-- The commutator formula for vertex algebras. -/
def commutator_formula [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s : ℤ) : Prop :=
  ncoef (Y R a) r (ncoef (Y R b) s c) - ncoef (Y R b) s (ncoef (Y R a) r c) =
  Finset.sum (Finset.range (Int.toNat (- order R a b))) (fun i ↦ (Ring.choose r i) •
  ncoef (Y R (ncoef (Y R a) i b)) (r+s-i) c)

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
    (n : ℕ) : Module.End R V where
  toFun := fun (x : V) => coeff (Y R x) n 1
  map_add' := by intros; funext; simp only [coeff_add_left_eq]
  map_smul' := by intros; funext; simp only [coeff_smul_left_eq, RingHom.id_apply]

/-- The skew-symmetry property for vertex algebras: `Y(u,z)v = exp(Tz)Y(v,-z)u`. -/
def skew_symmetry (R : Type*) [CommRing R] [AddCommGroupWithOne V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) (n : ℤ) : Prop :=
  ncoef (Y R b) n a = Finset.sum (Finset.range (Int.toNat (-n - order R a b)))
    (fun i ↦ (-1:ℤˣ)^(n + i + 1) • T R i (ncoef (Y R a) (n+i) b))

/-- A field is translation covariant with respect to a divided-power system of endomorphisms that
stabilizes identity if left translation satisfies the Leibniz rule.  We omit conditions on `f`. -/
def translation_covariance (R : Type*) [CommRing R] [AddCommGroupWithOne V]
    [NonAssocNonUnitalVertexAlgebra R V] (A : VertexOperator R V) (f : ℕ → Module.End R V) : Prop :=
  ∀(i : ℕ) (n : ℤ), f i * coeff A n = Finset.sum (Finset.antidiagonal i)
  fun m => (-1 : ℤˣ) ^ m.fst • Ring.choose n m.fst • (coeff A (n - m.fst) * T R m.snd)

end VertexAlg

end Unital

section VertexAlgebra

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

namespace VertexAlg

variable (R : Type*) {V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]

theorem Borcherds_identity (a b c : V) (r s t : ℤ) : Borcherds_id R a b c r s t :=
  VertexAlgebra.Borcherds_id a b c r s t

theorem unit_comm (a : V) : order R a 1 = 0 := VertexAlgebra.unit_comm a

theorem unit_right (a : V) : coeff (Y R a) 0 1 = a := VertexAlgebra.unit_right a

-- homs? cofiniteness?

end VertexAlg
