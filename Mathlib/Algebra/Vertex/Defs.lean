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
* NonUnitalVertexAlgebra: A NonAssNonUnitalVertexAlgebra satisfying Borcherds identity.
* VertexAlgebra: A NonUnitalVertexAlgebra with One, satisfying a right identity rule.

## Main results

* Vertex operators form an `R`-module.

We postpone the proofs of equivalences of various identities to a different file.

## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328

-/

set_option autoImplicit false

universe u v

variable {V : Type u} {R : Type v}

section VertexOperator

/-- A vertex operator over a semiring `R` is an `R`-linear map from an `R`-module `V` to Laurent
series with coefficients in `V`-/
@[ext]
structure VertexOperator (R : Type v) (V : Type u) [CommRing R] [AddCommMonoid V] [Module R V] where
/-- The underlying structure map of a vertex operator. -/
  toMap : V →ₗ[R] HahnSeries ℤ V

namespace VertexAlg

instance LinearMapClass (R : Type v) (V : Type u) [CommRing R] [AddCommMonoid V] [Module R V] :
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
* `LinearMap.addCommMonoid` and `LinearMap.addCommGroup`: the elementwise addition structures
  corresponding to addition in the codomain
* `LinearMap.distribMulAction` and `LinearMap.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.

-/

/-- The coefficient of a vertex operator, viewed as a formal power series with coefficients in
linear endomorphisms. -/
def coeff [CommRing R] [AddCommMonoid V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V :=
  {
    toFun := fun (x : V) => (A.toMap x).coeff n
    map_add' := by simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
    map_smul' := by simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
  }

/-- We write `index` instead of `coefficient of a vertex operator under normalized indexing`.
Alternative suggestions welcome. -/
def index [CommRing R] [AddCommMonoid V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := coeff A (-n-1)

theorem index_eq_coeff_neg [CommRing R] [AddCommMonoid V] [Module R V] (A : VertexOperator R V)
    (n : ℤ) : index A n = coeff A (-n-1) := rfl

/-- The normal convention for the normalized coefficient of a vertex operatoris either `Aₙ` or
`A(n)`.  Either choice seems to break things. -/
scoped[VertexAlg] notation A "⁅" n "⁆" => index A n

instance [CommRing R] [AddCommMonoid V] [Module R V] : Zero (VertexOperator R V) :=
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
instance [AddCommMonoid R] : AddCommMonoid (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      apply add_comm }
-/

@[simp] lemma zero_toFun [CommRing R] [AddCommMonoid V] [Module R V] (x : V) :
  (0 : VertexOperator R V).toMap x = 0 := rfl

@[simp] lemma zero_coeff [CommRing R] [AddCommMonoid V] [Module R V] (n : ℤ) :
    coeff (0 : VertexOperator R V) n = 0 := by
  exact rfl

@[simp] lemma zero_index [CommRing R] [AddCommMonoid V] [Module R V] (n : ℤ) :
    (0 : VertexOperator R V) ⁅n⁆ = 0 := by
  exact rfl

instance [CommRing R] [AddCommMonoid V] [Module R V] : Add (VertexOperator R V) :=--inferInstance?
  {
    add := fun a b =>
      {
      toMap :=
        {
        toFun := fun x => a.toMap x + b.toMap x
        map_add' := by
          intros
          simp only [map_add]
          rw [@add_add_add_comm]
        map_smul' := by
          simp only [map_smul, RingHom.id_apply, smul_add, forall_const]
        }
      }
  }

@[simp] lemma add_toMap_eq [CommRing R] [AddCommMonoid V] [Module R V] (a b : VertexOperator R V)
  (x : V): (a + b).toMap x = a.toMap x + b.toMap x := rfl

/-!
@[simp] lemma add_coef_eq [Semiring R] [AddCommMonoid V] [Module R V] (a b : VertexOperator R V)
  (n : ℤ) : (a + b) ⁅n⁆ = a ⁅n⁆ + b ⁅n⁆ := by exact rfl
-/

-- can I use LinearMap.addCommMonoid here?
instance [CommRing R] [AddCommMonoid V] [Module R V] : AddCommMonoid (VertexOperator R V) :=
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
  }

instance [CommRing R] [AddCommMonoid V] [Module R V] : SMul R (VertexOperator R V) :=
  { smul := fun r a =>
    {toMap :=
      {
        toFun := fun x => r • a.toMap x
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

@[simp] lemma smul_toMap_eq [CommRing R] [AddCommMonoid V] [Module R V] (r : R)
    (a : VertexOperator R V) (x : V): (r • a).toMap x = r • a.toMap x := rfl

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

instance [CommRing R] [AddCommGroup V] [Module R V] : Module R (VertexOperator R V) :=
  {
    add_smul := by
      intros
      ext x n
      simp only [smul_toMap_eq, HahnSeries.smul_coeff, add_toMap_eq, HahnSeries.add_coeff',
        Pi.add_apply, add_smul]
    zero_smul := by
      intros
      ext x n
      simp only [zero_smul, zero_toFun, HahnSeries.zero_coeff]
  }

end VertexAlg

end VertexOperator

/-- A non-associative non-unital vertex algebra over a commutative ring `R` is an `R`-module `V`
with a multiplication that takes values in Laurent series with coefficients in `V`. -/
class NonAssocNonUnitalVertexAlgebra (R : Type v) (V : Type u) [CommRing R] [AddCommGroup V] extends
    Module R V where
  /-- The multiplication operation in a vertex algebra. -/
  Y: V →ₗ[R] VertexOperator R V

section NonAssocNonUnitalVertexAlgebra

namespace VertexAlg

/-- The multiplication in a vertex algebra. -/
def Y (R : Type v) {V : Type u} [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V] :
    V →ₗ[R] VertexOperator R V := NonAssocNonUnitalVertexAlgebra.Y

--scoped[VertexAlg] notation a "(" n ")" => index (Y R a) n --seems to fail for any bracket choice.

/-- The order is the smallest integer `n` such that `a ⁅-n-1⁆ b ≠ 0` if `Y a b` is nonzero, and zero
otherwise.  In particular, `a ⁅n⁆ b = 0` for `n ≥ -order a b`. -/
noncomputable def order (R : Type v) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) : ℤ := HahnSeries.order (Y R a b)

theorem coeff_zero_if_lt_order [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b : V) (n : ℤ) (h: n < order R a b) : coeff (Y R a) n b = 0 := by
  rw [order] at h
  simp only [coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_nonzero_at_order [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b : V) (h: Y R a b ≠ 0) : coeff (Y R a) (order R a b) b ≠ 0 := by
  rw [order, coeff]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_order_ne_zero h

theorem index_zero_if_neg_order_leq [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) (n : ℤ) (h: - order R a b ≤ n) :
    index (Y R a) n b = 0 := by
  rw [index_eq_coeff_neg]
  refine coeff_zero_if_lt_order a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem index_nonzero_at_neg_order_minus_one [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b : V) (h: Y R a b ≠ 0) :
    index (Y R a) (-order R a b - 1) b ≠ 0 := by
  rw [index_eq_coeff_neg, neg_sub, sub_neg_eq_add, add_sub_cancel']
  exact coeff_nonzero_at_order a b h

-- a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The first sum in the Borcherds identity, giving coefficients of `(a(x)b)(z)c` near `z=y-x`. -/
noncomputable def Borcherds_sum_1 (R : Type v) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-t - order R a b)))
    (fun i ↦ (Ring.choose r i) • index (Y R (index (Y R a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving coefficients of `a(y)b(z)c` near `x=y-z`. -/
noncomputable def Borcherds_sum_2 (R : Type v) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order R b c)))
    (fun i ↦ (-1)^i • (Ring.choose t i) • index (Y R a) (r+t-i) (index (Y R b) (s+i) c))

/-- The third sum in the Borcherds identity, giving coefficients of `b(z)a(y)c` near `-x = z-y`. -/
noncomputable def Borcherds_sum_3 (R : Type v) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order R a c)))
    (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • index (Y R b) (s+t-i) (index (Y R a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable def Borcherds_id (R : Type v) [CommRing R] [AddCommGroup V]
    [NonAssocNonUnitalVertexAlgebra R V] (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 R a b c r s t = Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t

end VertexAlg

end NonAssocNonUnitalVertexAlgebra

/-- A vertex algebra over a commutative ring `R` is an `R`-module `V` with a distinguished unit
element `1`, together with a multiplication operation that takes values in Laurent series with
coefficients in `V`, such that `a(z) 1 ∈ a + zV[[z]]` for all `a ∈ V` -/
class VertexAlgebra (R : Type v) (V : Type u) [CommRing R] [AddCommGroupWithOne V] extends
    NonAssocNonUnitalVertexAlgebra R V where
  /-- The Borcherds identity holds. -/
  Borcherds_id : ∀ (a b c : V) (r s t : ℤ), VertexAlg.Borcherds_id R a b c r s t
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), VertexAlg.order R a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), VertexAlg.coeff (Y a) 0 1 = a

section VertexAlgebra

namespace VertexAlg

theorem Borcherds_identity (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_id R a b c r s t := VertexAlgebra.Borcherds_id a b c r s t

theorem unit_comm (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
    order R a 1 = 0 := VertexAlgebra.unit_comm a

theorem unit_right (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
    coeff (Y R a) 0 1 = a := VertexAlgebra.unit_right a



--noncomputable def commutator formula
--noncomputable def locality

--noncomputable def associativity
--noncomputable def weak associativity

--noncomputable def skew-symmetry


/-!


-/

end VertexAlg
