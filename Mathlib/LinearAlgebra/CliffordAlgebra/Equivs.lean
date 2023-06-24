/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.clifford_algebra.equivs
! leanprover-community/mathlib commit cf7a7252c1989efe5800e0b3cdfeb4228ac6b40e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `clifford_algebra`.

## Rings

* `clifford_algebra_ring.equiv`: any ring is equivalent to a `clifford_algebra` over a
  zero-dimensional vector space.

## Complex numbers

* `clifford_algebra_complex.equiv`: the `complex` numbers are equivalent as an `ℝ`-algebra to a
  `clifford_algebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `clifford_algebra_complex.to_complex`: the forward direction of this equiv
* `clifford_algebra_complex.of_complex`: the reverse direction of this equiv

We show additionally that this equivalence sends `complex.conj` to `clifford_algebra.involute` and
vice-versa:

* `clifford_algebra_complex.to_complex_involute`
* `clifford_algebra_complex.of_complex_conj`

Note that in this algebra `clifford_algebra.reverse` is the identity and so the clifford conjugate
is the same as `clifford_algebra.involute`.

## Quaternion algebras

* `clifford_algebra_quaternion.equiv`: a `quaternion_algebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `clifford_algebra_quaternion.to_quaternion`: the forward direction of this equiv
* `clifford_algebra_quaternion.of_quaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `quaternion_algebra.conj` to the clifford conjugate
and vice-versa:

* `clifford_algebra_quaternion.to_quaternion_star`
* `clifford_algebra_quaternion.of_quaternion_star`

## Dual numbers

* `clifford_algebra_dual_number.equiv`: `R[ε]` is is equivalent as an `R`-algebra to a clifford
  algebra over `R` where `Q = 0`.

-/


open CliffordAlgebra

/-! ### The clifford algebra isomorphic to a ring -/


namespace CliffordAlgebraRing

open scoped ComplexConjugate

variable {R : Type _} [CommRing R]

@[simp]
theorem ι_eq_zero : ι (0 : QuadraticForm R Unit) = 0 :=
  Subsingleton.elim _ _
#align clifford_algebra_ring.ι_eq_zero CliffordAlgebraRing.ι_eq_zero

/-- Since the vector space is empty the ring is commutative. -/
instance : CommRing (CliffordAlgebra (0 : QuadraticForm R Unit)) :=
  { CliffordAlgebra.instRing _ with
    mul_comm := fun x y => by
      induction x using CliffordAlgebra.induction
      case h_grade0 r => apply Algebra.commutes
      case h_grade1 x => simp
      case h_add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
      case h_mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc] }

theorem reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) : x.reverse = x := by
  induction x using CliffordAlgebra.induction
  case h_grade0 r => exact reverse.commutes _
  case h_grade1 x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  case h_mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  case h_add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]
#align clifford_algebra_ring.reverse_apply CliffordAlgebraRing.reverse_apply

@[simp]
theorem reverse_eq_id :
    (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) →ₗ[R] _) = LinearMap.id :=
  LinearMap.ext reverse_apply
#align clifford_algebra_ring.reverse_eq_id CliffordAlgebraRing.reverse_eq_id

@[simp]
theorem involute_eq_id :
    (involute : CliffordAlgebra (0 : QuadraticForm R Unit) →ₐ[R] _) = AlgHom.id R _ := by ext; simp
#align clifford_algebra_ring.involute_eq_id CliffordAlgebraRing.involute_eq_id

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun m : Unit => (MulZeroClass.zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext x; exact AlgHom.commutes _ x)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])
#align clifford_algebra_ring.equiv CliffordAlgebraRing.equiv

end CliffordAlgebraRing

/-! ### The clifford algebra isomorphic to the complex numbers -/


namespace CliffordAlgebraComplex

open scoped ComplexConjugate

/-- The quadratic form sending elements to the negation of their square. -/
def q : QuadraticForm ℝ ℝ :=
  -QuadraticForm.sq
#align clifford_algebra_complex.Q CliffordAlgebraComplex.q

@[simp]
theorem q_apply (r : ℝ) : q r = -(r * r) :=
  rfl
#align clifford_algebra_complex.Q_apply CliffordAlgebraComplex.q_apply

/-- Intermediate result for `clifford_algebra_complex.equiv`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def toComplex : CliffordAlgebra q →ₐ[ℝ] ℂ :=
  CliffordAlgebra.lift q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩
#align clifford_algebra_complex.to_complex CliffordAlgebraComplex.toComplex

@[simp]
theorem toComplex_ι (r : ℝ) : toComplex (ι q r) = r • Complex.I :=
  CliffordAlgebra.lift_ι_apply _ _ r
#align clifford_algebra_complex.to_complex_ι CliffordAlgebraComplex.toComplex_ι

/-- `clifford_algebra.involute` is analogous to `complex.conj`. -/
@[simp]
theorem toComplex_involute (c : CliffordAlgebra q) : toComplex c.involute = conj (toComplex c) := by
  have : to_complex (involute (ι Q 1)) = conj (to_complex (ι Q 1)) := by
    simp only [involute_ι, to_complex_ι, AlgHom.map_neg, one_smul, Complex.conj_I]
  suffices to_complex.comp involute = complex.conj_ae.to_alg_hom.comp to_complex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this
#align clifford_algebra_complex.to_complex_involute CliffordAlgebraComplex.toComplex_involute

/-- Intermediate result for `clifford_algebra_complex.equiv`: `ℂ` can be converted to
`clifford_algebra_complex.Q` above can be converted to. -/
def ofComplex : ℂ →ₐ[ℝ] CliffordAlgebra q :=
  Complex.lift
    ⟨CliffordAlgebra.ι q 1, by
      rw [CliffordAlgebra.ι_sq_scalar, Q_apply, one_mul, RingHom.map_neg, RingHom.map_one]⟩
#align clifford_algebra_complex.of_complex CliffordAlgebraComplex.ofComplex

@[simp]
theorem ofComplex_i : ofComplex Complex.I = ι q 1 :=
  Complex.liftAux_apply_I _ _
#align clifford_algebra_complex.of_complex_I CliffordAlgebraComplex.ofComplex_i

@[simp]
theorem toComplex_comp_ofComplex : toComplex.comp ofComplex = AlgHom.id ℝ ℂ := by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [of_complex_I, to_complex_ι, one_smul]
#align clifford_algebra_complex.to_complex_comp_of_complex CliffordAlgebraComplex.toComplex_comp_ofComplex

@[simp]
theorem toComplex_ofComplex (c : ℂ) : toComplex (ofComplex c) = c :=
  AlgHom.congr_fun toComplex_comp_ofComplex c
#align clifford_algebra_complex.to_complex_of_complex CliffordAlgebraComplex.toComplex_ofComplex

@[simp]
theorem ofComplex_comp_toComplex : ofComplex.comp toComplex = AlgHom.id ℝ (CliffordAlgebra q) := by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [to_complex_ι, one_smul, of_complex_I]
#align clifford_algebra_complex.of_complex_comp_to_complex CliffordAlgebraComplex.ofComplex_comp_toComplex

@[simp]
theorem ofComplex_toComplex (c : CliffordAlgebra q) : ofComplex (toComplex c) = c :=
  AlgHom.congr_fun ofComplex_comp_toComplex c
#align clifford_algebra_complex.of_complex_to_complex CliffordAlgebraComplex.ofComplex_toComplex

/-- The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to
`ℂ`. -/
@[simps]
protected def equiv : CliffordAlgebra q ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex
#align clifford_algebra_complex.equiv CliffordAlgebraComplex.equiv

/-- The clifford algebra is commutative since it is isomorphic to the complex numbers.

TODO: prove this is true for all `clifford_algebra`s over a 1-dimensional vector space. -/
instance : CommRing (CliffordAlgebra q) :=
  { CliffordAlgebra.instRing _ with
    mul_comm := fun x y =>
      CliffordAlgebraComplex.equiv.Injective <| by
        rw [AlgEquiv.map_mul, mul_comm, AlgEquiv.map_mul] }

/-- `reverse` is a no-op over `clifford_algebra_complex.Q`. -/
theorem reverse_apply (x : CliffordAlgebra q) : x.reverse = x := by
  induction x using CliffordAlgebra.induction
  case h_grade0 r => exact reverse.commutes _
  case h_grade1 x => rw [reverse_ι]
  case h_mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  case h_add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]
#align clifford_algebra_complex.reverse_apply CliffordAlgebraComplex.reverse_apply

@[simp]
theorem reverse_eq_id : (reverse : CliffordAlgebra q →ₗ[ℝ] _) = LinearMap.id :=
  LinearMap.ext reverse_apply
#align clifford_algebra_complex.reverse_eq_id CliffordAlgebraComplex.reverse_eq_id

/-- `complex.conj` is analogous to `clifford_algebra.involute`. -/
@[simp]
theorem ofComplex_conj (c : ℂ) : ofComplex (conj c) = (ofComplex c).involute :=
  CliffordAlgebraComplex.equiv.Injective <| by
    rw [equiv_apply, equiv_apply, to_complex_involute, to_complex_of_complex, to_complex_of_complex]
#align clifford_algebra_complex.of_complex_conj CliffordAlgebraComplex.ofComplex_conj

-- this name is too short for us to want it visible after `open clifford_algebra_complex`
attribute [protected] Q

end CliffordAlgebraComplex

/-! ### The clifford algebra isomorphic to the quaternions -/


namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type _} [CommRing R] (c₁ c₂ : R)

/-- `Q c₁ c₂` is a quadratic form over `R × R` such that `clifford_algebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
def q : QuadraticForm R (R × R) :=
  (c₁ • QuadraticForm.sq).Prod (c₂ • QuadraticForm.sq)
#align clifford_algebra_quaternion.Q CliffordAlgebraQuaternion.q

@[simp]
theorem q_apply (v : R × R) : q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) :=
  rfl
#align clifford_algebra_quaternion.Q_apply CliffordAlgebraQuaternion.q_apply

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (q c₁ c₂)) c₁ c₂ where
  i := ι (q c₁ c₂) (1, 0)
  j := ι (q c₁ c₂) (0, 1)
  k := ι (q c₁ c₂) (1, 0) * ι (q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticForm.polar]
    simp
#align clifford_algebra_quaternion.quaternion_basis CliffordAlgebraQuaternion.quaternionBasis

variable {c₁ c₂}

/-- Intermediate result of `clifford_algebra_quaternion.equiv`: clifford algebras over
`clifford_algebra_quaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
def toQuaternion : CliffordAlgebra (q c₁ c₂) →ₐ[R] ℍ[R,c₁,c₂] :=
  CliffordAlgebra.lift (q c₁ c₂)
    ⟨{  toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by ext <;> simp }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩
#align clifford_algebra_quaternion.to_quaternion CliffordAlgebraQuaternion.toQuaternion

@[simp]
theorem toQuaternion_ι (v : R × R) :
    toQuaternion (ι (q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]) :=
  CliffordAlgebra.lift_ι_apply _ _ v
#align clifford_algebra_quaternion.to_quaternion_ι CliffordAlgebraQuaternion.toQuaternion_ι

/-- The "clifford conjugate" maps to the quaternion conjugate. -/
theorem toQuaternion_star (c : CliffordAlgebra (q c₁ c₂)) :
    toQuaternion (star c) = star (toQuaternion c) := by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction
  case h_grade0 r =>
    simp only [reverse.commutes, AlgHom.commutes, QuaternionAlgebra.coe_algebraMap,
      QuaternionAlgebra.star_coe]
  case h_grade1 x =>
    rw [reverse_ι, involute_ι, to_quaternion_ι, AlgHom.map_neg, to_quaternion_ι,
      QuaternionAlgebra.neg_mk, star_mk, neg_zero]
  case h_mul x₁ x₂ hx₁ hx₂ => simp only [reverse.map_mul, AlgHom.map_mul, hx₁, hx₂, star_mul]
  case h_add x₁ x₂ hx₁ hx₂ => simp only [reverse.map_add, AlgHom.map_add, hx₁, hx₂, star_add]
#align clifford_algebra_quaternion.to_quaternion_star CliffordAlgebraQuaternion.toQuaternion_star

/-- Map a quaternion into the clifford algebra. -/
def ofQuaternion : ℍ[R,c₁,c₂] →ₐ[R] CliffordAlgebra (q c₁ c₂) :=
  (quaternionBasis c₁ c₂).liftHom
#align clifford_algebra_quaternion.of_quaternion CliffordAlgebraQuaternion.ofQuaternion

@[simp]
theorem ofQuaternion_mk (a₁ a₂ a₃ a₄ : R) :
    ofQuaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,c₂]) =
      algebraMap R _ a₁ + a₂ • ι (q c₁ c₂) (1, 0) + a₃ • ι (q c₁ c₂) (0, 1) +
        a₄ • (ι (q c₁ c₂) (1, 0) * ι (q c₁ c₂) (0, 1)) :=
  rfl
#align clifford_algebra_quaternion.of_quaternion_mk CliffordAlgebraQuaternion.ofQuaternion_mk

@[simp]
theorem ofQuaternion_comp_toQuaternion :
    ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra (q c₁ c₂)) := by
  ext : 1
  dsimp
  -- before we end up with two goals and have to do this twice
  ext
  all_goals
    dsimp
    rw [to_quaternion_ι]
    dsimp
    simp only [to_quaternion_ι, zero_smul, one_smul, zero_add, add_zero, RingHom.map_zero]
#align clifford_algebra_quaternion.of_quaternion_comp_to_quaternion CliffordAlgebraQuaternion.ofQuaternion_comp_toQuaternion

@[simp]
theorem ofQuaternion_toQuaternion (c : CliffordAlgebra (q c₁ c₂)) :
    ofQuaternion (toQuaternion c) = c :=
  AlgHom.congr_fun (ofQuaternion_comp_toQuaternion : _ = AlgHom.id R (CliffordAlgebra (q c₁ c₂))) c
#align clifford_algebra_quaternion.of_quaternion_to_quaternion CliffordAlgebraQuaternion.ofQuaternion_toQuaternion

@[simp]
theorem toQuaternion_comp_ofQuaternion : toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,c₂] :=
  by
  apply quaternion_algebra.lift.symm.injective
  ext1 <;> dsimp [QuaternionAlgebra.Basis.lift] <;> simp
#align clifford_algebra_quaternion.to_quaternion_comp_of_quaternion CliffordAlgebraQuaternion.toQuaternion_comp_ofQuaternion

@[simp]
theorem toQuaternion_ofQuaternion (q : ℍ[R,c₁,c₂]) : toQuaternion (ofQuaternion q) = q :=
  AlgHom.congr_fun (toQuaternion_comp_ofQuaternion : _ = AlgHom.id R ℍ[R,c₁,c₂]) q
#align clifford_algebra_quaternion.to_quaternion_of_quaternion CliffordAlgebraQuaternion.toQuaternion_ofQuaternion

/-- The clifford algebra over `clifford_algebra_quaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps]
protected def equiv : CliffordAlgebra (q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂] :=
  AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion
#align clifford_algebra_quaternion.equiv CliffordAlgebraQuaternion.equiv

/-- The quaternion conjugate maps to the "clifford conjugate" (aka `star`). -/
@[simp]
theorem ofQuaternion_star (q : ℍ[R,c₁,c₂]) : ofQuaternion (star q) = star (ofQuaternion q) :=
  CliffordAlgebraQuaternion.equiv.Injective <| by
    rw [equiv_apply, equiv_apply, to_quaternion_star, to_quaternion_of_quaternion,
      to_quaternion_of_quaternion]
#align clifford_algebra_quaternion.of_quaternion_star CliffordAlgebraQuaternion.ofQuaternion_star

-- this name is too short for us to want it visible after `open clifford_algebra_quaternion`
attribute [protected] Q

end CliffordAlgebraQuaternion

/-! ### The clifford algebra isomorphic to the dual numbers -/


namespace CliffordAlgebraDualNumber

open scoped DualNumber

open DualNumber TrivSqZeroExt

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

theorem ι_mul_ι (r₁ r₂) : ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0 := by
  rw [← mul_one r₁, ← mul_one r₂, ← smul_eq_mul R, ← smul_eq_mul R, LinearMap.map_smul,
    LinearMap.map_smul, smul_mul_smul, ι_sq_scalar, QuadraticForm.zero_apply, RingHom.map_zero,
    smul_zero]
#align clifford_algebra_dual_number.ι_mul_ι CliffordAlgebraDualNumber.ι_mul_ι

/-- The clifford algebra over a 1-dimensional vector space with 0 quadratic form is isomorphic to
the dual numbers. -/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε] :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨ι _ (1 : R), ι_mul_ι (1 : R) 1⟩)
    (by ext x : 1; dsimp; rw [lift_apply_eps, Subtype.coe_mk, lift_ι_apply, inr_hom_apply, eps])
    (by ext : 2; dsimp; rw [lift_ι_apply, inr_hom_apply, ← eps, lift_apply_eps, Subtype.coe_mk])
#align clifford_algebra_dual_number.equiv CliffordAlgebraDualNumber.equiv

@[simp]
theorem equiv_ι (r : R) : CliffordAlgebraDualNumber.equiv (ι _ r) = r • ε :=
  (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)
#align clifford_algebra_dual_number.equiv_ι CliffordAlgebraDualNumber.equiv_ι

@[simp]
theorem equiv_symm_eps :
    CliffordAlgebraDualNumber.equiv.symm (eps : R[ε]) = ι (0 : QuadraticForm R R) 1 :=
  DualNumber.lift_apply_eps _
#align clifford_algebra_dual_number.equiv_symm_eps CliffordAlgebraDualNumber.equiv_symm_eps

end CliffordAlgebraDualNumber

