/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `CliffordAlgebra`.

## Rings

* `CliffordAlgebraRing.equiv`: any ring is equivalent to a `CliffordAlgebra` over a
  zero-dimensional vector space.

## Complex numbers

* `CliffordAlgebraComplex.equiv`: the `Complex` numbers are equivalent as an `ℝ`-algebra to a
  `CliffordAlgebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `CliffordAlgebraComplex.toComplex`: the forward direction of this equiv
* `CliffordAlgebraComplex.ofComplex`: the reverse direction of this equiv

We show additionally that this equivalence sends `Complex.conj` to `CliffordAlgebra.involute` and
vice-versa:

* `CliffordAlgebraComplex.toComplex_involute`
* `CliffordAlgebraComplex.ofComplex_conj`

Note that in this algebra `CliffordAlgebra.reverse` is the identity and so the clifford conjugate
is the same as `CliffordAlgebra.involute`.

## Quaternion algebras

* `CliffordAlgebraQuaternion.equiv`: a `QuaternionAlgebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `CliffordAlgebraQuaternion.toQuaternion`: the forward direction of this equiv
* `CliffordAlgebraQuaternion.ofQuaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `QuaternionAlgebra.conj` to the clifford conjugate
and vice-versa:

* `CliffordAlgebraQuaternion.toQuaternion_star`
* `CliffordAlgebraQuaternion.ofQuaternion_star`

## Dual numbers

* `CliffordAlgebraDualNumber.equiv`: `R[ε]` is equivalent as an `R`-algebra to a clifford
  algebra over `R` where `Q = 0`.

-/

@[expose] public section


open CliffordAlgebra

/-! ### The clifford algebra isomorphic to a ring -/


namespace CliffordAlgebraRing

open scoped ComplexConjugate

variable {R : Type*} [CommRing R]

@[simp]
theorem ι_eq_zero : ι (0 : QuadraticForm R Unit) = 0 :=
  Subsingleton.elim _ _

/-- Since the vector space is empty the ring is commutative. -/
instance : CommRing (CliffordAlgebra (0 : QuadraticForm R Unit)) where
  mul_comm := fun x y => by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => apply Algebra.commutes
    | ι x => simp
    | add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
    | mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc]

theorem reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) :
    x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
theorem reverse_eq_id :
    (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) →ₗ[R] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

@[simp]
theorem involute_eq_id :
    (involute : CliffordAlgebra (0 : QuadraticForm R Unit) →ₐ[R] _) = AlgHom.id R _ := by ext; simp

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun _ : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])

end CliffordAlgebraRing

/-! ### The clifford algebra isomorphic to the complex numbers -/


namespace CliffordAlgebraComplex

open scoped ComplexConjugate

/-- The quadratic form sending elements to the negation of their square. -/
def Q : QuadraticForm ℝ ℝ :=
  -QuadraticMap.sq

@[simp]
theorem Q_apply (r : ℝ) : Q r = -(r * r) :=
  rfl

/-- Intermediate result for `CliffordAlgebraComplex.equiv`: clifford algebras over
`CliffordAlgebraComplex.Q` above can be converted to `ℂ`. -/
def toComplex : CliffordAlgebra Q →ₐ[ℝ] ℂ :=
  CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩

@[simp]
theorem toComplex_ι (r : ℝ) : toComplex (ι Q r) = r • Complex.I :=
  CliffordAlgebra.lift_ι_apply _ _ r

/-- `CliffordAlgebra.involute` is analogous to `Complex.conj`. -/
@[simp]
theorem toComplex_involute (c : CliffordAlgebra Q) :
    toComplex (involute c) = conj (toComplex c) := by
  have : toComplex (involute (ι Q 1)) = conj (toComplex (ι Q 1)) := by
    simp only [involute_ι, toComplex_ι, map_neg, one_smul, Complex.conj_I]
  suffices toComplex.comp involute = Complex.conjAe.toAlgHom.comp toComplex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

/-- Intermediate result for `CliffordAlgebraComplex.equiv`: `ℂ` can be converted to
`CliffordAlgebraComplex.Q` above can be converted to. -/
def ofComplex : ℂ →ₐ[ℝ] CliffordAlgebra Q :=
  Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar, Q_apply, one_mul, map_neg, map_one]⟩

@[simp]
theorem ofComplex_I : ofComplex Complex.I = ι Q 1 :=
  Complex.liftAux_apply_I _ (by simp)

@[simp]
theorem toComplex_comp_ofComplex : toComplex.comp ofComplex = AlgHom.id ℝ ℂ := by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [ofComplex_I, toComplex_ι, one_smul]

@[simp]
theorem toComplex_ofComplex (c : ℂ) : toComplex (ofComplex c) = c :=
  AlgHom.congr_fun toComplex_comp_ofComplex c

@[simp]
theorem ofComplex_comp_toComplex : ofComplex.comp toComplex = AlgHom.id ℝ (CliffordAlgebra Q) := by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [toComplex_ι, one_smul, ofComplex_I]

@[simp]
theorem ofComplex_toComplex (c : CliffordAlgebra Q) : ofComplex (toComplex c) = c :=
  AlgHom.congr_fun ofComplex_comp_toComplex c

/-- The clifford algebras over `CliffordAlgebraComplex.Q` is isomorphic as an `ℝ`-algebra to `ℂ`. -/
@[simps!]
protected def equiv : CliffordAlgebra Q ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex

/-- The clifford algebra is commutative since it is isomorphic to the complex numbers.

TODO: prove this is true for all `CliffordAlgebra`s over a 1-dimensional vector space. -/
instance : CommRing (CliffordAlgebra Q) where
  mul_comm := fun x y =>
    CliffordAlgebraComplex.equiv.injective <| by
      rw [map_mul, mul_comm, map_mul]

/-- `reverse` is a no-op over `CliffordAlgebraComplex.Q`. -/
theorem reverse_apply (x : CliffordAlgebra Q) : x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [reverse_ι]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
theorem reverse_eq_id : (reverse : CliffordAlgebra Q →ₗ[ℝ] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

/-- `Complex.conj` is analogous to `CliffordAlgebra.involute`. -/
@[simp]
theorem ofComplex_conj (c : ℂ) : ofComplex (conj c) = involute (ofComplex c) :=
  CliffordAlgebraComplex.equiv.injective <| by
    rw [equiv_apply, equiv_apply, toComplex_involute, toComplex_ofComplex, toComplex_ofComplex]

end CliffordAlgebraComplex

/-! ### The clifford algebra isomorphic to the quaternions -/


namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ : R)

/-- `Q c₁ c₂` is a quadratic form over `R × R` such that `CliffordAlgebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
def Q : QuadraticForm R (R × R) :=
  (c₁ • QuadraticMap.sq).prod (c₂ • QuadraticMap.sq)

@[simp]
theorem Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) :=
  rfl

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  i := ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub, eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticMap.polar]
    simp

variable {c₁ c₂}

/-- Intermediate result of `CliffordAlgebraQuaternion.equiv`: clifford algebras over
`CliffordAlgebraQuaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
def toQuaternion : CliffordAlgebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,0,c₂] :=
  CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{  toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by dsimp; rw [mul_zero] }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩

@[simp]
theorem toQuaternion_ι (v : R × R) :
    toQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂]) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- The "clifford conjugate" maps to the quaternion conjugate. -/
theorem toQuaternion_star (c : CliffordAlgebra (Q c₁ c₂)) :
    toQuaternion (star c) = star (toQuaternion c) := by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/-- Map a quaternion into the clifford algebra. -/
def ofQuaternion : ℍ[R,c₁,0,c₂] →ₐ[R] CliffordAlgebra (Q c₁ c₂) :=
  (quaternionBasis c₁ c₂).liftHom

@[simp]
theorem ofQuaternion_mk (a₁ a₂ a₃ a₄ : R) :
    ofQuaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,0,c₂]) =
      algebraMap R _ a₁ + a₂ • ι (Q c₁ c₂) (1, 0) + a₃ • ι (Q c₁ c₂) (0, 1) +
        a₄ • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)) :=
  rfl

@[simp]
theorem ofQuaternion_comp_toQuaternion :
    ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra (Q c₁ c₂)) := by
  ext : 2 <;> (ext; simp)

@[simp]
theorem ofQuaternion_toQuaternion (c : CliffordAlgebra (Q c₁ c₂)) :
    ofQuaternion (toQuaternion c) = c :=
  AlgHom.congr_fun ofQuaternion_comp_toQuaternion c

@[simp]
theorem toQuaternion_comp_ofQuaternion :
    toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,0,c₂] := by
  ext : 1 <;> simp

@[simp]
theorem toQuaternion_ofQuaternion (q : ℍ[R,c₁,0,c₂]) : toQuaternion (ofQuaternion q) = q :=
  AlgHom.congr_fun toQuaternion_comp_ofQuaternion q

/-- The clifford algebra over `CliffordAlgebraQuaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps!]
protected def equiv : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,0,c₂] :=
  AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion

/-- The quaternion conjugate maps to the "clifford conjugate" (aka `star`). -/
@[simp]
theorem ofQuaternion_star (q : ℍ[R,c₁,0,c₂]) : ofQuaternion (star q) = star (ofQuaternion q) :=
  CliffordAlgebraQuaternion.equiv.injective <| by
    rw [equiv_apply, equiv_apply, toQuaternion_star, toQuaternion_ofQuaternion,
      toQuaternion_ofQuaternion]

end CliffordAlgebraQuaternion

/-! ### The clifford algebra isomorphic to the dual numbers -/


namespace CliffordAlgebraDualNumber

open scoped DualNumber

open DualNumber TrivSqZeroExt

variable {R : Type*} [CommRing R]

theorem ι_mul_ι (r₁ r₂) : ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0 := by
  rw [← mul_one r₁, ← mul_one r₂, ← smul_eq_mul r₁, ← smul_eq_mul r₂, map_smul, map_smul,
    smul_mul_smul_comm, ι_sq_scalar, QuadraticMap.zero_apply, map_zero, smul_zero]

/-- The clifford algebra over a 1-dimensional vector space with 0 quadratic form is isomorphic to
the dual numbers. -/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε] :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨
      (Algebra.ofId _ _, ι (R := R) _ 1),
      ι_mul_ι (1 : R) 1,
      fun _ => (Algebra.commutes _ _).symm⟩)
    (by ext : 1; simp) (by ext : 2; simp)

@[simp]
theorem equiv_ι (r : R) : CliffordAlgebraDualNumber.equiv (ι (R := R) _ r) = r • ε := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)

@[simp]
theorem equiv_symm_eps :
    CliffordAlgebraDualNumber.equiv.symm (eps : R[ε]) = ι (0 : QuadraticForm R R) 1 := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact DualNumber.lift_apply_eps _

end CliffordAlgebraDualNumber
