/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The base change of a clifford algebra

In this file we show the isomorphism

* `CliffordAlgebra.equivBaseChange A Q` :
  `CliffordAlgebra (Q.baseChange A) ≃ₐ[A] (A ⊗[R] CliffordAlgebra Q)`
  with forward direction `CliffordAlgebra.toBasechange A Q` and reverse direction
  `CliffordAlgebra.ofBasechange A Q`.

This covers a more general case of the complexification of clifford algebras (as described in §2.2
of https://empg.maths.ed.ac.uk/Activities/Spin/Lecture2.pdf), where ℂ and ℝ are replaced by an
`R`-algebra `A` (where `2 : R` is invertible).

We show the additional results:

* `CliffordAlgebra.toBasechange_ι`: the effect of base-changing pure vectors.
* `CliffordAlgebra.ofBasechange_tmul_ι`: the effect of un-base-changing a tensor of a pure vectors.
* `CliffordAlgebra.toBasechange_involute`: the effect of base-changing an involution.
* `CliffordAlgebra.toBasechange_reverse`: the effect of base-changing a reversal.
-/

variable {R A V : Type*}
variable [CommRing R] [CommRing A] [AddCommGroup V]
variable [Algebra R A] [Module R V]
variable [Invertible (2 : R)]

open scoped TensorProduct

namespace CliffordAlgebra

variable (A)

/-- Auxiliary construction: note this is really just a heterobasic `CliffordAlgebra.map`. -/
def ofBaseChangeAux (Q : QuadraticForm R V) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra (Q.baseChange A) :=
  CliffordAlgebra.lift Q <| by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 ⊗ₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul, one_mul, ← Algebra.algebraMap_eq_smul_one,
      ← IsScalarTower.algebraMap_apply]

@[simp] theorem ofBaseChangeAux_ι (Q : QuadraticForm R V) (v : V) :
    ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (1 ⊗ₜ v) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- Convert from the base-changed clifford algebra to the clifford algebra over a base-changed
module. -/
def ofBaseChange (Q : QuadraticForm R V) :
    A ⊗[R] CliffordAlgebra Q →ₐ[A] CliffordAlgebra (Q.baseChange A) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A Q)
    fun _a _x => Algebra.commutes _ _

@[simp] theorem ofBaseChange_tmul_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    ofBaseChange A Q (z ⊗ₜ ι Q v) = ι (Q.baseChange A) (z ⊗ₜ v) := by
  change algebraMap _ _ z * ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z ⊗ₜ[R] v)
  rw [ofBaseChangeAux_ι, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

@[simp] theorem ofBaseChange_tmul_one (Q : QuadraticForm R V) (z : A) :
    ofBaseChange A Q (z ⊗ₜ 1) = algebraMap _ _ z := by
  change algebraMap _ _ z * ofBaseChangeAux A Q 1 = _
  rw [map_one, mul_one]

/-- Convert from the clifford algebra over a base-changed module to the base-changed clifford
algebra. -/
def toBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift _ <| by
    refine ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (ι Q), ?_⟩
    letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    letI : Invertible (2 : A ⊗[R] CliffordAlgebra Q) :=
      (Invertible.map (algebraMap R _) 2).copy 2 (map_ofNat _ _).symm
    suffices hpure_tensor : ∀ v w, (1 * 1) ⊗ₜ[R] (ι Q v * ι Q w) + (1 * 1) ⊗ₜ[R] (ι Q w * ι Q v) =
        QuadraticMap.polarBilin (Q.baseChange A) (1 ⊗ₜ[R] v) (1 ⊗ₜ[R] w) ⊗ₜ[R] 1 by
      -- the crux is that by converting to a statement about linear maps instead of quadratic forms,
      -- we then have access to all the partially-applied `ext` lemmas.
      rw [CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible _)]
      refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      ext v w
      dsimp
      exact hpure_tensor v w
    intros v w
    rw [← TensorProduct.tmul_add, CliffordAlgebra.ι_mul_ι_add_swap,
      QuadraticForm.polarBilin_baseChange, LinearMap.BilinForm.baseChange_tmul, one_mul,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, QuadraticMap.polarBilin_apply_apply]

@[simp] theorem toBaseChange_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    toBaseChange A Q (ι (Q.baseChange A) (z ⊗ₜ v)) = z ⊗ₜ ι Q v :=
  CliffordAlgebra.lift_ι_apply _ _ _

theorem toBaseChange_comp_involute (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (involute : CliffordAlgebra (Q.baseChange A) →ₐ[A] _) =
      (Algebra.TensorProduct.map (AlgHom.id _ _) involute).comp (toBaseChange A Q) := by
  ext v
  change toBaseChange A Q (involute (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A ⊗[R] CliffordAlgebra Q →ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
  rw [toBaseChange_ι, involute_ι, map_neg (toBaseChange A Q), toBaseChange_ι,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, involute_ι, TensorProduct.tmul_neg]

/-- The involution acts only on the right of the tensor product. -/
theorem toBaseChange_involute (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (involute x) =
      TensorProduct.map LinearMap.id (involute.toLinearMap) (toBaseChange A Q x) :=
  DFunLike.congr_fun (toBaseChange_comp_involute A Q) x

open MulOpposite

/-- Auxiliary theorem used to prove `toBaseChange_reverse` without needing induction. -/
theorem toBaseChange_comp_reverseOp (Q : QuadraticForm R V) :
    (toBaseChange A Q).op.comp reverseOp =
      ((Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)).toAlgHom.comp <|
        (Algebra.TensorProduct.map
          (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))).comp
        (toBaseChange A Q)) := by
  ext v
  change op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))) =
    Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
      (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))
        (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v))))
  rw [toBaseChange_ι, reverse_ι, toBaseChange_ι, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.opAlgEquiv_tmul, reverseOp_ι]
  rfl

/-- `reverse` acts only on the right of the tensor product. -/
theorem toBaseChange_reverse (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (reverse x) =
      TensorProduct.map LinearMap.id reverse (toBaseChange A Q x) := by
  have := DFunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.map_comp _ _ _ _).symm _).trans ?_
  rw [reverse, ← AlgEquiv.toLinearMap, ← AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearEquiv_toOpposite]
  dsimp
  -- `simp` fails here due to a timeout looking for a `Subsingleton` instance!?
  rw [LinearEquiv.self_trans_symm]
  rfl

attribute [ext] TensorProduct.ext

theorem toBaseChange_comp_ofBaseChange (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (ofBaseChange A Q) = AlgHom.id _ _ := by
  ext v
  simp

@[simp] theorem toBaseChange_ofBaseChange (Q : QuadraticForm R V) (x : A ⊗[R] CliffordAlgebra Q) :
    toBaseChange A Q (ofBaseChange A Q x) = x :=
  AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q :) x

theorem ofBaseChange_comp_toBaseChange (Q : QuadraticForm R V) :
    (ofBaseChange A Q).comp (toBaseChange A Q) = AlgHom.id _ _ := by
  ext x
  change ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] x)))
    = ι (Q.baseChange A) (1 ⊗ₜ[R] x)
  rw [toBaseChange_ι, ofBaseChange_tmul_ι]

@[simp] theorem ofBaseChange_toBaseChange
    (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    ofBaseChange A Q (toBaseChange A Q x) = x :=
  AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q :) x

/-- Base-changing the vector space of a clifford algebra is isomorphic as an A-algebra to
base-changing the clifford algebra itself; <|Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)<|.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an equivalence. -/
@[simps!]
def equivBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

end CliffordAlgebra
