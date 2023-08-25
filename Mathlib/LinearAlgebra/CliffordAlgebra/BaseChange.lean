/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.TensorProduct

#check 1

variable {R A V : Type*}
variable [CommRing R] [CommRing A] [AddCommGroup V]
variable [Algebra R A] [Module R V] [Module A V] [IsScalarTower R A V]
variable [Invertible (2 : R)]

open scoped TensorProduct


namespace CliffordAlgebra

variable (A)

/-- Auxiliary construction: note this is really just a heterobasic `CliffordAlgebra.map`. -/
noncomputable def ofBaseChangeAux (Q : QuadraticForm R V) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra (Q.baseChange A) :=
  CliffordAlgebra.lift Q <| by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 ⊗ₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul, one_mul, ←Algebra.algebraMap_eq_smul_one,
      ←IsScalarTower.algebraMap_apply]

@[simp] theorem ofBaseChangeAux_ι (Q : QuadraticForm R V) (v : V) :
    ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (1 ⊗ₜ v) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- Convert from the base-changed clifford algebra to the clifford algebra over a base-changed
module. -/
noncomputable def ofBaseChange (Q : QuadraticForm R V) :
    A ⊗[R] CliffordAlgebra Q →ₐ[A] CliffordAlgebra (Q.baseChange A) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.AlgebraTensorModule.lift $
      let f : A →ₗ[A] _ := (Algebra.lsmul A A (CliffordAlgebra (Q.baseChange A))).toLinearMap
      LinearMap.flip $ LinearMap.flip (({
        toFun := fun f : CliffordAlgebra (Q.baseChange A) →ₗ[A] CliffordAlgebra (Q.baseChange A) =>
          LinearMap.restrictScalars R f
        map_add' := fun f g => LinearMap.ext $ fun x => rfl
        map_smul' := fun (c : A) g => LinearMap.ext $ fun x => rfl
      } : _ →ₗ[A] _) ∘ₗ f) ∘ₗ (ofBaseChangeAux A Q).toLinearMap)
    (fun z₁ z₂ b₁ b₂ =>
      show (z₁ * z₂) • ofBaseChangeAux A Q (b₁ * b₂)
        = z₁ • ofBaseChangeAux A Q b₁ * z₂ • ofBaseChangeAux A Q b₂
      by rw [map_mul, smul_mul_smul])
    (fun r =>
      show r • ofBaseChangeAux A Q 1 = algebraMap A (CliffordAlgebra (Q.baseChange A)) r
      by rw [map_one, Algebra.algebraMap_eq_smul_one])

@[simp] theorem ofBaseChange_tmul_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    ofBaseChange A Q (z ⊗ₜ ι Q v) = ι (Q.baseChange A) (z ⊗ₜ v) := by
  show z • ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z ⊗ₜ[R] v)
  rw [ofBaseChangeAux_ι, ←map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp] theorem ofBaseChange_tmul_one (Q : QuadraticForm R V) (z : A) :
    ofBaseChange A Q (z ⊗ₜ 1) = algebraMap _ _ z := by
  show z • ofBaseChangeAux A Q 1 = _
  rw [map_one, ←Algebra.algebraMap_eq_smul_one]

theorem _root_.CliffordAlgebra.preserves_iff_bilin {R A M} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
    (h2 : IsUnit (2 : R))
    (f : M →ₗ[R] A) :
    (∀ x, f x * f x = algebraMap _ _ (Q x)) ↔
      ((LinearMap.mul R A).compl₂ f) ∘ₗ f + ((LinearMap.mul R A).flip.compl₂ f) ∘ₗ f =
        Q.polarBilin.toLin.compr₂ (Algebra.linearMap R A) := by
  simp_rw [FunLike.ext_iff]
  dsimp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    Algebra.linearMap_apply, LinearMap.mul_apply', BilinForm.toLin_apply, LinearMap.add_apply,
    LinearMap.flip_apply]
  have h2a := h2.map (algebraMap R A)
  refine ⟨fun h x y => ?_, fun h x => ?_⟩
  · rw [QuadraticForm.polarBilin_apply, QuadraticForm.polar, sub_sub, map_sub, map_add,
      ←h x, ←h y, ←h (x + y), eq_sub_iff_add_eq, map_add,
      add_mul, mul_add, mul_add, add_comm (f x * f x) (f x * f y),
      add_add_add_comm]
  · apply h2a.mul_left_cancel
    simp_rw [←Algebra.smul_def, two_smul]
    rw [h x x, QuadraticForm.polarBilin_apply, QuadraticForm.polar_self, two_mul, map_add]

set_option maxHeartbeats 400000 in
/-- Convert from the clifford algebra over a base-changed module to the base-changed clifford
algebra. -/
noncomputable def toBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift _ <| by
    let φ := TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (ι Q)
    refine ⟨φ, ?_⟩
    letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    rw [CliffordAlgebra.preserves_iff_bilin _ (isUnit_of_invertible _)]
    letI : IsScalarTower R A (A ⊗[R] V →ₗ[A] A ⊗[R] CliffordAlgebra Q) :=
      LinearMap.instIsScalarTowerLinearMapInstSMulLinearMapInstSMulLinearMap
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    ext v w
    change (1 * 1) ⊗ₜ[R] (ι Q v * ι Q w) + (1 * 1) ⊗ₜ[R] (ι Q w * ι Q v) =
      QuadraticForm.polar (Q.baseChange A) (1 ⊗ₜ[R] v) (1 ⊗ₜ[R] w) ⊗ₜ[R] 1
    rw [← TensorProduct.tmul_add, CliffordAlgebra.ι_mul_ι_add_swap]
      -- QuadraticForm.baseChange_polar_apply, one_mul, one_mul,
      -- Algebra.TensorProduct.algebraMap_tmul_one]
    sorry

@[simp] theorem toBaseChange_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    toBaseChange A Q (ι (Q.baseChange A) (z ⊗ₜ v)) = z ⊗ₜ ι Q v :=
  CliffordAlgebra.lift_ι_apply _ _ _

theorem toBaseChange_comp_involute (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (involute : CliffordAlgebra (Q.baseChange A) →ₐ[A] _) =
      (Algebra.TensorProduct.map (AlgHom.id _ _) involute).comp (toBaseChange A Q) := by
  ext v
  show toBaseChange A Q (involute (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A ⊗[R] CliffordAlgebra Q →ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
  rw [toBaseChange_ι, involute_ι, map_neg (toBaseChange A Q), toBaseChange_ι,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, involute_ι, TensorProduct.tmul_neg]

/-- The involution acts only on the right of the tensor product. -/
theorem toBaseChange_involute (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (involute x) =
      TensorProduct.map LinearMap.id (involute.toLinearMap) (toBaseChange A Q x) :=
  FunLike.congr_fun (toBaseChange_comp_involute A Q) x

open MulOpposite

/-- Auxiliary theorem used to prove `toBaseChange_reverse` without needing induction. -/
theorem toBaseChange_comp_reverseOp (Q : QuadraticForm R V) :
    (toBaseChange A Q).op.comp (reverseOp (Q := Q.baseChange A)) =
      ((Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)).toAlgHom.comp $
        (Algebra.TensorProduct.map ((AlgHom.id A A).toOpposite Commute.all) (reverseOp (Q := Q))).comp
          (toBaseChange A Q)) := by
  ext v
  save
  dsimp only [TensorProduct.AlgebraTensorModule.curry_apply, AlgHom.comp_toLinearMap,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
    Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.op_apply_apply, AlgEquiv.toAlgHom_eq_coe,
    AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearMap_apply]
  -- show
  --   op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))) =
  --   Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
  --     (Algebra.TensorProduct.map ((algHom.id A A).toOpposite Commute.all) (reverseOp Q)
  --        (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v))))
  rw [toBaseChange_ι, reverseOp_ι, unop_op, toBaseChange_ι, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.opAlgEquiv_tmul, reverseOp_ι, unop_op]
  rfl

/-- `reverse` acts only on the right of the tensor product. -/
theorem toBaseChange_reverse (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (reverse x) =
      TensorProduct.map LinearMap.id (reverse (Q := Q)) (toBaseChange A Q x) := by
  have := FunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (TensorProduct.AlgebraTensorModule.map_comp_map _ _ _ _ _).trans ?_
  erw [reverse, AlgHom.toLinearMap_toOpposite,
    TensorProduct.AlgebraTensorModule.map_apply]

attribute [ext] TensorProduct.ext

theorem toBaseChange_comp_ofBaseChange (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (ofBaseChange A Q) = AlgHom.id _ _ := by
  ext z : 2
  · change toBaseChange A Q (ofBaseChange A Q (z ⊗ₜ[R] 1)) = z ⊗ₜ[R] 1
    rw [ofBaseChange_tmul_one, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.id.map_eq_self]
  · ext v : 1
    change toBaseChange A Q (ofBaseChange A Q (1 ⊗ₜ[R] ι Q v)) = 1 ⊗ₜ[R] ι Q v
    rw [ofBaseChange_tmul_ι, toBaseChange_ι]

@[simp] theorem toBaseChange_ofBaseChange (Q : QuadraticForm R V) (x : A ⊗[R] CliffordAlgebra Q) :
    toBaseChange A Q (ofBaseChange A Q x) = x :=
  AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q : _) x

theorem ofBaseChange_comp_toBaseChange (Q : QuadraticForm R V) :
    (ofBaseChange A Q).comp (toBaseChange A Q) = AlgHom.id _ _ := by
  ext x
  show ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] x))) = ι (Q.baseChange A) (1 ⊗ₜ[R] x)
  rw [toBaseChange_ι, ofBaseChange_tmul_ι]

@[simp] theorem ofBaseChange_toBaseChange
    (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    ofBaseChange A Q (toBaseChange A Q x) = x :=
  AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q : _) x

/-- Base-changing the vector space of a clifford algebra is isomorphic as an A-algebra to
base-changing the clifford algebra itself; $Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)$.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an equivalence. -/
@[simps!]
noncomputable def equivBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)
