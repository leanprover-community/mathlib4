/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped TensorProduct

namespace QuadraticForm

/-- The complexification of a quadratic form, defined by $Q_ℂ(z ⊗ v) = z^2Q(v)$. -/
@[reducible]
noncomputable def complexify (Q : QuadraticForm ℝ V) : QuadraticForm ℂ (ℂ ⊗[ℝ] V) :=
  Q.baseChange ℂ

end QuadraticForm

namespace CliffordAlgebra

/-- Auxiliary construction: note this is really just a heterobasic `CliffordAlgebra.map`. -/
noncomputable def ofComplexifyAux (Q : QuadraticForm ℝ V) :
    CliffordAlgebra Q →ₐ[ℝ] CliffordAlgebra Q.complexify :=
  CliffordAlgebra.lift Q <| by
    letI : Invertible (2 : ℂ) := invertibleTwo
    refine ⟨(ι Q.complexify).restrictScalars ℝ ∘ₗ TensorProduct.mk ℝ ℂ V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar Q.complexify (1 ⊗ₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul, one_mul, ←Algebra.algebraMap_eq_smul_one,
      ←IsScalarTower.algebraMap_apply]

@[simp] lemma ofComplexifyAux_ι (Q : QuadraticForm ℝ V) (v : V) :
    ofComplexifyAux Q (ι Q v) = ι Q.complexify (1 ⊗ₜ v) :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Convert from the complexified clifford algebra to the clifford algebra over a complexified
module. -/
noncomputable def ofComplexify (Q : QuadraticForm ℝ V) :
    ℂ ⊗[ℝ] CliffordAlgebra Q →ₐ[ℂ] CliffordAlgebra Q.complexify :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.AlgebraTensorModule.lift $
      let f : ℂ →ₗ[ℂ] _ := (Algebra.lsmul ℂ ℂ (CliffordAlgebra Q.complexify)).toLinearMap
      LinearMap.flip $ LinearMap.flip (({
        toFun := fun f : CliffordAlgebra Q.complexify →ₗ[ℂ] CliffordAlgebra Q.complexify =>
          LinearMap.restrictScalars ℝ f
        map_add' := fun f g => LinearMap.ext $ fun x => rfl
        map_smul' := fun (c : ℂ) g => LinearMap.ext $ fun x => rfl
      } : _ →ₗ[ℂ] _) ∘ₗ f) ∘ₗ (ofComplexifyAux Q).toLinearMap)
    (fun z₁ z₂ b₁ b₂ =>
      show (z₁ * z₂) • ofComplexifyAux Q (b₁ * b₂)
        = z₁ • ofComplexifyAux Q b₁ * z₂ • ofComplexifyAux Q b₂
      by rw [map_mul, smul_mul_smul])
    (fun r =>
      show r • ofComplexifyAux Q 1 = algebraMap ℂ (CliffordAlgebra Q.complexify) r
      by rw [map_one, Algebra.algebraMap_eq_smul_one])

@[simp] lemma ofComplexify_tmul_ι (Q : QuadraticForm ℝ V) (z : ℂ) (v : V) :
    ofComplexify Q (z ⊗ₜ ι Q v) = ι Q.complexify (z ⊗ₜ v) := by
  show z • ofComplexifyAux Q (ι Q v) = ι Q.complexify (z ⊗ₜ[ℝ] v)
  rw [ofComplexifyAux_ι, ←map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp] lemma ofComplexify_tmul_one (Q : QuadraticForm ℝ V) (z : ℂ) :
    ofComplexify Q (z ⊗ₜ 1) = algebraMap _ _ z := by
  show z • ofComplexifyAux Q 1 = _
  rw [map_one, ←Algebra.algebraMap_eq_smul_one]

lemma _root_.CliffordAlgebra.preserves_iff_bilin {R A M} [CommRing R] [Ring A] [Algebra R A]
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

#check 1
variable  (Q : QuadraticForm ℝ V) in
#synth IsScalarTower ℝ ℂ (ℂ ⊗[ℝ] V →ₗ[ℂ] ℂ ⊗[ℝ] CliffordAlgebra Q)

/-- Convert from the clifford algebra over a complexified module to the complexified clifford
algebra. -/
noncomputable def toComplexify (Q : QuadraticForm ℝ V) :
    CliffordAlgebra Q.complexify →ₐ[ℂ] ℂ ⊗[ℝ] CliffordAlgebra Q :=
  CliffordAlgebra.lift _ <| by
    let φ := TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (ι Q)
    refine ⟨φ, ?_⟩
    rw [CliffordAlgebra.preserves_iff_bilin _ (IsUnit.mk0 (2 : ℂ) two_ne_zero)]
    letI : IsScalarTower ℝ ℂ (ℂ ⊗[ℝ] V →ₗ[ℂ] ℂ ⊗[ℝ] CliffordAlgebra Q) :=
      LinearMap.instIsScalarTowerLinearMapInstSMulLinearMapInstSMulLinearMap
    sorry
      -- refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      -- ext v w
      -- change (1 * 1) ⊗ₜ[ℝ] (ι Q v * ι Q w) + (1 * 1) ⊗ₜ[ℝ] (ι Q w * ι Q v) =
      --   QuadraticForm.polar (Q.complexify) (1 ⊗ₜ[ℝ] v) (1 ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] 1
      -- rw [← TensorProduct.tmul_add, CliffordAlgebra.ι_mul_ι_add_swap,
      --   QuadraticForm.baseChange_polar_apply, one_mul, one_mul,
      --   Algebra.TensorProduct.algebraMap_tmul_one]

@[simp] lemma toComplexify_ι (Q : QuadraticForm ℝ V) (z : ℂ) (v : V) :
    toComplexify Q (ι Q.complexify (z ⊗ₜ v)) = z ⊗ₜ ι Q v :=
  CliffordAlgebra.lift_ι_apply _ _ _

lemma toComplexify_comp_involute (Q : QuadraticForm ℝ V) :
    (toComplexify Q).comp (involute : CliffordAlgebra Q.complexify →ₐ[ℂ] _) =
      (Algebra.TensorProduct.map (AlgHom.id _ _) involute).comp (toComplexify Q) := by
  ext v
  show toComplexify Q (involute (ι Q.complexify (1 ⊗ₜ[ℝ] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        ℂ ⊗[ℝ] CliffordAlgebra Q →ₐ[ℂ] _)
      (toComplexify Q (ι Q.complexify (1 ⊗ₜ[ℝ] v)))
  rw [toComplexify_ι, involute_ι, map_neg (toComplexify Q), toComplexify_ι,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, involute_ι, TensorProduct.tmul_neg]

/-- The involution acts only on the right of the tensor product. -/
lemma toComplexify_involute (Q : QuadraticForm ℝ V) (x : CliffordAlgebra Q.complexify) :
    toComplexify Q (involute x) =
      TensorProduct.map LinearMap.id (involute.toLinearMap) (toComplexify Q x) :=
  FunLike.congr_fun (toComplexify_comp_involute Q) x

open MulOpposite

-- /-- Auxiliary lemma used to prove `toComplexify_reverse` without needing induction. -/
-- lemma toComplexify_comp_reverse_aux (Q : QuadraticForm ℝ V) :
--     (toComplexify Q).op.comp (reverse_aux Q.complexify) =
--       ((Algebra.TensorProduct.op_alg_equiv ℂ).to_algHom.comp $
--         (Algebra.TensorProduct.map' ((algHom.id ℂ ℂ).to_opposite commute.all) (reverse_aux Q)).comp
--           (toComplexify Q)) := by
--   ext v
--   show
--     op (toComplexify Q (reverse (ι Q.complexify (1 ⊗ₜ[ℝ] v)))) =
--     Algebra.TensorProduct.op_alg_equiv ℂ
--       (Algebra.TensorProduct.map' ((algHom.id ℂ ℂ).to_opposite commute.all) (reverse_aux Q)
--          (toComplexify Q (ι Q.complexify (1 ⊗ₜ[ℝ] v))))
--   rw [toComplexify_ι, reverse_ι, toComplexify_ι, Algebra.TensorProduct.map'_tmul,
--     Algebra.TensorProduct.op_alg_equiv_tmul, unop_reverse_aux, reverse_ι]
--   rfl

-- /-- `reverse` acts only on the right of the tensor product. -/
-- lemma toComplexify_reverse (Q : QuadraticForm ℝ V) (x : CliffordAlgebra Q.complexify) :
--     toComplexify Q (reverse x) =
--       TensorProduct.map LinearMap.id (reverse : _ →ₗ[ℝ] _) (toComplexify Q x) := by
--   have := fun_like.congr_fun (toComplexify_comp_reverse_aux Q) x
--   refine (congr_arg unop this).trans _; clear this
--   refine (TensorProduct.AlgebraTensorModule.map_map _ _ _ _ _).trans _
--   erw [←reverse_eq_reverse_aux, algHom.toLinearMap_to_opposite,
--     TensorProduct.AlgebraTensorModule.map_apply]

attribute [ext] TensorProduct.ext

lemma toComplexify_comp_ofComplexify (Q : QuadraticForm ℝ V) :
    (toComplexify Q).comp (ofComplexify Q) = AlgHom.id _ _ := by
  ext z : 2
  · change toComplexify Q (ofComplexify Q (z ⊗ₜ[ℝ] 1)) = z ⊗ₜ[ℝ] 1
    rw [ofComplexify_tmul_one, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.id.map_eq_self]
  · ext v : 1
    change toComplexify Q (ofComplexify Q (1 ⊗ₜ[ℝ] ι Q v)) = 1 ⊗ₜ[ℝ] ι Q v
    rw [ofComplexify_tmul_ι, toComplexify_ι]

@[simp] lemma toComplexify_ofComplexify (Q : QuadraticForm ℝ V) (x : ℂ ⊗[ℝ] CliffordAlgebra Q) :
    toComplexify Q (ofComplexify Q x) = x :=
  AlgHom.congr_fun (toComplexify_comp_ofComplexify Q : _) x

lemma ofComplexify_comp_toComplexify (Q : QuadraticForm ℝ V) :
    (ofComplexify Q).comp (toComplexify Q) = AlgHom.id _ _ := by
  ext x
  show ofComplexify Q (toComplexify Q (ι Q.complexify (1 ⊗ₜ[ℝ] x))) = ι Q.complexify (1 ⊗ₜ[ℝ] x)
  rw [toComplexify_ι, ofComplexify_tmul_ι]

@[simp] lemma ofComplexify_toComplexify
    (Q : QuadraticForm ℝ V) (x : CliffordAlgebra Q.complexify) :
    ofComplexify Q (toComplexify Q x) = x :=
  AlgHom.congr_fun (ofComplexify_comp_toComplexify Q : _) x

/-- Complexifying the vector space of a clifford algebra is isomorphic as a ℂ-algebra to
complexifying the clifford algebra itself; $Cℓ(ℂ ⊗_ℝ V, Q_ℂ) ≅ ℂ ⊗_ℝ Cℓ(V, Q)$.

This is `CliffordAlgebra.toComplexify` and `CliffordAlgebra.ofComplexify` as an equivalence. -/
@[simps!]
noncomputable def equivComplexify (Q : QuadraticForm ℝ V) :
    CliffordAlgebra Q.complexify ≃ₐ[ℂ] ℂ ⊗[ℝ] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toComplexify Q) (ofComplexify Q)
    (toComplexify_comp_ofComplexify Q)
    (ofComplexify_comp_toComplexify Q)
