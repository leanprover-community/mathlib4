/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `TensorAlgebra R M` is isomorphic to a direct sum of tensor powers, as
`TensorAlgebra.equivDirectSum`.
-/

open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

/-- The canonical embedding from a tensor power to the tensor algebra -/
def toTensorAlgebra {n} : ⨂[R]^n M →ₗ[R] TensorAlgebra R M :=
  PiTensorProduct.lift (TensorAlgebra.tprod R M n)

@[simp]
theorem toTensorAlgebra_tprod {n} (x : Fin n → M) :
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x :=
  PiTensorProduct.lift.tprod _

@[simp]
theorem toTensorAlgebra_gOne :
    TensorPower.toTensorAlgebra (@GradedMonoid.GOne.one _ (fun n => ⨂[R]^n M) _ _) = 1 := by
  simp [GradedMonoid.GOne.one, TensorPower.toTensorAlgebra_tprod]

@[simp]
theorem toTensorAlgebra_gMul {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    TensorPower.toTensorAlgebra (@GradedMonoid.GMul.mul _ (fun n => ⨂[R]^n M) _ _ _ _ a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b := by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap, ← LinearMap.compr₂_apply, ← @LinearMap.mul_apply' R, ←
    LinearMap.compl₂_apply, ← LinearMap.comp_apply]
  refine LinearMap.congr_fun (LinearMap.congr_fun ?_ a) b
  clear! a b
  ext (a b)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, ← gMul_def,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, tprod_mul_tprod, toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  refine Eq.trans ?_ List.prod_append
  congr
  rw [List.ofFn_comp' _ (TensorAlgebra.ι R), List.ofFn_comp' _ (TensorAlgebra.ι R),
    List.ofFn_comp' _ (TensorAlgebra.ι R), ← List.map_append, List.ofFn_fin_append]

@[simp]
theorem toTensorAlgebra_galgebra_toFun (r : R) :
    TensorPower.toTensorAlgebra (DirectSum.GAlgebra.toFun (R := R) (A := fun n => ⨂[R]^n M) r) =
      algebraMap _ _ r := by
  rw [TensorPower.galgebra_toFun_def, TensorPower.algebraMap₀_eq_smul_one, LinearMap.map_smul,
    TensorPower.toTensorAlgebra_gOne, Algebra.algebraMap_eq_smul_one]

end TensorPower

namespace TensorAlgebra

/-- The canonical map from a direct sum of tensor powers to the tensor algebra. -/
def ofDirectSum : (⨁ n, ⨂[R]^n M) →ₐ[R] TensorAlgebra R M :=
  DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

@[simp]
theorem ofDirectSum_of_tprod {n} (x : Fin n → M) :
    ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n x :=
  (DirectSum.toAddMonoid_of
    (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)

/-- The canonical map from the tensor algebra to a direct sum of tensor powers. -/
def toDirectSum : TensorAlgebra R M →ₐ[R] ⨁ n, ⨂[R]^n M :=
  TensorAlgebra.lift R <|
    DirectSum.lof R ℕ (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]
theorem toDirectSum_ι (x : M) :
    toDirectSum (ι R x) =
      DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => x) :=
  TensorAlgebra.lift_ι_apply _ _

theorem ofDirectSum_comp_toDirectSum :
    ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M) := by
  ext
  simp [tprod_apply]

@[simp]
theorem ofDirectSum_toDirectSum (x : TensorAlgebra R M) :
    ofDirectSum (TensorAlgebra.toDirectSum x) = x :=
  AlgHom.congr_fun ofDirectSum_comp_toDirectSum x

@[simp]
theorem mk_reindex_cast {n m : ℕ} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ ↦ M) (Equiv.cast <| congr_arg Fin h) x) =
    GradedMonoid.mk n x :=
  Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)

@[simp]
theorem mk_reindex_fin_cast {n m : ℕ} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ ↦ M) (finCongr h) x) = GradedMonoid.mk n x := by
  rw [finCongr_eq_equivCast, mk_reindex_cast h]

/-- The product of tensor products made of a single vector is the same as a single product of
all the vectors. -/
theorem _root_.TensorPower.list_prod_gradedMonoid_mk_single (n : ℕ) (x : Fin n → M) :
    ((List.finRange n).map fun a =>
          (GradedMonoid.mk _ (PiTensorProduct.tprod R fun _ : Fin 1 => x a) :
            GradedMonoid fun n => ⨂[R]^n M)).prod =
      GradedMonoid.mk n (PiTensorProduct.tprod R x) := by
  refine Fin.consInduction ?_ ?_ x <;> clear x
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    rfl
  · intro n x₀ x ih
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    simp_rw [Function.comp_def, Fin.cons_zero, Fin.cons_succ]
    rw [ih, GradedMonoid.mk_mul_mk, TensorPower.tprod_mul_tprod]
    refine TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) ?_
    dsimp only [GradedMonoid.mk]
    rw [TensorPower.cast_tprod]
    simp_rw [Fin.append_left_eq_cons, Function.comp_def]
    congr 1 with i

theorem toDirectSum_tensorPower_tprod {n} (x : Fin n → M) :
    toDirectSum (tprod R M n x) = DirectSum.of _ n (PiTensorProduct.tprod R x) := by
  rw [tprod_apply, map_list_prod, List.map_ofFn]
  simp_rw [Function.comp_def, toDirectSum_ι]
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  rw [GradedMonoid.mk_list_dProd]
  rw [TensorPower.list_prod_gradedMonoid_mk_single]

theorem toDirectSum_comp_ofDirectSum :
    toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, ⨂[R]^n M) := by
  ext
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]

@[simp]
theorem toDirectSum_ofDirectSum (x : ⨁ n, ⨂[R]^n M) :
    TensorAlgebra.toDirectSum (ofDirectSum x) = x :=
  AlgHom.congr_fun toDirectSum_comp_ofDirectSum x

/-- The tensor algebra is isomorphic to a direct sum of tensor powers. -/
@[simps!]
def equivDirectSum : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M :=
  AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum

end TensorAlgebra
