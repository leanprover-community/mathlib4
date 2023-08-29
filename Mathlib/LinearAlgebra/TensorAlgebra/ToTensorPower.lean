/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.TensorPower

#align_import linear_algebra.tensor_algebra.to_tensor_power from "leanprover-community/mathlib"@"d97a0c9f7a7efe6d76d652c5a6b7c9c634b70e0a"

/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `TensorAlgebra R M` is isomorphic to a direct sum of tensor powers, as
`TensorAlgebra.equivDirectSum`.
-/


open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

/-- The canonical embedding from a tensor power to the tensor algebra -/
def toTensorAlgebra {n} : (⨂[R]^n) M →ₗ[R] TensorAlgebra R M :=
  PiTensorProduct.lift (TensorAlgebra.tprod R M n)
#align tensor_power.to_tensor_algebra TensorPower.toTensorAlgebra

@[simp]
theorem toTensorAlgebra_tprod {n} (x : Fin n → M) :
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x :=
  PiTensorProduct.lift.tprod _
#align tensor_power.to_tensor_algebra_tprod TensorPower.toTensorAlgebra_tprod

@[simp]
theorem toTensorAlgebra_gOne :
    TensorPower.toTensorAlgebra (@GradedMonoid.GOne.one _ (fun n => (⨂[R]^n) M) _ _) = 1 :=
  TensorPower.toTensorAlgebra_tprod _
#align tensor_power.to_tensor_algebra_ghas_one TensorPower.toTensorAlgebra_gOne

@[simp]
theorem toTensorAlgebra_gMul {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    TensorPower.toTensorAlgebra (@GradedMonoid.GMul.mul _ (fun n => (⨂[R]^n) M) _ _ _ _ a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b := by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap, ← LinearMap.compr₂_apply, ← @LinearMap.mul_apply' R, ←
    LinearMap.compl₂_apply, ← LinearMap.comp_apply]
  refine' LinearMap.congr_fun (LinearMap.congr_fun _ a) b
  -- ⊢ LinearMap.compr₂ (LinearMap.compr₂ (TensorProduct.mk R ((⨂[R]^i) M) ((⨂[R]^j …
  clear! a b
  -- ⊢ LinearMap.compr₂ (LinearMap.compr₂ (TensorProduct.mk R ((⨂[R]^i) M) ((⨂[R]^j …
  ext (a b)
  -- ⊢ ↑(LinearMap.compMultilinearMap (↑(LinearMap.compMultilinearMap (LinearMap.co …
  -- Porting note: pulled the next two lines out of the long `simp only` below.
  simp only [LinearMap.compMultilinearMap_apply]
  -- ⊢ ↑(↑(LinearMap.compr₂ (LinearMap.compr₂ (TensorProduct.mk R ((⨂[R]^i) M) ((⨂[ …
  rw [LinearMap.compr₂_apply, ← gMul_eq_coe_linearMap]
  -- ⊢ ↑toTensorAlgebra (GradedMonoid.GMul.mul (↑(PiTensorProduct.tprod R) a) (↑(Pi …
  simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
    TensorPower.tprod_mul_tprod, TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply, ←
    gMul_eq_coe_linearMap]
  refine' Eq.trans _ List.prod_append
  -- ⊢ List.prod (List.ofFn fun i_1 => ↑(TensorAlgebra.ι R) (Fin.append a b i_1)) = …
  -- Porting note: was `congr`
  apply congr_arg
  -- ⊢ (List.ofFn fun i_1 => ↑(TensorAlgebra.ι R) (Fin.append a b i_1)) = (List.ofF …
  -- Porting note: `erw` for `Function.comp`
  erw [← List.map_ofFn _ (TensorAlgebra.ι R), ← List.map_ofFn _ (TensorAlgebra.ι R), ←
    List.map_ofFn _ (TensorAlgebra.ι R), ← List.map_append, List.ofFn_fin_append]
#align tensor_power.to_tensor_algebra_ghas_mul TensorPower.toTensorAlgebra_gMul

@[simp]
theorem toTensorAlgebra_galgebra_toFun (r : R) :
    TensorPower.toTensorAlgebra (DirectSum.GAlgebra.toFun (R := R) (A := fun n => (⨂[R]^n) M) r) =
      algebraMap _ _ r := by
  rw [TensorPower.galgebra_toFun_def, TensorPower.algebraMap₀_eq_smul_one, LinearMap.map_smul,
    TensorPower.toTensorAlgebra_gOne, Algebra.algebraMap_eq_smul_one]
#align tensor_power.to_tensor_algebra_galgebra_to_fun TensorPower.toTensorAlgebra_galgebra_toFun

end TensorPower

namespace TensorAlgebra

/-- The canonical map from a direct sum of tensor powers to the tensor algebra. -/
def ofDirectSum : (⨁ n, (⨂[R]^n) M) →ₐ[R] TensorAlgebra R M :=
  DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul) TensorPower.toTensorAlgebra_galgebra_toFun
#align tensor_algebra.of_direct_sum TensorAlgebra.ofDirectSum

@[simp]
theorem ofDirectSum_of_tprod {n} (x : Fin n → M) :
    ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n x :=
  (DirectSum.toAddMonoid_of
    (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)
#align tensor_algebra.of_direct_sum_of_tprod TensorAlgebra.ofDirectSum_of_tprod

/-- The canonical map from the tensor algebra to a direct sum of tensor powers. -/
def toDirectSum : TensorAlgebra R M →ₐ[R] ⨁ n, (⨂[R]^n) M :=
  TensorAlgebra.lift R <|
    DirectSum.lof R ℕ (fun n => (⨂[R]^n) M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap
#align tensor_algebra.to_direct_sum TensorAlgebra.toDirectSum

@[simp]
theorem toDirectSum_ι (x : M) :
    toDirectSum (ι R x) =
      DirectSum.of (fun n => (⨂[R]^n) M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => x) :=
  TensorAlgebra.lift_ι_apply _ _
#align tensor_algebra.to_direct_sum_ι TensorAlgebra.toDirectSum_ι

theorem ofDirectSum_comp_toDirectSum :
    ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M) := by
  ext
  -- ⊢ ↑(LinearMap.comp (AlgHom.toLinearMap (AlgHom.comp ofDirectSum toDirectSum))  …
  simp [DirectSum.lof_eq_of, tprod_apply]
  -- 🎉 no goals
#align tensor_algebra.of_direct_sum_comp_to_direct_sum TensorAlgebra.ofDirectSum_comp_toDirectSum

@[simp]
theorem ofDirectSum_toDirectSum (x : TensorAlgebra R M) :
    ofDirectSum (TensorAlgebra.toDirectSum x) = x :=
  AlgHom.congr_fun ofDirectSum_comp_toDirectSum x
#align tensor_algebra.of_direct_sum_to_direct_sum TensorAlgebra.ofDirectSum_toDirectSum

@[simp]
theorem mk_reindex_cast {n m : ℕ} (h : n = m) (x : (⨂[R]^n) M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R M (Equiv.cast <| congr_arg Fin h) x) =
    GradedMonoid.mk n x :=
  Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)
#align tensor_algebra.mk_reindex_cast TensorAlgebra.mk_reindex_cast

@[simp]
theorem mk_reindex_fin_cast {n m : ℕ} (h : n = m) (x : (⨂[R]^n) M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R M (Fin.castIso h).toEquiv x) = GradedMonoid.mk n x :=
  by rw [Fin.castIso_to_equiv, mk_reindex_cast h]
     -- 🎉 no goals
#align tensor_algebra.mk_reindex_fin_cast TensorAlgebra.mk_reindex_fin_cast

/-- The product of tensor products made of a single vector is the same as a single product of
all the vectors. -/
theorem _root_.TensorPower.list_prod_gradedMonoid_mk_single (n : ℕ) (x : Fin n → M) :
    ((List.finRange n).map fun a =>
          (GradedMonoid.mk _ (PiTensorProduct.tprod R fun _ : Fin 1 => x a) :
            GradedMonoid fun n => (⨂[R]^n) M)).prod =
      GradedMonoid.mk n (PiTensorProduct.tprod R x) := by
  refine' Fin.consInduction _ _ x <;> clear x
  -- ⊢ List.prod (List.map (fun a => GradedMonoid.mk 1 (⨂ₜ[R] (x : Fin 1), Fin.elim …
                                      -- ⊢ List.prod (List.map (fun a => GradedMonoid.mk 1 (⨂ₜ[R] (x : Fin 1), Fin.elim …
                                      -- ⊢ ∀ {n : ℕ} (x₀ : M) (x : Fin n → M), List.prod (List.map (fun a => GradedMono …
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    -- ⊢ 1 = GradedMonoid.mk 0 (↑(PiTensorProduct.tprod R) Fin.elim0)
    rfl
    -- 🎉 no goals
  · intro n x₀ x ih
    -- ⊢ List.prod (List.map (fun a => GradedMonoid.mk 1 (⨂ₜ[R] (x_1 : Fin 1), Fin.co …
    rw [List.finRange_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    -- ⊢ GradedMonoid.mk 1 (⨂ₜ[R] (x_1 : Fin 1), Fin.cons x₀ x 0) * List.prod (List.m …
    simp_rw [Function.comp, Fin.cons_zero, Fin.cons_succ]
    -- ⊢ GradedMonoid.mk 1 (⨂ₜ[R] (x : Fin 1), x₀) * List.prod (List.map (fun x_1 =>  …
    rw [ih, GradedMonoid.mk_mul_mk, TensorPower.tprod_mul_tprod]
    -- ⊢ GradedMonoid.mk (1 + n) (↑(PiTensorProduct.tprod R) (Fin.append (fun x => x₀ …
    refine' TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) _
    -- ⊢ ↑(TensorPower.cast R M (_ : 1 + n = n + 1)) (GradedMonoid.mk (1 + n) (↑(PiTe …
    dsimp only [GradedMonoid.mk]
    -- ⊢ ↑(TensorPower.cast R M (_ : 1 + n = n + 1)) (↑(PiTensorProduct.tprod R) (Fin …
    rw [TensorPower.cast_tprod]
    -- ⊢ ↑(PiTensorProduct.tprod R) (Fin.append (fun x => x₀) x ∘ ↑(Fin.castIso (_ :  …
    simp_rw [Fin.append_left_eq_cons, Function.comp]
    -- ⊢ (⨂ₜ[R] (x_1 : Fin (n + 1)), Fin.cons x₀ x (↑(Fin.castIso (_ : 1 + n = n + 1) …
    congr 1 with i
    -- 🎉 no goals
#align tensor_power.list_prod_graded_monoid_mk_single TensorPower.list_prod_gradedMonoid_mk_single

theorem toDirectSum_tensorPower_tprod {n} (x : Fin n → M) :
    toDirectSum (tprod R M n x) = DirectSum.of _ n (PiTensorProduct.tprod R x) := by
  rw [tprod_apply, AlgHom.map_list_prod, List.map_ofFn]
  -- ⊢ List.prod (List.ofFn (↑toDirectSum ∘ fun i => ↑(ι R) (x i))) = ↑(DirectSum.o …
  simp_rw [Function.comp, toDirectSum_ι]
  -- ⊢ List.prod (List.ofFn fun x_1 => ↑(DirectSum.of (fun n => (⨂[R]^n) M) 1) (⨂ₜ[ …
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  -- ⊢ ↑(DirectSum.of (fun n => (⨂[R]^n) M) (List.dProdIndex (List.finRange n) fun  …
  apply DirectSum.of_eq_of_gradedMonoid_eq
  -- ⊢ GradedMonoid.mk (List.dProdIndex (List.finRange n) fun x => 1) (List.dProd ( …
  rw [GradedMonoid.mk_list_dProd]
  -- ⊢ List.prod (List.map (fun a => GradedMonoid.mk 1 (⨂ₜ[R] (x_1 : Fin 1), x a))  …
  rw [TensorPower.list_prod_gradedMonoid_mk_single]
  -- 🎉 no goals
#align tensor_algebra.to_direct_sum_tensor_power_tprod TensorAlgebra.toDirectSum_tensorPower_tprod

theorem toDirectSum_comp_ofDirectSum :
    toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, (⨂[R]^n) M) := by
  ext
  -- ⊢ ↑(LinearMap.compMultilinearMap (LinearMap.comp (AlgHom.toLinearMap (AlgHom.c …
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]
  -- 🎉 no goals
#align tensor_algebra.to_direct_sum_comp_of_direct_sum TensorAlgebra.toDirectSum_comp_ofDirectSum

@[simp]
theorem toDirectSum_ofDirectSum (x : ⨁ n, (⨂[R]^n) M) :
    TensorAlgebra.toDirectSum (ofDirectSum x) = x :=
  AlgHom.congr_fun toDirectSum_comp_ofDirectSum x
#align tensor_algebra.to_direct_sum_of_direct_sum TensorAlgebra.toDirectSum_ofDirectSum

/-- The tensor algebra is isomorphic to a direct sum of tensor powers. -/
@[simps!]
def equivDirectSum : TensorAlgebra R M ≃ₐ[R] ⨁ n, (⨂[R]^n) M :=
  AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum
#align tensor_algebra.equiv_direct_sum TensorAlgebra.equivDirectSum

end TensorAlgebra
