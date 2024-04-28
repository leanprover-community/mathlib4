/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Algebra.Operations

/-!

# Some results on tensor product of submodules

## Linear maps induced by multiplication for submodules

Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`). We define some linear maps
induced by the multiplication in `S` (see also `LinearMap.mul'`), which are
mainly used in the definition of linearly disjointness (`Submodule.LinearDisjoint`).

- `Submodule.mulMap`: the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  induced by the multiplication in `S`, whose image is `M * N` (`Submodule.mulMap_range`).

- `Submodule.mulMap'`: the natural map `M ⊗[R] N →ₗ[R] M * N`
  induced by multiplication in `S`, which is surjective (`Submodule.mulMap'_surjective`).

- `Submodule.lTensorOne`: the natural isomorphism between
  `i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the structure map.
  This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`.

- `Submodule.rTensorOne`: the natural isomorphism between
  `M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the structure map.
  This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`.

- `Submodule.mulLeftMap`: if `m : ι → M` is a family of elements, then there is an `R`-linear map
  from `ι →₀ N` to `S` which maps `{ n_i }` to the sum of `m_i * n_i`.

- `Submodule.mulRightMap`: if `n : ι → N` is a family of elements, then there is an `R`-linear map
  from `ι →₀ M` to `S` which maps `{ m_i }` to the sum of `m_i * n_i`.

-/

open scoped Classical TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

section mulMap

-- can't use `LinearMap.mul' R S ∘ₗ TensorProduct.mapIncl M N` since it is not defeq to
-- `Subalgebra.mulMap` which is `(Algebra.TensorProduct.productMap A.val B.val).toLinearMap`

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`. -/
def mulMap : M ⊗[R] N →ₗ[R] S :=
  TensorProduct.lift <| ((LinearMap.domRestrict' N).comp <| .mul R S).domRestrict M

@[simp]
theorem mulMap_tmul (m : M) (n : N) : mulMap M N (m ⊗ₜ[R] n) = m.1 * n.1 := rfl

theorem mulMap_op :
    mulMap (equivOpposite.symm (MulOpposite.op M)) (equivOpposite.symm (MulOpposite.op N)) =
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ mulMap N M ∘ₗ
    (TensorProduct.congr
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm M)
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm N) ≪≫ₗ
    TensorProduct.comm R M N).toLinearMap :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comm_of_commute (hc : ∀ (m : M) (n : N), Commute m.1 n.1) :
    mulMap N M = mulMap M N ∘ₗ TensorProduct.comm R N M := by
  refine TensorProduct.ext' fun n m ↦ ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

theorem mulMap_comp_rTensor (M' : Submodule R S) (hM : M' ≤ M) :
    mulMap M N ∘ₗ (inclusion hM).rTensor N = mulMap M' N :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comp_lTensor (N' : Submodule R S) (hN : N' ≤ N) :
    mulMap M N ∘ₗ (inclusion hN).lTensor M = mulMap M N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_comp_map_inclusion (M' N' : Submodule R S) (hM : M' ≤ M) (hN : N' ≤ N) :
    mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M' N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_eq_mul'_comp_mapIncl : mulMap M N = .mul' R S ∘ₗ TensorProduct.mapIncl M N :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem mulMap_range : LinearMap.range (mulMap M N) = M * N := by
  refine le_antisymm ?_ (mul_le.2 fun m hm n hn ↦ ⟨⟨m, hm⟩ ⊗ₜ[R] ⟨n, hn⟩, rfl⟩)
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero]; exact zero_mem _
  | tmul a b => exact mul_mem_mul a.2 b.2
  | add a b ha hb => rw [_root_.map_add]; exact add_mem ha hb

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural map
`M ⊗[R] N →ₗ[R] M * N` induced by multiplication in `S`,
which is surjective (`Submodule.mulMap'_surjective`). -/
def mulMap' : M ⊗[R] N →ₗ[R] ↥(M * N) :=
  (LinearEquiv.ofEq _ _ (mulMap_range M N)).toLinearMap ∘ₗ (mulMap M N).rangeRestrict

@[simp]
theorem val_mulMap'_tmul (m : M) (n : N) : (mulMap' M N (m ⊗ₜ[R] n) : S) = m.1 * n.1 := rfl

theorem mulMap'_surjective : Function.Surjective (mulMap' M N) := by
  simp_rw [mulMap', LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    LinearMap.surjective_rangeRestrict]

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural map
`i(R) ⊗[R] N →ₗ[R] N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This is promoted to an isomorphism as `Submodule.lTensorOne`. Use that instead. -/
def lTensorOne' : (1 : Submodule R S) ⊗[R] N →ₗ[R] N :=
  (LinearEquiv.ofEq _ _ (by rw [mulMap_range, one_mul])).toLinearMap ∘ₗ (mulMap _ N).rangeRestrict

theorem lTensorOne'_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (n : N) : N.lTensorOne' (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  Subtype.val_injective <| by simp [lTensorOne', Algebra.smul_def]

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`. -/
def lTensorOne : (1 : Submodule R S) ⊗[R] N ≃ₗ[R] N := by
  refine LinearEquiv.ofLinear N.lTensorOne' (TensorProduct.mk R (1 : Submodule R S) N
    ⟨1, one_le.1 (le_refl _)⟩) (by ext; simp [lTensorOne']) (TensorProduct.ext' fun r n ↦ ?_)
  change ⟨1, _⟩ ⊗ₜ[R] lTensorOne' N _ = r ⊗ₜ[R] n
  obtain ⟨x, y, h : algebraMap R S y = x⟩ := r
  simp_rw [← h, lTensorOne'_apply, ← TensorProduct.smul_tmul,
    SetLike.mk_smul_mk, Algebra.smul_def, mul_one]

theorem lTensorOne_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (n : N) : N.lTensorOne (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  N.lTensorOne'_apply y n

theorem lTensorOne_symm_apply (n : N) :
    N.lTensorOne.symm n = ⟨1, one_le.1 (le_refl _)⟩ ⊗ₜ[R] n := rfl

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural map
`M ⊗[R] i(R) →ₗ[R] M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This is promoted to an isomorphism as `Submodule.rTensorOne`. Use that instead. -/
def rTensorOne' : M ⊗[R] (1 : Submodule R S) →ₗ[R] M :=
  (LinearEquiv.ofEq _ _ (by rw [mulMap_range, mul_one])).toLinearMap ∘ₗ (mulMap M _).rangeRestrict

theorem rTensorOne'_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (m : M) : M.rTensorOne' (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  Subtype.val_injective <| by simp [rTensorOne', Algebra.smul_def, Algebra.commutes y m.1]

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`. -/
def rTensorOne : M ⊗[R] (1 : Submodule R S) ≃ₗ[R] M := by
  refine LinearEquiv.ofLinear M.rTensorOne' ((TensorProduct.comm R _ _).toLinearMap ∘ₗ
    TensorProduct.mk R (1 : Submodule R S) M ⟨1, one_le.1 (le_refl _)⟩)
      (by ext; simp [rTensorOne']) (TensorProduct.ext' fun n r ↦ ?_)
  change rTensorOne' M _ ⊗ₜ[R] ⟨1, _⟩ = n ⊗ₜ[R] r
  obtain ⟨x, y, h : algebraMap R S y = x⟩ := r
  simp_rw [← h, rTensorOne'_apply, TensorProduct.smul_tmul,
    SetLike.mk_smul_mk, Algebra.smul_def, mul_one]

theorem rTensorOne_apply
    (y : R) {hy : algebraMap R S y ∈ (1 : Submodule R S)}
    (m : M) : M.rTensorOne (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  M.rTensorOne'_apply y m

theorem rTensorOne_symm_apply (m : M) :
    M.rTensorOne.symm m = m ⊗ₜ[R] ⟨1, one_le.1 (le_refl _)⟩ := rfl

variable {M} in
/-- If `m : ι → M` is a family of elements, then there is an `R`-linear map from `ι →₀ N` to
`S` which maps `{ n_i }` to the sum of `m_i * n_i`. -/
def mulLeftMap {ι : Type*} (m : ι → M) : (ι →₀ N) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m) ∘ₗ
    (TensorProduct.finsuppScalarLeft R N ι).symm.toLinearMap

variable {M N} in
@[simp]
theorem mulLeftMap_apply_single {ι : Type*} (m : ι → M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap, TensorProduct.finsuppScalarLeft_symm_apply_single]

variable {M} in
theorem mulLeftMap_def' {ι : Type*} (m : ι → M) : mulLeftMap N m =
    Finsupp.lsum ℕ fun (i : ι) ↦ (LinearMap.mulLeft R (m i).1).comp N.subtype := by
  ext; simp

variable {M N} in
theorem mulLeftMap_apply {ι : Type*} (m : ι → M) (n : ι →₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) ↦ (m i).1 * n.1 :=
  congr($(mulLeftMap_def' N m) n)

variable {N} in
/-- If `n : ι → N` is a family of elements, then there is an `R`-linear map from `ι →₀ M` to
`S` which maps `{ m_i }` to the sum of `m_i * n_i`. -/
def mulRightMap {ι : Type*} (n : ι → N) : (ι →₀ M) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n) ∘ₗ
    (TensorProduct.finsuppScalarRight R M ι).symm.toLinearMap

variable {M N} in
@[simp]
theorem mulRightMap_apply_single {ι : Type*} (n : ι → N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap, TensorProduct.finsuppScalarRight_symm_apply_single]

variable {N} in
theorem mulRightMap_def' {ι : Type*} (n : ι → N) : mulRightMap M n =
    Finsupp.lsum ℕ fun (i : ι) ↦ LinearMap.smulRight M.subtype (n i).1 := by
  ext; simp

variable {M N} in
theorem mulRightMap_apply {ι : Type*} (n : ι → N) (m : ι →₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) ↦ m.1 * (n i).1 :=
  congr($(mulRightMap_def' M n) m)

variable {M} in
theorem mulLeftMap_eq_mulRightMap_of_commute {ι : Type*} (m : ι → M)
    (hc : ∀ (i : ι) (n : N), Commute (m i).1 n.1) : mulLeftMap N m = mulRightMap N m := by
  ext i n; simp [(hc i n).eq]

end mulMap

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ ↦ mul_comm _ _

variable {M} in
theorem mulLeftMap_eq_mulRightMap {ι : Type*} (m : ι → M) : mulLeftMap N m = mulRightMap N m :=
  mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ ↦ mul_comm _ _

end CommSemiring

end Submodule
