/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!

# Linearly disjoint of submodules

This file contains basics about the linearly disjoint of submodules.

## Mathematical background

We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`).

- `M` and `N` are linearly disjoint (`Submodule.LinearDisjoint M N` or simply
  `M.LinearDisjoint N`), if the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  (`Submodule.mulMap M N`) induced by the multiplication in `S` is injective.

The following is the first equivalent characterization of linearly disjointness:

- `Submodule.LinearDisjoint.map_linearIndependent_left_of_flat`:
  if `M` and `N` are linearly disjoint, if `N` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, they are also `N`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }`
  to the sum of `m_i * n_i` (`Submodule.LinearDisjoint.mulLeftMap N m`) is injective.

- `Submodule.LinearDisjoint.of_map_linearIndependent_left`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, which is also `N`-linearly independent,
  then `M` and `N` are linearly disjoint.

Dually, we have:

- `Submodule.LinearDisjoint.map_linearIndependent_right_of_flat`:
  if `M` and `N` are linearly disjoint, if `M` is a flat `R`-module, then for any family of
  `R`-linearly independent elements `{ n_i }` of `N`, they are also `M`-linearly independent,
  in the sense that the `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }`
  to the sum of `m_i * n_i` (`Submodule.LinearDisjoint.mulRightMap M n`) is injective.

- `Submodule.LinearDisjoint.of_map_linearIndependent_right`:
  conversely, if `{ n_i }` is an `R`-basis of `N`, which is also `M`-linearly independent,
  then `M` and `N` are linearly disjoint.

The following is the second equivalent characterization of linearly disjointness:

- `Submodule.LinearDisjoint.map_linearIndependent_mul_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then for any family of
  `R`-linearly independent elements `{ m_i }` of `M`, and any family of
  `R`-linearly independent elements `{ n_j }` of `N`, the family `{ m_i * n_j }` in `S` is
  also `R`-linearly independent.

- `Submodule.LinearDisjoint.of_map_linearIndependent_mul`:
  conversely, if `{ m_i }` is an `R`-basis of `M`, if `{ n_i }` is an `R`-basis of `N`,
  such that the family `{ m_i * n_j }` in `S` is `R`-linearly independent,
  then `M` and `N` are linearly disjoint.

## Other main results

- `Submodule.LinearDisjoint.symm_of_commute`, `Submodule.linearDisjoint_symm_of_commute`:
  linearly disjoint is symmetric under some commutative conditions.

- `Submodule.linearDisjoint_op`:
  linearly disjoint is preserved by taking multiplicative opposite.

- `Submodule.LinearDisjoint.of_le_left_of_flat`, `Submodule.LinearDisjoint.of_le_right_of_flat`,
  `Submodule.LinearDisjoint.of_le_of_flat_left`, `Submodule.LinearDisjoint.of_le_of_flat_right`:
  linearly disjoint is preserved by taking submodules under some flatness conditions.

- `Submodule.LinearDisjoint.of_linearDisjoint_finite_left`,
  `Submodule.LinearDisjoint.of_linearDisjoint_finite_right`,
  `Submodule.LinearDisjoint.of_linearDisjoint_finite`:
  conversely, if any finitely generated submodules of `M` and `N` are linearly disjoint,
  then `M` and `N` themselves are linearly disjoint.

- `Submodule.LinearDisjoint.of_bot_left`, `Submodule.LinearDisjoint.of_bot_right`:
  the zero module is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_self_left`, `Submodule.LinearDisjoint.of_self_right`:
  the image of `R` in `S` is linearly disjoint with any other submodules.

- `Submodule.LinearDisjoint.of_left_le_self_of_flat`,
  `Submodule.LinearDisjoint.of_right_le_self_of_flat`:
  if a submodule is contained in the image of `R` in `S`, then it is linearly disjoint with
  any other submodules, under some flatness conditions.

- `Submodule.LinearDisjoint.not_linearIndependent_pair_of_commute_of_flat`,
  `Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat`:
  if `M` and `N` are linearly disjoint, if one of `M` and `N` is flat, then any two commutative
  elements contained in the intersection of `M` and `N` are not `R`-linearly independent (namely,
  their span is not `R ^ 2`). In particular, if any two elements in the intersection of `M` and `N`
  are commutative, then the rank of the intersection of `M` and `N` is at most one.

- `Submodule.LinearDisjoint.rank_le_one_of_commute_of_flat_of_self`:
  if `M` and itself are linearly disjoint, if `M` is flat, if any two elements in `M`
  are commutative, then the rank of `M` is at most one.

The results with name containing "of_commute" also have corresponding specified versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

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

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`. -/
def mulMap := TensorProduct.lift <| ((LinearMap.domRestrict' N).comp <| .mul R S).domRestrict M

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

theorem mulMap_comp_inclusion (M' N' : Submodule R S) (hM : M' ≤ M) (hN : N' ≤ N) :
    mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M' N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural map
`i(R) ⊗[R] N →ₗ[R] N` induced by multiplication in `S`, here `i : R → S` is the structure map. -/
def lTensorAlgebraMap' :
    (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) ⊗[R] N →ₗ[R] N := by
  refine (mulMap (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) N).codRestrict N ?_
  intro c
  induction c using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero]; exact N.zero_mem
  | tmul r n =>
    rw [mulMap_tmul]
    obtain ⟨_, y, rfl⟩ := r
    convert N.smul_mem y n.2 using 1
    simp [Algebra.smul_def]
  | add x y hx hy => rw [_root_.map_add]; exact N.add_mem hx hy

theorem lTensorAlgebraMap'_apply
    (y : R) {hy : algebraMap R S y ∈ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range}
    (n : N) : N.lTensorAlgebraMap' (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  Subtype.val_injective <| by simp [lTensorAlgebraMap', Algebra.smul_def]

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`. -/
def lTensorAlgebraMap :
    (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) ⊗[R] N ≃ₗ[R] N := by
  refine LinearEquiv.ofLinear N.lTensorAlgebraMap'
    (TensorProduct.mk R (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) N
      ⟨1, 1, map_one _⟩) ?_ ?_
  · ext; simp [lTensorAlgebraMap']
  · ext r n
    obtain ⟨_, y, rfl⟩ := r
    simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.id_coe, id_eq, lTensorAlgebraMap'_apply]
    rw [← TensorProduct.smul_tmul]
    congr 1
    exact Subtype.val_injective <| by simp [Algebra.smul_def]

theorem lTensorAlgebraMap_apply
    (y : R) {hy : algebraMap R S y ∈ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range}
    (n : N) : N.lTensorAlgebraMap (⟨algebraMap R S y, hy⟩ ⊗ₜ[R] n) = y • n :=
  N.lTensorAlgebraMap'_apply y n

theorem lTensorAlgebraMap_symm_apply (n : N) :
    N.lTensorAlgebraMap.symm n = ⟨1, 1, map_one _⟩ ⊗ₜ[R] n := rfl

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural map
`M ⊗[R] i(R) →ₗ[R] M` induced by multiplication in `S`, here `i : R → S` is the structure map. -/
def rTensorAlgebraMap' :
    M ⊗[R] (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) →ₗ[R] M := by
  refine (mulMap M (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range)).codRestrict M ?_
  intro c
  induction c using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero]; exact M.zero_mem
  | tmul m r =>
    rw [mulMap_tmul]
    obtain ⟨_, y, rfl⟩ := r
    convert M.smul_mem y m.2 using 1
    simp [Algebra.smul_def, show _ * _ = _ * _ from Algebra.commute_algebraMap_left y m.1]
  | add x y hx hy => rw [_root_.map_add]; exact M.add_mem hx hy

theorem rTensorAlgebraMap'_apply
    (y : R) {hy : algebraMap R S y ∈ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range}
    (m : M) : M.rTensorAlgebraMap' (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  Subtype.val_injective <| by simp [rTensorAlgebraMap', Algebra.smul_def,
    show _ * _ = _ * _ from Algebra.commute_algebraMap_left y m.1]

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural isomorphism between
`M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`. -/
def rTensorAlgebraMap :
    M ⊗[R] (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) ≃ₗ[R] M := by
  refine LinearEquiv.ofLinear M.rTensorAlgebraMap'
    ((TensorProduct.comm R _ _).toLinearMap ∘ₗ TensorProduct.mk R
      (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) M ⟨1, 1, map_one _⟩) ?_ ?_
  · ext; simp [rTensorAlgebraMap']
  · ext m r
    obtain ⟨_, y, rfl⟩ := r
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, AlgHom.toRingHom_eq_coe,
      IsScalarTower.coe_toAlgHom, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.mk_apply,
      TensorProduct.comm_tmul, LinearMap.id_coe, id_eq, rTensorAlgebraMap'_apply]
    rw [TensorProduct.smul_tmul]
    congr 1
    exact Subtype.val_injective <| by simp [Algebra.smul_def]

theorem rTensorAlgebraMap_apply
    (y : R) {hy : algebraMap R S y ∈ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range}
    (m : M) : M.rTensorAlgebraMap (m ⊗ₜ[R] ⟨algebraMap R S y, hy⟩) = y • m :=
  M.rTensorAlgebraMap'_apply y m

theorem rTensorAlgebraMap_symm_apply (m : M) :
    M.rTensorAlgebraMap.symm m = m ⊗ₜ[R] ⟨1, 1, map_one _⟩ := rfl

namespace LinearDisjoint

variable {M} in
/-- If `m : ι → M` is a family of elements, then there is an `R`-linear map from `ι →₀ N` to
`S` which maps `{ n_i }` to the sum of `m_i * n_i`. -/
def mulLeftMap {ι : Type*} (m : ι → M) : (ι →₀ N) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m) ∘ₗ
    TensorProduct.finsuppScalarLeft.symm.toLinearMap

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
    TensorProduct.finsuppScalarRight.symm.toLinearMap

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

end LinearDisjoint

end mulMap

/-- Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective. -/
protected def LinearDisjoint : Prop := Function.Injective (mulMap M N)

variable {M N}

theorem LinearDisjoint.injective (H : M.LinearDisjoint N) : Function.Injective (mulMap M N) := H

/-- Linearly disjoint is preserved by taking multiplicative opposite. -/
theorem linearDisjoint_op :
    M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.op N)).LinearDisjoint
      (equivOpposite.symm (MulOpposite.op M)) := by
  simp only [Submodule.LinearDisjoint, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [Submodule.LinearDisjoint, mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

-- TODO: remove once #11731 is merged
lemma _root_.TensorProduct.coe_congr_right_refl {R : Type*} [CommSemiring R] {M N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] (f : M ≃ₗ[R] P) :
    (TensorProduct.congr f (LinearEquiv.refl R N)).toLinearMap = LinearMap.rTensor N f :=
  rfl

-- TODO: remove once #11731 is merged
lemma _root_.TensorProduct.coe_congr_left_refl {R : Type*} [CommSemiring R] {M N Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R Q] (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr (LinearEquiv.refl R M) g).toLinearMap = LinearMap.lTensor M g :=
  rfl

namespace LinearDisjoint

variable (M N)

theorem of_map_linearIndependent_left' {ι : Type*} (m : Basis ι R M)
    (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N := by
  simp_rw [mulLeftMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_right_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

theorem of_map_linearIndependent_right' {ι : Type*} (n : Basis ι R N)
    (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N := by
  simp_rw [mulRightMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_left_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

-- TODO: remove once #11598 is merged
theorem _root_.finsuppTensorFinsupp'_symm_single (R ι κ : Type*) [CommSemiring R] (i : ι × κ)
    (r₁ r₂ : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
      Finsupp.single i.1 r₁ ⊗ₜ Finsupp.single i.2 r₂ :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp'_single_tmul_single ..).symm

theorem of_map_linearIndependent_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : Function.Injective (Finsupp.total (κ × ι) S R fun i ↦ m i.1 * n i.2)) :
    M.LinearDisjoint N := by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.total (κ × ι) S R fun i ↦ m i.1 * n i.2 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      LinearEquiv.trans_apply, Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

theorem of_bot_left : (⊥ : Submodule R S).LinearDisjoint N := Function.injective_of_subsingleton _

theorem of_bot_right : M.LinearDisjoint (⊥ : Submodule R S) := Function.injective_of_subsingleton _

theorem of_self_left :
    (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range).LinearDisjoint N := by
  have : N.subtype ∘ₗ N.lTensorAlgebraMap.toLinearMap =
      mulMap (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) N := by
    change N.subtype ∘ₗ N.lTensorAlgebraMap' = _
    simp [lTensorAlgebraMap']
  have h : Function.Injective (N.subtype ∘ₗ N.lTensorAlgebraMap.toLinearMap) :=
    N.injective_subtype.comp N.lTensorAlgebraMap.injective
  rwa [this] at h

theorem of_self_right :
    M.LinearDisjoint (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) := by
  have : M.subtype ∘ₗ M.rTensorAlgebraMap.toLinearMap =
      mulMap M (Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) := by
    change M.subtype ∘ₗ M.rTensorAlgebraMap' = _
    simp [rTensorAlgebraMap']
  have h : Function.Injective (M.subtype ∘ₗ M.rTensorAlgebraMap.toLinearMap) :=
    M.injective_subtype.comp M.rTensorAlgebraMap.injective
  rwa [this] at h

-- TODO: move to suitable file and give it a better name
private theorem test1 (R : Type*) [CommSemiring R] (M N : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (x : M ⊗[R] N) :
    ∃ S : Multiset (M × N), x = (S.map fun i ↦ i.1 ⊗ₜ[R] i.2).sum := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

-- TODO: move to suitable file and give it a better name
private theorem test2L {ι : Type*} [Fintype ι] (x : ι → M ⊗[R] N) :
    ∃ (M' : Submodule R S) (x' : ι → M' ⊗[R] N) (hM : M' ≤ M), Module.Finite R M' ∧
      ∀ (i : ι), (inclusion hM).rTensor N (x' i) = x i := by
  choose Sx hSx using fun i ↦ test1 R M N (x i)
  let T := ((Finset.sum Finset.univ Sx).map fun i ↦ i.1.1).toFinset
  let M' := span R (T : Set S)
  have hM : M' ≤ M := span_le.2 fun x hx ↦ by
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_map, Prod.exists,
      exists_and_right, Subtype.exists, exists_eq_right, T] at hx
    obtain ⟨hx, _⟩ := hx
    exact hx
  let f (i : M × N) : M' ⊗[R] N :=
    if h : i.1.1 ∈ T then ⟨i.1.1, subset_span h⟩ ⊗ₜ[R] i.2 else 0
  let x' (i : ι) := ((Sx i).map f).sum
  refine ⟨M', x', hM, inferInstance, fun j ↦ ?_⟩
  simp_rw [x', hSx, map_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun i hi ↦ ?_
  replace hi : i.1.1 ∈ T := by
    simp only [Multiset.mem_toFinset, Multiset.mem_map, SetLike.coe_eq_coe, Prod.exists,
      exists_and_right, Subtype.exists, exists_eq_right, T]
    exact ⟨i.2.1, i.2.2, Multiset.mem_of_le (Finset.single_le_sum (by simp) (by simp)) hi⟩
  simp_rw [Function.comp_apply, f, dif_pos hi]; rfl

-- TODO: move to suitable file and give it a better name
private theorem test2Lpair (x y : M ⊗[R] N) :
    ∃ (M' : Submodule R S) (x' y' : M' ⊗[R] N) (hM : M' ≤ M), Module.Finite R M' ∧
      (inclusion hM).rTensor N x' = x ∧ (inclusion hM).rTensor N y' = y := by
  obtain ⟨M', x', hM, hfin, hx⟩ := test2L M N ![x, y]
  exact ⟨M', x' 0, x' 1, hM, hfin, hx 0, hx 1⟩

-- TODO: move to suitable file and give it a better name
private theorem test2R {ι : Type*} [Fintype ι] (x : ι → M ⊗[R] N) :
    ∃ (N' : Submodule R S) (x' : ι → M ⊗[R] N') (hN : N' ≤ N), Module.Finite R N' ∧
      ∀ (i : ι), (inclusion hN).lTensor M (x' i) = x i := by
  obtain ⟨N', x', hN, hfin, hx⟩ := test2L N M fun i ↦ TensorProduct.comm R M N (x i)
  have key : (inclusion hN).lTensor M ∘ₗ TensorProduct.comm R N' M =
      (TensorProduct.comm R M N).symm ∘ₗ (inclusion hN).rTensor M :=
    TensorProduct.ext' fun _ _ ↦ rfl
  refine ⟨N', fun i ↦ TensorProduct.comm R N' M (x' i), hN, hfin, fun i ↦ ?_⟩
  replace hx := congr((TensorProduct.comm R M N).symm $(hx i))
  rw [LinearEquiv.symm_apply_apply] at hx
  simpa only [← hx] using congr($key (x' i))

-- TODO: move to suitable file and give it a better name
private theorem test2Rpair (x y : M ⊗[R] N) :
    ∃ (N' : Submodule R S) (x' y' : M ⊗[R] N') (hN : N' ≤ N), Module.Finite R N' ∧
      (inclusion hN).lTensor M x' = x ∧ (inclusion hN).lTensor M y' = y := by
  obtain ⟨M', x', hM, hfin, hx⟩ := test2R M N ![x, y]
  exact ⟨M', x' 0, x' 1, hM, hfin, hx 0, hx 1⟩

theorem of_linearDisjoint_finite_left
    (H : ∀ M' : Submodule R S, M' ≤ M → [Module.Finite R M'] → M'.LinearDisjoint N) :
    M.LinearDisjoint N := fun x y hxy ↦ by
  obtain ⟨M', x', y', hM, _, hx', hy'⟩ := test2Lpair M N x y
  suffices x' = y' by rw [← hx', ← hy', this]
  exact H M' hM (by simpa [← mulMap_comp_rTensor _ _ _ hM, hx', hy'])

theorem of_linearDisjoint_finite_right
    (H : ∀ N' : Submodule R S, N' ≤ N → [Module.Finite R N'] → M.LinearDisjoint N') :
    M.LinearDisjoint N := fun x y hxy ↦ by
  obtain ⟨N', x', y', hN, _, hx', hy'⟩ := test2Rpair M N x y
  suffices x' = y' by rw [← hx', ← hy', this]
  exact H N' hN (by simpa [← mulMap_comp_lTensor _ _ _ hN, hx', hy'])

theorem of_linearDisjoint_finite
    (H : ∀ (M' N' : Submodule R S), M' ≤ M → N' ≤ N →
      [Module.Finite R M'] → [Module.Finite R N'] → M'.LinearDisjoint N') :
    M.LinearDisjoint N :=
  of_linearDisjoint_finite_left _ _ fun _ hM _ ↦
    of_linearDisjoint_finite_right _ _ fun _ hN _ ↦ H _ _ hM hN

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ ↦ mul_comm _ _

variable {M N}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (M N : Submodule R S)

variable {M N} in
theorem map_linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι → M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m)
  refine (TensorProduct.finsuppScalarLeft.symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm
  exact H.injective.comp (Module.Flat.preserves_injective_linearMap (M := N) _ hm)

theorem of_map_linearIndependent_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ N) := Finsupp.instAddCommGroup
  exact of_map_linearIndependent_left' M N m (LinearMap.ker_eq_bot.1 H)

-- TODO: move to suitable file ?
theorem _root_.Module.Flat.preserves_injective_linearMap'
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module.Flat R N] (L : M →ₗ[R] M') (hL : Function.Injective L) :
    Function.Injective (LinearMap.lTensor N L) := by
  -- rw [Module.Flat.lTensor_inj_iff_rTensor_inj]
  simp_rw [← LinearMap.comm_comp_rTensor_comp_comm_eq, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact Module.Flat.preserves_injective_linearMap L hL

variable {M N} in
theorem map_linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι → N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n)
  refine (TensorProduct.finsuppScalarRight.symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hn
  exact H.injective.comp (Module.Flat.preserves_injective_linearMap' (N := M) _ hn)

theorem of_map_linearIndependent_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ M) := Finsupp.instAddCommGroup
  exact of_map_linearIndependent_right' M N n (LinearMap.ker_eq_bot.1 H)

variable {M N} in
theorem map_linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι →₀ R) (Finsupp.total κ M R m)
  let i2 := LinearMap.lTensor M (Finsupp.total ι N R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.preserves_injective_linearMap' _ hn
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1, i2]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ →₀ R) (Finsupp.total ι N R n)
  let i2 := LinearMap.rTensor N (Finsupp.total κ M R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.preserves_injective_linearMap' _ hn
  have h2 : Function.Injective i2 := Module.Flat.preserves_injective_linearMap _ hm
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1, i2]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul_of_flat (H : M.LinearDisjoint N)
    (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.map_linearIndependent_mul_of_flat_left hm hn
  · exact H.map_linearIndependent_mul_of_flat_right hm hn

theorem of_map_linearIndependent_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at H
  exact of_map_linearIndependent_mul' M N m n H

variable {M N} in
theorem of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S}
    (h : M' ≤ M) [Module.Flat R N] :
    M'.LinearDisjoint N := by
  let i := mulMap M N ∘ₗ (Submodule.inclusion h).rTensor N
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.preserves_injective_linearMap _ <| Submodule.inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  rwa [this] at hi

variable {M N} in
theorem of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S}
    (h : N' ≤ N) [Module.Flat R M] :
    M.LinearDisjoint N' := by
  let i := mulMap M N ∘ₗ (Submodule.inclusion h).lTensor M
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.preserves_injective_linearMap' _ <| Submodule.inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  rwa [this] at hi

variable {M N} in
theorem of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R N] [Module.Flat R M'] :
    M'.LinearDisjoint N' := (H.of_le_left_of_flat hm).of_le_right_of_flat hn

variable {M N} in
theorem of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R M] [Module.Flat R N'] :
    M'.LinearDisjoint N' := (H.of_le_right_of_flat hn).of_le_left_of_flat hm

theorem of_left_le_self_of_flat
    (h : M ≤ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) [Module.Flat R N] :
    M.LinearDisjoint N := (of_self_left N).of_le_left_of_flat h

theorem of_right_le_self_of_flat
    (h : N ≤ Subalgebra.toSubmodule (IsScalarTower.toAlgHom R R S).range) [Module.Flat R M] :
    M.LinearDisjoint N := (of_self_right M).of_le_right_of_flat h

section not_linearIndependent_pair

variable {M N}

variable [Nontrivial R] (H : M.LinearDisjoint N)

theorem not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let n : Fin 2 → N := (Submodule.inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _
    (LinearMap.ker_eq_bot_of_injective (Submodule.inclusion_injective _))
  -- need this instance otherwise it only has semigroup structure
  letI : AddCommGroup (Fin 2 →₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 →₀ M := .single 0 ⟨b.1, b.2.1⟩ - .single 1 ⟨a.1, a.2.1⟩
  have hm : mulRightMap M n m = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.map_linearIndependent_right_of_flat hn, mem_bot] at hm
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero,
    false_or, m] at hm
  exact h.ne_zero 0 hm.2

theorem not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let m : Fin 2 → M := (Submodule.inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _
    (LinearMap.ker_eq_bot_of_injective (Submodule.inclusion_injective _))
  -- need this instance otherwise it only has semigroup structure
  letI : AddCommGroup (Fin 2 →₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 →₀ N := .single 0 ⟨b.1, b.2.2⟩ - .single 1 ⟨a.1, a.2.2⟩
  have hn : mulLeftMap N m n = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.map_linearIndependent_left_of_flat hm, mem_bot] at hn
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero,
    false_or, n] at hn
  exact h.ne_zero 0 hn.2

theorem not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc

theorem not_linearIndependent_pair_of_commute_of_flat' (hf : Module.Flat R M ∨ Module.Flat R N)
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] := by
  have h := H.not_linearIndependent_pair_of_commute_of_flat hf ⟨a, ha⟩ ⟨b, hb⟩ hc
  contrapose! h
  refine .of_comp (M ⊓ N).subtype ?_
  convert h
  exact (FinVec.map_eq _ _).symm

theorem not_linearIndependent_pair_of_commute_of_flat_left' [Module.Flat R M]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' (Or.inl ‹_›) ha hb hc

theorem not_linearIndependent_pair_of_commute_of_flat_right' [Module.Flat R N]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) (hc : Commute a b) :
    ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' (Or.inr ‹_›) ha hb hc

theorem rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 := by
  refine rank_le fun s h ↦ ?_
  by_contra hs
  rw [not_le, ← Fintype.card_coe, Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.comp ![a, b] fun i j hij ↦ by
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hab] at hij
    · simp [hab.symm] at hij
    · rfl
  convert this
  ext i
  fin_cases i <;> simp

theorem rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc

theorem rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc

theorem rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M]
    (hc : ∀ (m n : M), Commute m.1 n.1) : Module.rank R M ≤ 1 := by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc

end not_linearIndependent_pair

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (M N : Submodule R S)

section not_linearIndependent_pair

variable {M N}

variable [Nontrivial R] (H : M.LinearDisjoint N)

theorem not_linearIndependent_pair_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat' (hf : Module.Flat R M ∨ Module.Flat R N)
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat' hf ha hb (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_left' [Module.Flat R M]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left' ha hb (mul_comm _ _)

theorem not_linearIndependent_pair_of_flat_right' [Module.Flat R N]
    {a b : S} (ha : a ∈ M ⊓ N) (hb : b ∈ M ⊓ N) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right' ha hb (mul_comm _ _)

theorem rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) :
    Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat hf fun _ _ ↦ mul_comm _ _

theorem rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_left fun _ _ ↦ mul_comm _ _

theorem rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_right fun _ _ ↦ mul_comm _ _

theorem rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] :
    Module.rank R M ≤ 1 :=
  H.rank_le_one_of_commute_of_flat_of_self fun _ _ ↦ mul_comm _ _

end not_linearIndependent_pair

end LinearDisjoint

end CommRing

end Submodule
