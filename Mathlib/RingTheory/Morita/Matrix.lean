/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.Data.Matrix.Basis

/-!
# Morita Equivalece between `R` and `Mₙ(R)`

## Main definitions
- `ModuleCat.toMatrixModCat`: The functor from `Mod-R` to `Mod-Mₙ(R)` induced by
  `LinearMap.mapMatrixModule` and `Matrix.Module.matrixModule`.
- `MatrixModCat.toModuleCat`: The functor from `Mod-Mₙ(R)` to `Mod-R` induced by sending `M` to
  the image of `E₁₁ • ·` where `E₁₁` is the elementary matrix.

## TODO (Edison)
- Prove `R` and `Mₙ(R)` are morita-equivalent.
-/

@[expose] public section

universe u

variable (R ι : Type*) [Ring R] [Fintype ι] [DecidableEq ι]

open CategoryTheory Matrix.Module

/-- The functor from `Mod-R` to `Mod-Mₙ(R)` induced by `LinearMap.mapModule` and
  `Matrix.matrixModule`. -/
@[simps]
def ModuleCat.toMatrixModCat : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  obj M := ModuleCat.of (Matrix ι ι R) (ι → M)
  map f := ModuleCat.ofHom <| f.hom.mapMatrixModule ι
  map_id _ := ModuleCat.hom_ext <| LinearMap.mapMatrixModule_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.mapMatrixModule_comp f.hom g.hom)

namespace MatrixModCat.toModuleCat

open Matrix

variable [Inhabited ι] {M : Type*} [AddCommGroup M] [Module (Matrix ι ι R) M] [Module R M]
  [IsScalarTower R (Matrix ι ι R) M]

variable (M) in
def α : Submodule R M where
  __ := DistribMulAction.toAddMonoidHom M (single default default 1 : Matrix ι ι R)|>.range
  smul_mem' r {m} := by simpa using fun x h ↦ ⟨r • x, by
    rw [← h, ← smul_assoc r, Matrix.smul_eq_diagonal_mul, show (diagonal fun x : ι ↦ r) *
      single _ _ 1 = single default default 1 * diagonal (fun _ ↦ r) by ext; simp [Matrix.single],
      SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]
    nth_rw 1 [← one_smul (Matrix ι ι R) x]
    rw [smul_assoc]⟩

variable {R ι} in
@[simp]
lemma α_mem (x : M) : x ∈ α R ι M ↔ ∃ y : M, (single default default 1 : Matrix ι ι R) • y = x :=
  Iff.rfl

-- instance : SMul R (α R ι M) where
--     smul a x := ⟨(single default default a : Matrix ι ι R) • x.1, α_mem _|>.2
--       ⟨(single default default a : Matrix ι ι R) • x.1, by simp [← SemigroupAction.mul_smul]⟩⟩

-- @[simp]
-- lemma smul_α_coe
--     (x : R) (y : α R ι M) : ((x • y : α R ι M) : M) =
--     (single default default x : Matrix ι ι R) • y.1 := rfl

-- lemma one_smul' (x : α R ι M) : (1 : R) • x = x := by
--   obtain ⟨y, hy⟩ := α_mem x.1|>.1 x.2
--   ext; simp [← hy, ← SemigroupAction.mul_smul]

-- lemma mul_smul' (a a' : R) (x : α R ι M) : (a * a') • x = a • (a' • x) := by
--   obtain ⟨y, hy⟩ := α_mem x.1|>.1 x.2
--   ext; simp [← hy, ← SemigroupAction.mul_smul]

-- lemma smul_zero' (a : R) : a • (0 : α R ι M) = 0 := by ext; simp

-- lemma smul_add' (a : R) (x y : α R ι M) : a • (x + y) = a • x + a • y := by
--   obtain ⟨x', hx'⟩ := α_mem x.1|>.1 x.2
--   obtain ⟨y', hy'⟩ := α_mem y.1|>.1 y.2
--   ext; simp [← hx', ← hy', ← SemigroupAction.mul_smul, ← smul_add]

-- lemma add_smul' (a b : R) (x : α R ι M) : (a + b) • x = a • x + b • x := by
--   obtain ⟨y, hy⟩ := α_mem x.1|>.1 x.2
--   ext; simpa [← hy, ← SemigroupAction.mul_smul, ← add_smul] using congr_fun
--     (congr(@HSMul.hSMul _ _ _ _ $(single_add default default a b))) _

-- lemma zero_smul' (x : α R ι M) : (0 : R) • x = 0 := by
--   obtain ⟨y, hy⟩ := α_mem x.1|>.1 x.2
--   ext; simp [← hy, ← SemigroupAction.mul_smul]

-- instance module_α : Module R <| α R ι M where
--   one_smul := one_smul' _ _
--   mul_smul := mul_smul' _ _
--   smul_zero := smul_zero' _ _
--   smul_add := smul_add' _ _
--   add_smul := add_smul' _ _
--   zero_smul := zero_smul' _ _

variable {R ι} in
@[simps]
def _root_.LinearMap.fromMatrixLinear {N : Type*} [AddCommGroup N] [Module (Matrix ι ι R) N]
    [Module R N] [IsScalarTower R (Matrix ι ι R) N] [Module R M] [IsScalarTower R (Matrix ι ι R) M]
    (f : M →ₗ[Matrix ι ι R] N) : (α R ι M) →ₗ[R] (α R ι N) where
  toFun x := ⟨f x.1, by obtain ⟨y, hy⟩ := α_mem x.1|>.1 x.2; simp [← hy]⟩
  map_add' := by simp
  map_smul' := by simp --[Subtype.ext_iff]


end MatrixModCat.toModuleCat

variable [Inhabited ι]

/-- the functor from Module Cat of `Mₙ(R)` to Module Cat of `R` induced by sending `M` to
  the image of `E₁₁ • ·` where `E₁₁` is the elementary matrix -/
@[simps]
def MatrixModCat.toModuleCat : ModuleCat (Matrix ι ι R) ⥤ ModuleCat R where
  obj M :=
    letI := Module.compHom M ({
      toFun r := r • 1
      map_one' := by simp
      map_mul' := by simp [SemigroupAction.mul_smul]
      map_zero' := by simp
      map_add' := by simp [add_smul]
    } : R →+* Matrix ι ι R)
    letI : IsScalarTower R (Matrix ι ι R) M := {
      smul_assoc r m x := by
        change _ = (r • 1 : Matrix ι ι R) • m • x
        rw [Matrix.smul_eq_diagonal_mul, SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]}
    ModuleCat.of R (MatrixModCat.toModuleCat.α R ι M)
  map {M N} f :=
    letI := Module.compHom M ({
      toFun r := r • 1
      map_one' := by simp
      map_mul' := by simp [SemigroupAction.mul_smul]
      map_zero' := by simp
      map_add' := by simp [add_smul]
    } : R →+* Matrix ι ι R)
    letI : IsScalarTower R (Matrix ι ι R) M := {
      smul_assoc r m x := by
        change _ = (r • 1 : Matrix ι ι R) • m • x
        rw [Matrix.smul_eq_diagonal_mul, SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]}
    letI := Module.compHom N ({
      toFun r := r • 1
      map_one' := by simp
      map_mul' := by simp [SemigroupAction.mul_smul]
      map_zero' := by simp
      map_add' := by simp [add_smul]
    } : R →+* Matrix ι ι R)
    letI : IsScalarTower R (Matrix ι ι R) N := {
      smul_assoc r m x := by
        change _ = (r • 1 : Matrix ι ι R) • m • x
        rw [Matrix.smul_eq_diagonal_mul, SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]}
    ModuleCat.ofHom <| LinearMap.fromMatrixLinear f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

open MatrixModCat.toModuleCat Matrix

/-- auxilary isomorphism showing that compose two functors gives `id` on objects. -/
@[simps]
def fromModuleCat_toModuleCatLinearEquiv (M : Type*) [AddCommGroup M] [Module R M] :
    MatrixModCat.toModuleCat.α R ι (ι → M) ≃ₗ[R] M where
  toFun x := ∑ i : ι, x.1 i
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' r := fun ⟨x, hx⟩ ↦ by simp [Finset.smul_sum]
  invFun x := ⟨Function.update 0 default x, Function.const ι x, by
    ext i
    simp only [DistribMulAction.toAddMonoidHom_apply, smul_def, Function.const_apply,
      Function.update_apply, Pi.zero_apply]
    split_ifs with h
    · simp [h, single]
    · simp [Ne.symm h]⟩
  left_inv := fun ⟨x, hx⟩ ↦ by
    obtain ⟨y, hy⟩ := α_mem x|>.1 hx
    ext i
    simp only [Function.update_apply, Pi.zero_apply]
    split_ifs with h
    · simp only [← hy, single, smul_def, of_apply, ite_smul, one_smul, zero_smul, h,
      true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [Finset.sum_eq_single default (by
        simpa using fun b hb ↦ Finset.sum_eq_zero (ι := ι) (by grind)) (by simp)]
      simp
    · simp [← hy, single, Ne.symm h]
  right_inv x := by simp [Function.update_apply]

/-- the functor from `toModuleCat` compose `fromModuleCat` to `𝟙 _` induced by previous
  linear equiv. -/
@[simps]
def matrix.unitIsoHom :
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R ι ⟶
    𝟭 (ModuleCat R) where
  app X := ModuleCat.ofHom <| by
    convert (fromModuleCat_toModuleCatLinearEquiv R ι X).toLinearMap using 1
    simp only [ModuleCat.toMatrixModCat]
    congr!
    ext r v : 3
    change (r • (1 : Matrix ι ι R)) • v = fun i ↦ r • v i
    ext j
    simp [Matrix.one_apply]
  naturality {X Y} f := by
    -- ext;
    -- simp
    sorry

#exit
/-- the functor from `𝟙 _` to `toModuleCat` compose `fromModuleCat` induced by the inverse of
  previous linear equiv. -/
@[simps]
def matrix.unitIsoInv :
    𝟭 (ModuleCat R) ⟶
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R ι  where
  app X := ModuleCat.ofHom <| (fromModuleCat_toModuleCatLinearEquiv R ι X).symm.toLinearMap
  naturality {X Y} f := by
    ext x
    simp only [MatrixModCat.toModuleCat, Functor.comp_obj, ModuleCat.toMatrixModCat_obj_carrier,
      ModuleCat.toMatrixModCat_obj_isAddCommGroup, ModuleCat.toMatrixModCat_obj_isModule,
      Functor.id_obj, Functor.id_map, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Functor.comp_map, ModuleCat.toMatrixModCat_map]
    ext i
    simp only [fromModuleCat_toModuleCatLinearEquiv_symm_apply_coe, Function.update_apply,
      Pi.zero_apply, LinearMap.fromMatrixLinear_apply_coe, LinearMap.mapMatrixModule_apply,
      LinearMap.compLeft_apply, Function.comp_apply]
    split_ifs <;> simp

/-- the natural isomorphism showing that `toModuleCat` compose with `fromModuleCat` gives `id` -/
@[simps]
def matrix.unitIso :
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R ι ≅ 𝟭 (ModuleCat R) where
  hom := matrix.unitIsoHom R ι
  inv := matrix.unitIsoInv R ι
  hom_inv_id := by
    ext M : 2
    simp [← ModuleCat.ofHom_comp, MatrixModCat.toModuleCat]
  inv_hom_id := by
    ext M : 2
    simp [← ModuleCat.ofHom_comp]
