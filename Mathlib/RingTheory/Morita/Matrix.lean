/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.RingTheory.Morita.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Module.BigOperators
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.StacksAttribute
/-!
# Morita Equivalence between `R` and `Mₙ(R)`

## Main definitions
- `ModuleCat.toMatrixModCat`: The functor from `Mod-R` to `Mod-Mₙ(R)` induced by
  `LinearMap.mapMatrixModule` and `Matrix.Module.matrixModule`.
- `MatrixModCat.toModuleCat`: The functor from `Mod-Mₙ(R)` to `Mod-R` induced by sending `M` to
  the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix.
- `ModuleCat.matrixEquivalence`: An equivalence of categories composed by
  `ModuleCat.toMatrixModCat R ι`.
  and `MatrixModCat.toModuleCat R i`.
- `moritaEquivalentToMatrix`: `moritaEquivalentToMatrix` is a `MoritaEquivalence`.

## Main results
- `IsMoritaEquivalent.matrix`: `R` and `Mₙ(R)` are Morita equivalent.

-/

@[expose] public section

universe u v

variable (R : Type u) (ι : Type v) [Ring R] [Fintype ι] [DecidableEq ι]

open CategoryTheory Matrix.Module

/-- The functor from `Mod-R` to `Mod-Mₙ(R)` induced by `LinearMap.mapModule` and
  `Matrix.matrixModule`. -/
@[simps]
def ModuleCat.toMatrixModCat : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  obj M := ModuleCat.of (Matrix ι ι R) (ι → M)
  map f := ModuleCat.ofHom <| f.hom.mapMatrixModule ι
  map_id _ := ModuleCat.hom_ext <| LinearMap.mapMatrixModule_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.mapMatrixModule_comp f.hom g.hom)

variable {ι}

namespace MatrixModCat

open Matrix

variable {M : Type*} [AddCommGroup M] [Module (Matrix ι ι R) M] [Module R M]
  [IsScalarTower R (Matrix ι ι R) M]

variable (M) in
/-- The image of `Eᵢᵢ` (the elementary matrix) acting on all elements in `M`. -/
def toModuleCatObj (i : ι) : Submodule R M :=
  LinearMap.range (τ₁₂ := .id _) <|
    { __ := DistribSMul.toAddMonoidHom M (single i i 1 : Matrix ι ι R)
      map_smul' r x := by
        dsimp
        have : Commute (diagonal fun x : ι ↦ r) (single i i 1) := by
          ext; simp [Matrix.single]
        rw [← smul_assoc r, Matrix.smul_eq_diagonal_mul, this.eq,
          SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]
        nth_rw 1 [← one_smul (Matrix ι ι R) x]
        rw [smul_assoc] }

variable {R} in
@[simp]
lemma mem_toModuleCatObj (i : ι) {x : M} :
    x ∈ toModuleCatObj R M i ↔ ∃ y : M, single i i (1 : R) • y = x :=
  Iff.rfl

variable {R} in
/-- An `R`-linear map between `Eᵢᵢ • M` and `Eᵢᵢ • N` induced by an `Mₙ(R)`-linear map
  from `M` to `N`. -/
@[simps!]
def fromMatrixLinear {N : Type*} [AddCommGroup N] [Module (Matrix ι ι R) N] (i : ι)
    [Module R N] [IsScalarTower R (Matrix ι ι R) N] (f : M →ₗ[Matrix ι ι R] N) :
    toModuleCatObj R M i →ₗ[R] toModuleCatObj R N i :=
  f.restrictScalars R |>.restrict fun x hx => by
    obtain ⟨y, rfl⟩ := mem_toModuleCatObj i |>.1 hx
    exact ⟨f y, map_smul _ _ _ |>.symm⟩

end MatrixModCat

universe w

lemma MatrixModCat.isScalarTower_toModuleCat (M : ModuleCat (Matrix ι ι R)) :
    letI := Module.compHom M (Matrix.scalar (α := R) ι)
    IsScalarTower R (Matrix ι ι R) M :=
  letI := Module.compHom M (Matrix.scalar (α := R) ι)
  { smul_assoc r m x := show _ = Matrix.scalar ι r • (m • x) by
      rw [← SemigroupAction.mul_smul, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul] }

/-- The functor from the category of modules over `Mₙ(R)` to the category of modules over `R`
  induced by sending `M` to the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix. -/
@[simps]
def MatrixModCat.toModuleCat (i : ι) : ModuleCat (Matrix ι ι R) ⥤ ModuleCat R :=
  letI (M : ModuleCat (Matrix ι ι R)) := Module.compHom M (Matrix.scalar (α := R) ι)
  haveI := MatrixModCat.isScalarTower_toModuleCat
  { obj M := ModuleCat.of R (MatrixModCat.toModuleCatObj R M i)
    map f := ModuleCat.ofHom <| fromMatrixLinear i f.hom
    map_id _ := rfl
    map_comp _ _ := rfl }

open MatrixModCat Matrix

/-- The linear equiv induced by the equality `toModuleCat (toMatrixModCat M) = Eᵢᵢ • Mⁿ`. -/
def fromModuleCatToModuleCatLinearEquivtoModuleCatObj
    (M : Type*) [AddCommGroup M] [Module R M] (i : ι) :
    (ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R i).obj (.of R M) ≃ₗ[R]
    MatrixModCat.toModuleCatObj R (ι → M) i where
  __ := AddEquiv.refl _
  map_smul' _ _ := Subtype.ext <| scalar_smul _ _

/-- Auxiliary isomorphism showing that compose two functors gives `id` on objects. -/
@[simps]
def fromModuleCatToModuleCatLinearEquiv (M : Type*) [AddCommGroup M] [Module R M] (i : ι) :
    MatrixModCat.toModuleCatObj R (ι → M) i ≃ₗ[R] M where
  toFun x := ∑ i : ι, x.1 i
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' r := fun ⟨x, hx⟩ ↦ by simp [Finset.smul_sum]
  invFun x := ⟨Pi.single i x, Function.const ι x, by simp⟩
  left_inv := fun ⟨x, hx⟩ ↦ by
    obtain ⟨y, hy⟩ := mem_toModuleCatObj i |>.1 hx
    rw [single_smul] at hy
    simp [← hy]
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism showing that `toModuleCat` is the left inverse of `toMatrixModCat`. -/
def MatrixModCat.unitIso (i : ι) :
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R i ≅ 𝟭 (ModuleCat R) :=
  NatIso.ofComponents (fun X ↦ (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R X i ≪≫ₗ
    (fromModuleCatToModuleCatLinearEquiv R X i)).toModuleIso) <| by
    intros
    ext
    simp [fromModuleCatToModuleCatLinearEquivtoModuleCatObj]

/-- The linear equiv induced by the equality `toMatrixModCat (toModuleCat M) = Mⁿ` -/
def toModuleCatFromModuleCatLinearEquiv (M : ModuleCat (Matrix ι ι R)) (j : ι) :
    letI := Module.compHom M (Matrix.scalar (α := R) ι)
    haveI := MatrixModCat.isScalarTower_toModuleCat
    M ≃ₗ[Matrix ι ι R] (ι → MatrixModCat.toModuleCatObj R M j) where
  toFun m i := ⟨single j i (1 : R) • m, single j i (1 : R) • m, by
    simp [← SemigroupAction.mul_smul]⟩
  map_add' _ _ := by ext; simp
  map_smul' x m := funext fun i ↦ Subtype.ext <| by
    letI := Module.compHom M (Matrix.scalar (α := R) ι)
    haveI := MatrixModCat.isScalarTower_toModuleCat R M
    simp only [← SemigroupAction.mul_smul, RingHom.id_apply, Module.smul_apply,
      AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, ← smul_assoc, ← Finset.sum_smul]
    congr
    ext i1 j1
    simp only [mul_apply, smul_single, smul_eq_mul, mul_one, sum_apply]
    rw [Finset.sum_eq_single_of_mem (a := i) (by simp) (fun b _ hb ↦ by simp [single, Ne.symm hb])]
    simp only [single_apply, and_true, ite_mul, one_mul, zero_mul]
    split_ifs with h <;> simp [h]
  invFun m := ∑ i, single i j (1 : R) • m i
  left_inv m := by simp [← SemigroupAction.mul_smul, ← Finset.sum_smul, sum_single_one]
  right_inv v := by
    dsimp
    ext i
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single i (fun b _ hb ↦ by
      simp [← SemigroupAction.mul_smul, single_mul_single_of_ne _ _ _ _ hb.symm]) (by simp)]
    obtain ⟨y, hy⟩ := by simpa [-SetLike.coe_mem] using (v i).2
    simp [← SemigroupAction.mul_smul, ← hy]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism showing that `toMatrixModCat` is the right inverse of `toModuleCat`. -/
def MatrixModCat.counitIso (i : ι) :
    MatrixModCat.toModuleCat R i ⋙ ModuleCat.toMatrixModCat R ι ≅ 𝟭 (ModuleCat (Matrix ι ι R)) :=
  NatIso.ofComponents (fun X ↦ ((toModuleCatFromModuleCatLinearEquiv R X i).symm).toModuleIso) <| by
    intros
    ext
    simp [toModuleCatFromModuleCatLinearEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- `ModuleCat.toMatrixModCat R ι` and `MatrixModCat.toModuleCat R i` together form
  an equivalence of categories. -/
@[simps, stacks 074D "(1)"]
def ModuleCat.matrixEquivalence (i : ι) : ModuleCat R ≌ ModuleCat (Matrix ι ι R) where
  functor := ModuleCat.toMatrixModCat R ι
  inverse := MatrixModCat.toModuleCat R i
  unitIso := MatrixModCat.unitIso R i |>.symm
  counitIso := MatrixModCat.counitIso R i
  functor_unitIso_comp X := by
    ext1
    suffices (toModuleCatFromModuleCatLinearEquiv R ((ModuleCat.toMatrixModCat R ι).obj X)
      i).symm.toLinearMap ∘ₗ LinearMap.mapMatrixModule ι (ModuleCat.Hom.hom
      ((unitIso R i).inv.app X)) = LinearMap.id by simpa using this
    ext x
    simp [unitIso, toModuleCatFromModuleCatLinearEquiv, fromModuleCatToModuleCatLinearEquiv,
      fromModuleCatToModuleCatLinearEquivtoModuleCatObj, Finset.univ_sum_single]

set_option backward.isDefEq.respectTransparency false in
open ModuleCat.Algebra in
/-- Moreover `ModuleCat.matrixEquivalence` is a `MoritaEquivalence`. -/
@[simps]
def moritaEquivalenceMatrix (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] (i : ι) :
    MoritaEquivalence R₀ R (Matrix ι ι R) where
  eqv := ModuleCat.matrixEquivalence R i
  linear.map_smul {X Y} f r := by
    ext (v : ι → X)
    simp only [ModuleCat.matrixEquivalence_functor, ModuleCat.toMatrixModCat_obj_carrier,
      ModuleCat.toMatrixModCat_map, ModuleCat.hom_smul, ModuleCat.hom_ofHom, LinearMap.smul_apply]
    ext i
    simp only [LinearMap.mapMatrixModule_apply, LinearMap.compLeft_apply, Function.comp_apply,
      LinearMap.smul_apply]
    change _ = ((algebraMap R₀ (Matrix ι ι R) r) • ((ModuleCat.Hom.hom f).mapMatrixModule ι v)) i
    simp [Matrix.algebraMap_matrix_apply]

theorem IsMoritaEquivalent.matrix (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Nonempty ι] :
    IsMoritaEquivalent R₀ R (Matrix ι ι R) :=
  ⟨Nonempty.map (moritaEquivalenceMatrix R R₀) inferInstance⟩
