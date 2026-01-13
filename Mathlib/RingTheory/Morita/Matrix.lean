/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Matrix.Module
/-!
# Morita Equivalece between `R` and `Mₙ(R)`

## Main definitions
- `ModuleCat.toMatrixModCat`: The functor from `Mod-R` to `Mod-Mₙ(R)` induced by
  `LinearMap.mapMatrixModule` and `Matrix.Module.matrixModule`.
- `MatrixModCat.toModuleCat`: The functor from `Mod-Mₙ(R)` to `Mod-R` induced by sending `M` to
  the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix.

## TODO (Edison)
- Prove `R` and `Mₙ(R)` are morita-equivalent.
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

namespace MatrixModCat

open Matrix

variable {M : Type*} [AddCommGroup M] [Module (Matrix ι ι R) M] [Module R M]
  [IsScalarTower R (Matrix ι ι R) M]

variable {ι} (M) in
/-- The image of `Eᵢᵢ` (the elementary matrix) acting on all elements in `M`. -/
def toModuleCatObj (i : ι) : Submodule R M :=
  LinearMap.range (τ₁₂ := .id _) <|
    { __ := DistribMulAction.toAddMonoidHom M (single i i 1 : Matrix ι ι R)
      map_smul' r x := by
        dsimp
        have : Commute (diagonal fun x : ι ↦ r) (single i i 1) := by
          ext; simp [Matrix.single]
        rw [← smul_assoc r, Matrix.smul_eq_diagonal_mul, this.eq,
          SemigroupAction.mul_smul, ← Matrix.smul_one_eq_diagonal]
        nth_rw 1 [← one_smul (Matrix ι ι R) x]
        rw [smul_assoc] }

variable {R ι} in
@[simp]
lemma mem_toModuleCatObj (i : ι) {x : M} :
    x ∈ toModuleCatObj R M i ↔ ∃ y : M, single i i (1 : R) • y = x :=
  Iff.rfl

variable {R ι} in
/-- An `R`-linear map between `Eᵢᵢ • M` and `Eᵢᵢ • N` induced by an `Mₙ(R)`-linear map
  from `M` to `N` -/
@[simps!]
def fromMatrixLinear {N : Type*} [AddCommGroup N] [Module (Matrix ι ι R) N] (i : ι)
    [Module R N] [IsScalarTower R (Matrix ι ι R) N] [Module R M] [IsScalarTower R (Matrix ι ι R) M]
    (f : M →ₗ[Matrix ι ι R] N) : toModuleCatObj R M i →ₗ[R] toModuleCatObj R N i :=
  f.restrictScalars R |>.restrict fun x hx => by
    obtain ⟨y, rfl⟩ := mem_toModuleCatObj i |>.1 hx
    exact ⟨f y, map_smul _ _ _ |>.symm⟩

end MatrixModCat

universe w

/-- The functor from the category of modules over `Mₙ(R)` to the category of modules over `R`
  induced by sending `M` to the image of `Eᵢᵢ • ·` where `Eᵢᵢ` is the elementary matrix -/
@[simps]
def MatrixModCat.toModuleCat [Inhabited ι] : ModuleCat (Matrix ι ι R) ⥤ ModuleCat R :=
  letI (M : ModuleCat (Matrix ι ι R)) := Module.compHom M (Matrix.scalar (α := R) ι)
  haveI (M : ModuleCat (Matrix ι ι R)) : IsScalarTower R (Matrix ι ι R) M :=
    { smul_assoc r m x := show _ = (Matrix.scalar ι r) • (m • x) by
        rw [← mul_smul, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul] }
  { obj M := ModuleCat.of R (MatrixModCat.toModuleCatObj R M default)
    map {M N} f := ModuleCat.ofHom <| fromMatrixLinear default f.hom
    map_id _ := rfl
    map_comp _ _ := rfl }

open MatrixModCat Matrix

variable [Inhabited ι]

/-- The linear equiv induced by the equality `toModuleCat (toMatrixModCat M) = Eᵢᵢ • Mⁿ` -/
def fromModuleCatToModuleCatLinearEquivtoModuleCatObj (M : Type*) [AddCommGroup M] [Module R M] :
    (ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R ι).obj (.of R M) ≃ₗ[R]
    MatrixModCat.toModuleCatObj R (ι := ι) (ι → M) default where
  __ := AddEquiv.refl _
  map_smul' _ _ := Subtype.ext <| scalar_smul _ _

/-- auxilary isomorphism showing that compose two functors gives `id` on objects. -/
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

/-- the natural isomorphism showing that `toModuleCat` is the left inverse of `toMatrixModCat` -/
def MatrixModCat.unitIso :
    ModuleCat.toMatrixModCat R ι ⋙ MatrixModCat.toModuleCat R ι ≅ 𝟭 (ModuleCat R) :=
  NatIso.ofComponents (fun X ↦ (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R ι X ≪≫ₗ
    (fromModuleCatToModuleCatLinearEquiv R ι X default)).toModuleIso) <| by
    intros
    ext
    simp [fromModuleCatToModuleCatLinearEquivtoModuleCatObj]
