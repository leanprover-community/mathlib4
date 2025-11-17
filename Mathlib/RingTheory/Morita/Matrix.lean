/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Module

/-!
## Main definitions
- `ModuleCat.toMatrixModCat`: The functor from `Mod-R` to `Mod-Mₙ(R)` induced by
  `LinearMap.mapModule` and `Matrix.matrixModule`.

## TODO (Edison)
- Prove `R` and `Mₙ(R)` are morita-equivalent.
-/

universe u

variable (R ι : Type*) [Ring R] [Fintype ι] [DecidableEq ι]

open CategoryTheory Matrix.Module

/-- The functor from `Mod-R` to `Mod-Mₙ(R)` induced by `LinearMap.mapModule` and
  `Matrix.matrixModule`. -/
@[simps]
def ModuleCat.toMatrixModCat : ModuleCat R ⥤ ModuleCat (Matrix ι ι R) where
  obj M := ModuleCat.of (Matrix ι ι R) (ι → M)
  map f := ModuleCat.ofHom f.hom.mapMatrixModule
  map_id _ := ModuleCat.hom_ext LinearMap.id_mapMatrixModule
  map_comp f g := ModuleCat.hom_ext (LinearMap.comp_mapMatrixModule f.hom g.hom)
