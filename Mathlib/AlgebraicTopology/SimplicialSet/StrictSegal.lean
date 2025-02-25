/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _⦋n⦌ → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal`.

-/

universe v u

open CategoryTheory

open Simplicial SimplicialObject SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal where
  /-- The inverse to `X.spine n`. -/
  spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌
  /-- `spineToSimplex` is a right inverse to `X.spine n`. -/
  spine_spineToSimplex {n : ℕ} (f : Path X n) : X.spine n (spineToSimplex f) = f
  /-- `spineToSimplex` is a left inverse to `X.spine n`. -/
  spineToSimplex_spine {n : ℕ} (Δ : X _⦋n⦌) : spineToSimplex (X.spine n Δ) = Δ

namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

/-- The fields of `StrictSegal` define an equivalence between `X _⦋n⦌` and `Path X n`. -/
def spineEquiv (n : ℕ) : X _⦋n⦌ ≃ Path X n where
  toFun := spine X n
  invFun := spineToSimplex
  left_inv := spineToSimplex_spine
  right_inv := spine_spineToSimplex

theorem spineInjective {n : ℕ} : Function.Injective (spineEquiv (X := X) n) := Equiv.injective _

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex]

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal (f : Path X n) : X _⦋1⦌ := diagonal X (spineToSimplex f)

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply spineInjective
  unfold spineEquiv
  dsimp
  rw [spine_spineToSimplex]
  convert spine_map_subinterval X j l hjl (spineToSimplex f)
  exact Eq.symm (spine_spineToSimplex f)

theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) :
    X.map (intervalEdge j l hjl).op (spineToSimplex f) =
      spineToDiagonal (Path.interval f j l hjl) := by
  unfold spineToDiagonal
  rw [← congrArg (diagonal X) (spineToSimplex_interval f j l hjl)]
  unfold diagonal
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, diag_subinterval_eq]

/-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.{u}} [StrictSegal X] [StrictSegal Y]
    {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    spineToSimplex (f.map σ) = σ.app _ (spineToSimplex f) := by
  apply spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, Path.map, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp only [types_comp_apply, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : i.castSucc < j) :
    (X.spine n (X.δ j (spineToSimplex f))).vertex i = f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i h]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i = f.arrow i.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i =
      spineToDiagonal (Path.interval f i 2 (by omega)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]

end StrictSegal

end SSet

namespace CategoryTheory.Nerve

open SSet

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor. -/
noncomputable instance strictSegal (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  spineToSimplex {n} F :=
    ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
      (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
        (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
  spine_spineToSimplex {n} F := by
    ext i
    · exact ComposableArrows.ext₀ rfl
    · refine ComposableArrows.ext₁ ?_ ?_ ?_
      · exact Functor.congr_obj (F.arrow_src i).symm 0
      · exact Functor.congr_obj (F.arrow_tgt i).symm 0
      · dsimp
        apply ComposableArrows.mkOfObjOfMapSucc_map_succ
  spineToSimplex_spine {n} F := by
    fapply ComposableArrows.ext
    · intro i
      rfl
    · intro i hi
      apply ComposableArrows.mkOfObjOfMapSucc_map_succ

end CategoryTheory.Nerve
