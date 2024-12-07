/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of `n + 1` 0-simplices
and `n` 1-simplices, together with identifications between 0-simplices and the sources and targets
of the 1-simplices.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path of length `n`.
-/

universe v u

namespace SSet

open CategoryTheory

open Simplicial SimplexCategory

variable (X : SSet.{u})

/-- A path in a simplicial set `X` of length `n` is a directed path of `n` edges.-/
@[ext]
structure Path (n : ℕ) where
  /-- A path includes the data of `n+1` 0-simplices in `X`.-/
  vertex (i : Fin (n + 1)) : X _[0]
  /-- A path includes the data of `n` 1-simplices in `X`.-/
  arrow (i : Fin n) : X _[1]
  /-- The sources of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_src (i : Fin n) : X.δ 1 (arrow i) = vertex i.castSucc
  /-- The targets of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_tgt (i : Fin n) : X.δ 0 (arrow i) = vertex i.succ


variable {X} in
/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely the subpath
spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def Path.interval {n : ℕ} (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) :
    Path X l where
  vertex i := f.vertex ⟨j + i, by omega⟩
  arrow i := f.arrow ⟨j + i, by omega⟩
  arrow_src i := f.arrow_src ⟨j + i, by omega⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed by
traversing through its vertices in order.-/
@[simps]
def spine (n : ℕ) (Δ : X _[n]) : X.Path n where
  vertex i := X.map (SimplexCategory.const [0] [n] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.δ_one_mkOfSucc]
    simp only [len_mk, Fin.coe_castSucc, Fin.coe_eq_castSucc]
  arrow_tgt i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.δ_zero_mkOfSucc]

lemma spine_map_subinterval {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n) (Δ : X _[n]) :
    X.spine l (X.map (subinterval j l (by omega)).op Δ) =
      (X.spine n Δ).interval j l (by omega) := by
  ext i
  · simp only [spine_vertex, Path.interval, ← FunctorToTypes.map_comp_apply, ← op_comp,
      const_subinterval_eq]
  · simp only [spine_arrow, Path.interval, ← FunctorToTypes.map_comp_apply, ← op_comp,
      mkOfSucc_subinterval_eq]

/-- Two paths of the same nonzero length are equal if all of their arrows are equal. -/
@[ext]
lemma Path.ext' {n : ℕ} {f g : Path X (n + 1)}
    (h : ∀ i : Fin (n + 1), f.arrow i = g.arrow i) :
    f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last n), ← g.arrow_tgt (Fin.last n), h]
  · exact h j

/-- Maps of simplicial sets induce maps of paths in a simplicial set.-/
@[simps]
def Path.map {X Y : SSet.{u}} {n : ℕ} (f : X.Path n) (σ : X ⟶ Y) : Y.Path n where
  vertex i := σ.app (Opposite.op [0]) (f.vertex i)
  arrow i := σ.app (Opposite.op [1]) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
    exact congr (σ.naturality (δ 1).op) rfl |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
    exact congr (σ.naturality (δ 0).op) rfl |>.symm

/-- `Path.map` respects subintervals of paths.-/
lemma map_interval {X Y : SSet.{u}} {n : ℕ} (f : X.Path n) (σ : X ⟶ Y)
    (j l : ℕ) (hjl : j + l ≤ n) :
    (f.map σ).interval j l hjl = (f.interval j l hjl).map σ := rfl

/-- The spine of the unique non-degenerate `n`-simplex in `Δ[n]`.-/
def standardSimplex.spineId (n : ℕ) : Path Δ[n] n :=
  spine Δ[n] n (standardSimplex.id n)

/-- Any inner horn contains the spine of the unique non-degenerate `n`-simplex
in `Δ[n]`.-/
@[simps]
def horn.spineId {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path Λ[n + 2, i] (n + 2) where
  vertex j := ⟨standardSimplex.spineId _ |>.vertex j, (horn.const n i j _).property⟩
  arrow j := ⟨standardSimplex.spineId _ |>.arrow j, by
    let edge := horn.primitiveEdge h₀ hₙ j
    have ha : (standardSimplex.spineId _).arrow j = edge.val := by
      dsimp only [edge, standardSimplex.spineId, standardSimplex.id, spine_arrow,
        mkOfSucc, horn.primitiveEdge, horn.edge, standardSimplex.edge,
        standardSimplex.map_apply]
      aesop
    rw [ha]
    exact edge.property⟩
  arrow_src := by
    simp only [horn, SimplicialObject.δ, Subtype.mk.injEq]
    exact standardSimplex.spineId _ |>.arrow_src
  arrow_tgt := by
    simp only [horn, SimplicialObject.δ, Subtype.mk.injEq]
    exact standardSimplex.spineId _ |>.arrow_tgt

@[simp]
lemma horn.spineId_map_hornInclusion {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId i h₀ hₙ) (hornInclusion (n + 2) i) =
      standardSimplex.spineId (n + 2) := rfl

end SSet
