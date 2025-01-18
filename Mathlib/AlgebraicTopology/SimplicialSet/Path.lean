/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of
`n + 1` 0-simplices and `n` 1-simplices, together with identifications between
0-simplices and the sources and targets of the 1-simplices. We define this
construction first for 1-truncated simplicial sets in `SSet.Truncated.Path₁`.
A path in a simplicial set `X` is then defined as a 1-truncated path in the
1-truncation of `X`.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path
of length `n`.
-/

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated SimplicialObject.Truncated

variable (X : SSet.Truncated.{u} 1)

/-- A path of length `n` in a 1-truncated simplicial set `X` is a directed path
of `n` edges. -/
@[ext]
structure Path₁ (n : ℕ) where
  /-- A path includes the data of `n + 1` 0-simplices in `X`.-/
  vertex (i : Fin (n + 1)) : X _[0]₁
  /-- A path includes the data of `n` 1-simplices in `X`.-/
  arrow (i : Fin n) : X _[1]₁
  /-- The source of a 1-simplex in a path is identified with the source vertex. -/
  arrow_src (i : Fin n) : X.map (Hom.tr (δ 1)).op (arrow i) = vertex i.castSucc
  /-- The target of a 1-simplex in a path is identified with the target vertex. -/
  arrow_tgt (i : Fin n) : X.map (Hom.tr (δ 0)).op (arrow i) = vertex i.succ

namespace Path₁

variable {X} {n : ℕ}

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path₁ X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last n), ← g.arrow_tgt (Fin.last n), h]
  · exact h j

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def interval (f : Path₁ X n) (j l : ℕ) (h : j + l ≤ n) : Path₁ X l where
  vertex i := f.vertex ⟨j + i, by omega⟩
  arrow i := f.arrow ⟨j + i, by omega⟩
  arrow_src i := f.arrow_src ⟨j + i, by omega⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩

variable {X Y : SSet.Truncated.{u} 1} {n : ℕ}

/-- Maps of 1-truncated simplicial sets induce maps of paths. -/
@[simps]
def map (f : Path₁ X n) (σ : X ⟶ Y) : Path₁ Y n where
  vertex i := σ.app _ (f.vertex i)
  arrow i := σ.app _ (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
    exact congr (σ.naturality (Hom.tr (δ 1)).op) rfl |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
    exact congr (σ.naturality (Hom.tr (δ 0)).op) rfl |>.symm

/-- `Path₁.map` respects subintervals of paths. -/
lemma map_interval (f : Path₁ X n) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := rfl

end Path₁

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- A path of length `m` in an `n + 1`-truncated simplicial set `X` is defined
by further 1-truncating `X`, then taking the 1-truncated path. -/
abbrev Path (m : ℕ) := trunc (n + 1) 1 |>.obj X |>.Path₁ m

namespace Path

variable {X} {m : ℕ}

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path X (m + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Path₁.ext' h

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
abbrev interval (f : Path X m) (j l : ℕ) (h : j + l ≤ m) : Path X l :=
  Path₁.interval f j l h

variable {X Y : SSet.Truncated.{u} (n + 1)} {m : ℕ}

/-- Maps of `n + 1`-truncated simplicial sets induce maps of paths. -/
@[simps!]
abbrev map (f : Path X m) (σ : X ⟶ Y) : Path Y m :=
  Path₁.map f <| trunc (n + 1) 1 |>.map σ

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (f : Path X m) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := rfl

end Path

/-- The spine of an `m`-simplex in `X` is the path of edges of length `m` formed
by traversing through its vertices in order. -/
@[simps]
def spine (m : ℕ) (h : m ≤ n + 1 := by leq) (Δ : X _[m]ₙ₊₁) : Path X m where
  vertex i := X.map (Hom.tr (const [0] [m] i)).op Δ
  arrow i := X.map (Hom.tr (mkOfSucc i)).op Δ
  arrow_src i := by
    dsimp only [Hom.tr, trunc, SimplicialObject.Truncated.trunc, incl,
      whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    change X.map (Hom.tr (_ ≫ _)).op _ = _
    rw [δ_one_mkOfSucc, Fin.coe_castSucc, Fin.coe_eq_castSucc]
  arrow_tgt i := by
    dsimp only [Hom.tr, trunc, SimplicialObject.Truncated.trunc, incl,
      whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    change X.map (Hom.tr (_ ≫ _)).op _ = _
    rw [δ_zero_mkOfSucc]

lemma spine_map_vertex (m : ℕ) (hm : m ≤ n + 1 := by leq) (Δ : X _[m]ₙ₊₁)
    (a : ℕ) (ha : a ≤ n + 1 := by leq) (φ : [a]ₙ₊₁ ⟶ [m]ₙ₊₁) (i : Fin (a + 1)) :
    (X.spine a ha (X.map φ.op Δ)).vertex i =
      (X.spine m hm Δ).vertex (φ.toOrderHom i) := by
  dsimp only [spine_vertex]
  rw [← FunctorToTypes.map_comp_apply]
  rfl

lemma spine_map_subinterval (m : ℕ) (h : m ≤ n + 1 := by leq)
    (j l : ℕ) (hjl : j + l ≤ m) (Δ : X _[m]ₙ₊₁) :
    X.spine l (by leq) (X.map (subinterval j l hjl).op Δ) =
      (X.spine m h Δ).interval j l hjl := by
  ext i
  · simp only [Path₁.interval, spine_vertex, ← FunctorToTypes.map_comp_apply]
    change X.map (Hom.tr ((const [0] [l] i) ≫ (subinterval j l hjl))).op _ = _
    rw [const_subinterval_eq j l hjl]
  · simp only [Path₁.interval, spine_arrow, ← FunctorToTypes.map_comp_apply]
    change X.map (Hom.tr (mkOfSucc i ≫ subinterval j l hjl)).op _ = _
    rw [mkOfSucc_subinterval_eq]

end Truncated

variable (X : SSet.{u})

/-- A path of length `n` in a simplicial set `X` is defined by 1-truncating `X`,
then taking the 1-truncated path. -/
abbrev Path (n : ℕ) := truncation 1 |>.obj X |>.Path₁ n

namespace Path
open Truncated (Path₁)

variable {X} {n : ℕ}

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Path₁.ext' h

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
abbrev interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n) : Path X l :=
  Path₁.interval f j l h

variable {X Y : SSet.{u}} {n : ℕ}

/-- Maps of `n + 1`-truncated simplicial sets induce maps of paths. -/
@[simps!]
abbrev map (f : Path X n) (σ : X ⟶ Y) : Path Y n :=
  Path₁.map f <| truncation 1 |>.map σ

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (f : Path X n) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := rfl

end Path

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed
by traversing in order through the vertices of `X _[n]ₙ₊₁`. -/
@[simps!]
abbrev spine (n : ℕ) : X _[n] → Path X n :=
  truncation (n + 1) |>.obj X |>.spine n

lemma spine_map_vertex {n : ℕ} (Δ : X _[n]) {m : ℕ} (φ : [m] ⟶ [n])
    (i : Fin (m + 1)) :
    (spine X m (X.map φ.op Δ)).vertex i =
      (spine X n Δ).vertex (φ.toOrderHom i) :=
  truncation ((m ⊔ n) + 1) |>.obj X
    |>.spine_map_vertex n (by leq) Δ m (by leq) φ i

/-- The spine of the unique non-degenerate `n`-simplex in `Δ[n]`. -/
def standardSimplex.spineId (n : ℕ) : Path Δ[n] n := spine Δ[n] n (id n)

/-- Any inner horn contains `standardSimplex.spineId`. -/
@[simps]
def horn.spineId {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path Λ[n + 2, i] (n + 2) where
  vertex j := ⟨standardSimplex.spineId _ |>.vertex j, horn.const n i j _ |>.2⟩
  arrow j := ⟨standardSimplex.spineId _ |>.arrow j, by
    let edge := primitiveEdge h₀ hₙ j
    suffices (standardSimplex.spineId _).arrow j = edge.1 from this ▸ edge.2
    simp only [edge, SimplicialObject.truncation, Truncated.inclusion, edge_coe,
      primitiveEdge, whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj,
      fullSubcategoryInclusion.obj, standardSimplex.spineId, Quiver.Hom.unop_op,
      Truncated.spine_arrow, Functor.comp_map, Functor.op_map,
      standardSimplex.edge, fullSubcategoryInclusion.map,
      standardSimplex.map_apply, EmbeddingLike.apply_eq_iff_eq]
    apply Hom.ext_one_left <;> rfl⟩
  arrow_src := by
    simp only [SimplicialObject.truncation, horn, whiskeringLeft_obj_obj,
      Functor.comp_obj, Functor.comp_map, Subtype.mk.injEq]
    exact standardSimplex.spineId (n + 2) |>.arrow_src
  arrow_tgt := by
    simp only [SimplicialObject.truncation, horn, whiskeringLeft_obj_obj,
      Functor.comp_obj, Functor.comp_map, Subtype.mk.injEq]
    exact standardSimplex.spineId (n + 2) |>.arrow_tgt

@[simp]
lemma horn.spineId_map_hornInclusion {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId i h₀ hₙ) (hornInclusion (n + 2) i) =
      standardSimplex.spineId (n + 2) := rfl

end SSet
