/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of
`n + 1` 0-simplices and `n` 1-simplices, together with identifications between
0-simplices and the sources and targets of the 1-simplices. We define this
construction first for truncated simplicial sets in `SSet.Truncated.Path`. A
path in a simplicial set `X` is then defined as a 1-truncated path in the
1-truncation of `X`.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path
of length `n`.
-/

universe v u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

/-- A path of length `n` in a 1-truncated simplicial set `X` is a directed path
of `n` edges. -/
@[ext]
structure Path₁ (X : SSet.Truncated.{u} 1) (n : ℕ) where
  /-- A path includes the data of `n + 1` 0-simplices in `X`. -/
  vertex : Fin (n + 1) → X _⦋0⦌₁
  /-- A path includes the data of `n` 1-simplices in `X`. -/
  arrow : Fin n → X _⦋1⦌₁
  /-- The source of a 1-simplex in a path is identified with the source vertex. -/
  arrow_src (i : Fin n) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  /-- The target of a 1-simplex in a path is identified with the target vertex. -/
  arrow_tgt (i : Fin n) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

/-- A path of length `m` in an `n + 1`-truncated simplicial set `X` is given by
the data of a `Path₁` structure on the further 1-truncation of `X`. -/
def Path {n : ℕ} (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) :=
  trunc (n + 1) 1 |>.obj X |>.Path₁ m

namespace Path

variable {n : ℕ} {X : SSet.Truncated.{u} (n + 1)} {m : ℕ}

/-- A path includes the data of `n + 1` 0-simplices in `X`. -/
abbrev vertex (f : Path X m) (i : Fin (m + 1)) : X _⦋0⦌ₙ₊₁ :=
  Path₁.vertex f i

/-- A path includes the data of `n` 1-simplices in `X`. -/
abbrev arrow (f : Path X m) (i : Fin m) : X _⦋1⦌ₙ₊₁ :=
  Path₁.arrow f i

/-- The source of a 1-simplex in a path is identified with the source vertex. -/
lemma arrow_src (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  Path₁.arrow_src f i

/-- The target of a 1-simplex in a path is identified with the target vertex. -/
lemma arrow_tgt (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  Path₁.arrow_tgt f i

@[ext]
lemma ext {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Path₁.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path X (m + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m), ← g.arrow_tgt (Fin.last m), h]
  · exact h j

/-- For `j + l ≤ m`, a path of length `m` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def interval (f : Path X m) (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l where
  vertex i := f.vertex ⟨j + i, by omega⟩
  arrow i := f.arrow ⟨j + i, by omega⟩
  arrow_src i := f.arrow_src ⟨j + i, by omega⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩

variable {X Y : SSet.Truncated.{u} (n + 1)} {m : ℕ}

/-- Maps of `n + 1`-truncated simplicial sets induce maps of paths. -/
def map (f : Path X m) (σ : X ⟶ Y) : Path Y m where
  vertex i := σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i)
  arrow i := σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
    exact congr (σ.naturality (tr (δ 1)).op) rfl |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
    exact congr (σ.naturality (tr (δ 0)).op) rfl |>.symm

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
lemma map_vertex (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌ₙ₊₁) (f.vertex i) :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
lemma map_arrow (f : Path X m) (σ : X ⟶ Y) (i : Fin m) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌ₙ₊₁) (f.arrow i) :=
  rfl


lemma map_interval (f : Path X m) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- The spine of an `m`-simplex in `X` is the path of edges of length `m`
formed by traversing in order through its vertices. -/
def spine (m : ℕ) (h : m ≤ n + 1 := by omega) (Δ : X _⦋m⦌ₙ₊₁) : Path X m where
  vertex i := X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ
  arrow i := X.map (tr (mkOfSucc i)).op Δ
  arrow_src i := by
    dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
      Functor.whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ObjectProperty.ιOfLE_map,
      ← tr_comp, ObjectProperty.homMk_hom, δ_one_mkOfSucc]
  arrow_tgt i := by
    dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
      Functor.whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ObjectProperty.ιOfLE_map,
      ← tr_comp, ObjectProperty.homMk_hom, δ_zero_mkOfSucc]

/-- Further truncating `X` above `m` does not change the `m`-spine. -/
lemma trunc_spine (k m : ℕ) (h : m ≤ k + 1) (hₙ : k ≤ n) :
    ((trunc (n + 1) (k + 1)).obj X).spine m = X.spine m :=
  rfl

variable (m : ℕ) (hₘ : m ≤ n + 1)

/- We write this lemma manually to ensure it refers to `Path.vertex`. -/
@[simp]
lemma spine_vertex (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 1)) :
    (X.spine m hₘ Δ).vertex i =
      X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op Δ :=
  rfl

/- We write this lemma manually to ensure it refers to `Path.arrow`. -/
@[simp]
lemma spine_arrow (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m) :
    (X.spine m hₘ Δ).arrow i = X.map (tr (mkOfSucc i)).op Δ :=
  rfl

lemma spine_map_vertex (Δ : X _⦋m⦌ₙ₊₁) (a : ℕ) (hₐ : a ≤ n + 1)
    (φ : ⦋a⦌ₙ₊₁ ⟶ ⦋m⦌ₙ₊₁) (i : Fin (a + 1)) :
    (X.spine a hₐ (X.map φ.op Δ)).vertex i =
      (X.spine m hₘ Δ).vertex (φ.hom.toOrderHom i) := by
  dsimp only [spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp',
    SimplexCategory.const_comp]

lemma spine_map_subinterval (j l : ℕ) (h : j + l ≤ m) (Δ : X _⦋m⦌ₙ₊₁) :
    X.spine l (by cutsat) (X.map (tr (subinterval j l h)).op Δ) =
      (X.spine m hₘ Δ).interval j l h := by
  ext i
  · dsimp only [spine_vertex, Path.interval]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
      const_subinterval_eq]
  · dsimp only [spine_arrow, Path.interval]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
      mkOfSucc_subinterval_eq]

end Truncated

/-- A path of length `n` in a simplicial set `X` is defined as a 1-truncated
path in the 1-truncation of `X`. -/
abbrev Path (X : SSet.{u}) (n : ℕ) := truncation 1 |>.obj X |>.Path n

namespace Path

variable {X : SSet.{u}} {n : ℕ}

/-- A path includes the data of `n + 1` 0-simplices in `X`. -/
abbrev vertex (f : Path X n) (i : Fin (n + 1)) : X _⦋0⦌ :=
  Truncated.Path.vertex f i

/-- A path includes the data of `n` 1-simplices in `X`. -/
abbrev arrow (f : Path X n) (i : Fin n) : X _⦋1⦌ :=
  Truncated.Path.arrow f i

/-- The source of a 1-simplex in a path is identified with the source vertex. -/
lemma arrow_src (f : Path X n) (i : Fin n) :
    X.map (δ 1).op (f.arrow i) = f.vertex i.castSucc :=
  Truncated.Path.arrow_src f i

/-- The target of a 1-simplex in a path is identified with the target vertex. -/
lemma arrow_tgt (f : Path X n) (i : Fin n) :
    X.map (δ 0).op (f.arrow i) = f.vertex i.succ :=
  Truncated.Path.arrow_tgt f i

@[ext]
lemma ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  Truncated.Path.ext hᵥ hₐ

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Truncated.Path.ext' h

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n := by omega) : Path X l :=
  Truncated.Path.interval f j l h

variable {X Y : SSet.{u}} {n : ℕ}

/-- Maps of simplicial sets induce maps of paths in a simplicial set. -/
def map (f : Path X n) (σ : X ⟶ Y) : Path Y n :=
  Truncated.Path.map f ((truncation 1).map σ)

@[simp]
lemma map_vertex (f : Path X n) (σ : X ⟶ Y) (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op ⦋0⦌) (f.vertex i) :=
  rfl

@[simp]
lemma map_arrow (f : Path X n) (σ : X ⟶ Y) (i : Fin n) :
    (f.map σ).arrow i = σ.app (op ⦋1⦌) (f.arrow i) :=
  rfl

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (f : Path X n) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

section spine

variable (X : SSet.{u}) (n : ℕ)

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed
by traversing in order through the vertices of `X _⦋n⦌ₙ₊₁`. -/
def spine : X _⦋n⦌ → Path X n :=
  truncation (n + 1) |>.obj X |>.spine n

@[simp]
lemma spine_vertex (Δ : X _⦋n⦌) (i : Fin (n + 1)) :
    (X.spine n Δ).vertex i = X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op Δ :=
  rfl

@[simp]
lemma spine_arrow (Δ : X _⦋n⦌) (i : Fin n) :
    (X.spine n Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl

/-- For `m ≤ n + 1`, the `m`-spine of `X` factors through the `n + 1`-truncation
of `X`. -/
lemma truncation_spine (m : ℕ) (h : m ≤ n + 1) :
    ((truncation (n + 1)).obj X).spine m = X.spine m :=
  rfl

lemma spine_map_vertex (Δ : X _⦋n⦌) {m : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (X.spine m (X.map φ.op Δ)).vertex i =
      (X.spine n Δ).vertex (φ.toOrderHom i) :=
  truncation (max m n + 1) |>.obj X
    |>.spine_map_vertex n (by omega) Δ m (by omega) (InducedCategory.homMk φ) i

lemma spine_map_subinterval (j l : ℕ) (h : j + l ≤ n) (Δ : X _⦋n⦌) :
    X.spine l (X.map (subinterval j l h).op Δ) = (X.spine n Δ).interval j l h :=
  truncation (n + 1) |>.obj X |>.spine_map_subinterval n (by cutsat) j l h Δ

end spine

/-- The spine of the unique non-degenerate `n`-simplex in `Δ[n]`. -/
def stdSimplex.spineId (n : ℕ) : Path Δ[n] n :=
  spine Δ[n] n (objEquiv.symm (𝟙 _))

@[simp]
lemma stdSimplex.spineId_vertex (n : ℕ) (i : Fin (n + 1)) :
    (stdSimplex.spineId n).vertex i = obj₀Equiv.symm i := rfl

@[simp]
lemma stdSimplex.spineId_arrow_apply_zero (n : ℕ) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 0 = i.castSucc := rfl

@[simp]
lemma stdSimplex.spineId_arrow_apply_one (n : ℕ) (i : Fin n) :
    (stdSimplex.spineId n).arrow i 1 = i.succ := rfl

/-- A path of a simplicial set can be lifted to a subcomplex if the vertices
and arrows belong to this subcomplex. -/
@[simps]
def Subcomplex.liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ} (p : Path X n)
    (hp₀ : ∀ j, p.vertex j ∈ A.obj _)
    (hp₁ : ∀ j, p.arrow j ∈ A.obj _) :
    Path A n where
  vertex j := ⟨p.vertex j, hp₀ _⟩
  arrow j := ⟨p.arrow j, hp₁ _⟩
  arrow_src j := Subtype.ext <| p.arrow_src j
  arrow_tgt j := Subtype.ext <| p.arrow_tgt j

@[simp]
lemma Subcomplex.map_ι_liftPath {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ} (p : Path X n)
    (hp₀ : ∀ j, p.vertex j ∈ A.obj _)
    (hp₁ : ∀ j, p.arrow j ∈ A.obj _) :
    (A.liftPath p hp₀ hp₁).map A.ι = p := rfl

/-- Any inner horn contains the spine of the unique non-degenerate `n`-simplex
in `Δ[n]`. -/
@[simps! vertex_coe arrow_coe]
def horn.spineId {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path (Λ[n + 2, i] : SSet.{u}) (n + 2) :=
  Λ[n + 2, i].liftPath (stdSimplex.spineId (n + 2)) (by simp) (fun j ↦ by
    convert (horn.primitiveEdge.{u} h₀ hₙ j).2
    ext a
    fin_cases a <;> rfl)

@[simp]
lemma horn.spineId_map_hornInclusion {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId.{u} i h₀ hₙ) Λ[n + 2, i].ι =
      stdSimplex.spineId (n + 2) := rfl

end SSet
