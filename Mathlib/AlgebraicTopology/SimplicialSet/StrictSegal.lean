/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if, for all `m : ℕ`,
the map `X.spine m : X _[m] → X.Path m` is an equivalence, with equivalence
inverse `spineToSimplex {m : ℕ} : Path X m → X _[m]`. We define this
construction first for `n + 1`-truncated simplicial sets in
`SSet.Truncated.StrictSegal`. The data of a `StrictSegal` simplicial set is
then defined by an `SSet.Truncated.StrictSegal` structure on the
`n + 1`-truncation of `X` for all `n : ℕ`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set
is isomorphic to the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal
which is proven in `Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal`.
-/

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if
its simplices are uniquely determined by their spine. -/
structure StrictSegal where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by omega) : Path X m → X _[m]ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1) :
    spineToSimplex m ∘ spine X m = id

/-- For an `n + 1`-truncated simplicial set `X`, `IsStrictSegal X` asserts the
mere existence of an inverse to `spine X m` for all `m ≤ n + 1`. -/
class IsStrictSegal : Prop where
  segal (m : ℕ) (h : m ≤ n + 1 := by omega) : Function.Bijective (X.spine m)

namespace StrictSegal

variable {X} (sx : StrictSegal X)

section spineToSimplex

@[simp]
lemma spine_spineToSimplex_apply (m : ℕ) (h : m ≤ n + 1) (f : Path X m) :
    X.spine m h (sx.spineToSimplex m h f) = f :=
  congr_fun (sx.spine_spineToSimplex m h) f

@[simp]
lemma spineToSimplex_spine_apply (m : ℕ) (h : m ≤ n + 1) (Δ : X _[m]ₙ₊₁) :
    sx.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine m h) Δ

section autoParam

variable (m : ℕ) (h : m ≤ n + 1 := by omega)

/-- The fields of `StrictSegal` define an equivalence between `X _[m]ₙ₊₁`
and `Path X m`. -/
def spineEquiv : X _[m]ₙ₊₁ ≃ Path X m where
  toFun := spine X m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

theorem spineInjective : Function.Injective (sx.spineEquiv m h) :=
  Equiv.injective _

/-- In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex. -/
def spineToDiagonal : Path X m → X _[1]ₙ₊₁ :=
  X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

end autoParam

/-- The unique existence of an inverse to `spine X m` for all `m ≤ n + 1`
implies the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  segal m h := sx.spineEquiv m h |>.bijective

variable (m : ℕ) (h : m ≤ n + 1)

@[simp]
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (tr (const [0] [m] i)).op (sx.spineToSimplex m h f) = f.vertex i := by
  rw [← spine_vertex (h := h), spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow (h := h), spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_interval (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (subinterval j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToSimplex l _ (f.interval j l hjl) := by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]
  convert spine_map_subinterval X m h j l hjl <| sx.spineToSimplex m h f
  exact sx.spine_spineToSimplex_apply m h f |>.symm

theorem spineToSimplex_edge (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (intervalEdge j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToDiagonal l (by omega) (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval, ← FunctorToTypes.map_comp_apply, ← op_comp,
    ← tr_comp, diag_subinterval_eq]

end spineToSimplex

open Opposite in
/-- For any `σ : X ⟶ Y` between `n + 1`-truncated `StrictSegal` simplicial sets,
`spineToSimplex` commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
    (sy : StrictSegal Y) (m : ℕ) (h : m ≤ n) (f : Path X (m + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (m + 1) _ (f.map σ) =
      σ.app (op [m + 1]ₙ₊₁) (sx.spineToSimplex (m + 1) _ f) := by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp only [spineToSimplex_arrow, types_comp_apply, Path.map_arrow]

section spine_δ

variable (m : ℕ) (h : m ≤ n) (f : Path X (m + 1))
variable {i : Fin (m + 1)} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (hij : i.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.castSucc := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    const_comp, spineToSimplex_vertex]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
    OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (hij : j ≤ i.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.succ := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    const_comp, spineToSimplex_vertex]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
    OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_le_castSucc j i hij]

variable {i : Fin m} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.castSucc := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_lt hij, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.succ := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_gt hij, spineToSimplex_arrow]

end spine_δ

variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) (m : ℕ)
  (h : m ≤ n + 1) (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}

lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i =
      sx.spineToDiagonal 2 (by omega) (f.interval i 2 (by omega)) := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_eq hij, spineToSimplex_edge]

end StrictSegal
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
structure StrictSegal where
  /-- The inverse to `spine X n`. -/
  spineToSimplex {n : ℕ} : Path X n → X _[n]
  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
  spine_spineToSimplex (n : ℕ) : spine X n ∘ spineToSimplex = id
  /-- `spineToSimplex` is a left inverse to `spine X n`. -/
  spineToSimplex_spine (n : ℕ) : spineToSimplex ∘ spine X n = id

/-- For `X` a simplicial set, `IsStrictSegal X` asserts the mere existence of
an inverse to `spine X n` for all `n : ℕ`. -/
class IsStrictSegal : Prop where
  segal (n : ℕ) : Function.Bijective (spine X n)

namespace StrictSegal

variable {X} (sx : StrictSegal X) {n : ℕ}

@[simp]
lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  congr_fun (sx.spine_spineToSimplex n) f

@[simp]
lemma spineToSimplex_spine_apply (Δ : X _[n]) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine n) Δ

/-- The fields of `StrictSegal` define an equivalence between `X _[n]`
and `Path X n`. -/
def spineEquiv (n : ℕ) : X _[n] ≃ Path X n where
  toFun := spine X n
  invFun := spineToSimplex sx
  left_inv := spineToSimplex_spine_apply sx
  right_inv := spine_spineToSimplex_apply sx

theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  Equiv.injective _

/-- The unique existence of an inverse to `spine X n` forall `n : ℕ` implies
the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  segal n := sx.spineEquiv n |>.bijective

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (sx.spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex_apply]

/-- In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal (f : Path X n) : X _[1] :=
  SimplicialObject.diagonal X (sx.spineToSimplex f)

section interval

variable (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n)

@[simp]
theorem spineToSimplex_interval :
    X.map (subinterval j l hjl).op (sx.spineToSimplex f) =
      sx.spineToSimplex (f.interval j l hjl) := by
  apply sx.spineInjective
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply, spine_map_subinterval,
    spine_spineToSimplex_apply]

theorem spineToSimplex_edge :
    X.map (intervalEdge j l hjl).op (sx.spineToSimplex f) =
      sx.spineToDiagonal (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, SimplicialObject.diagonal]
  rw [← spineToSimplex_interval, ← FunctorToTypes.map_comp_apply, ← op_comp,
    diag_subinterval_eq]

end interval

/-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X)
    (sy : StrictSegal Y) {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) := by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, Path.map, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp only [types_comp_apply, spineToSimplex_arrow, Path.map_arrow]

variable (f : Path X (n + 1))
variable {i : Fin (n + 1)} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i =
      f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i h]

variable {i : Fin n} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i =
      sx.spineToDiagonal (f.interval i 2 (by omega)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]

end StrictSegal
end SSet

open SSet Truncated

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor.-/
noncomputable def CategoryTheory.Nerve.strictSegal
  (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  spineToSimplex {n} F :=
    ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
      (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
        (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
  spine_spineToSimplex n := by
    ext F i
    · exact ComposableArrows.ext₀ rfl
    · refine ComposableArrows.ext₁ ?_ ?_ ?_
      · exact Functor.congr_obj (F.arrow_src i).symm 0
      · exact Functor.congr_obj (F.arrow_tgt i).symm 0
      · dsimp [truncation, SimplicialObject.truncation]
        apply ComposableArrows.mkOfObjOfMapSucc_map_succ
  spineToSimplex_spine n := by
    ext F
    fapply ComposableArrows.ext
    · intro i
      rfl
    · intro i hi
      dsimp [truncation, SimplicialObject.truncation]
      exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi
