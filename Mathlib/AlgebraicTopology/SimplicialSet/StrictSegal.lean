/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _[n] → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _[n]`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal`.

-/

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if
its simplices are uniquely determined by their spine. -/
structure StrictSegal {n : ℕ} (X : SSet.Truncated.{u} (n + 1)) where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by leq) : Path X m → X _[m]ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by leq) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1 := by leq) :
    spineToSimplex m ∘ spine X m = id

namespace StrictSegal

/- TODO: find a better way than this section to avoid capturing an extra `m`
in `spine_δ_arrow_eq`. -/
section

variable {n : ℕ} {X : SSet.Truncated.{u} (n + 1)} (segal : StrictSegal X)
  (m : ℕ) (h : m ≤ n + 1 := by leq)

lemma spine_spineToSimplex_apply (f : Path X m) :
    X.spine m h (segal.spineToSimplex m h f) = f :=
  congr_fun (segal.spine_spineToSimplex m) f

lemma spineToSimplex_spine_apply (Δ : X _[m]ₙ₊₁) :
    segal.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (spineToSimplex_spine segal m) Δ

/-- The fields of `StrictSegal` define an equivalence between `X _[m]ₙ₊₁`
and `Path X m`. -/
def spineEquiv : X _[m]ₙ₊₁ ≃ Path X m where
  toFun := spine X m
  invFun := segal.spineToSimplex m
  left_inv := segal.spineToSimplex_spine_apply m
  right_inv := segal.spine_spineToSimplex_apply m

theorem spineInjective : Function.Injective (spineEquiv segal m) :=
  Equiv.injective _

@[simp]
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (const [0] [m] i).op (segal.spineToSimplex m h f) = f.vertex i := by
  rw [← spine_vertex (h := h), spine_spineToSimplex_apply (h := h)]

@[simp]
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (mkOfSucc i).op (segal.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow (h := h), spine_spineToSimplex_apply (h := h)]

/- TODO: SimplicialObject.Truncated.diagonal -/
/-- In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex. -/
def spineToDiagonal : Path X m → X _[1]ₙ₊₁ :=
  X.map (diag m).op ∘ segal.spineToSimplex m h

@[simp]
theorem spineToSimplex_interval (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (subinterval j l hjl).op (segal.spineToSimplex m h f) =
      segal.spineToSimplex l (by leq) (f.interval j l hjl) := by
  apply segal.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply _ l]
  convert spine_map_subinterval X m h j l hjl (spineToSimplex _ m h f)
  exact segal.spine_spineToSimplex_apply m h f |>.symm

theorem spineToSimplex_edge (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (intervalEdge j l hjl).op (segal.spineToSimplex m h f) =
      segal.spineToDiagonal l (by leq) (f.interval j l hjl) := by
  dsimp [spineToDiagonal]
  rw [← spineToSimplex_interval (h := h), ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [diag_subinterval_eq]

end

/- TODO: spineToSimplex_map -/

section

variable {n : ℕ} {X : SSet.Truncated.{u} (n + 1)} (segal : StrictSegal X)
  (m : ℕ) (h : m ≤ n := by leq)

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (f : Path X (m + 1)) {i : Fin (m + 1)} {j : Fin (m + 2)}
    (hij : i.castSucc < j) :
    (X.spine m (by leq) (X.map (δ j).op
      (segal.spineToSimplex (m + 1) (by leq) f))).vertex i =
      f.vertex i.castSucc := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [const_comp, spineToSimplex_vertex _ (m + 1)]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (f : Path X (m + 1)) {i : Fin (m + 1)} {j : Fin (m + 2)}
    (hij : j ≤ i.castSucc) :
    (X.spine m (by leq) (X.map (δ j).op
      (segal.spineToSimplex (m + 1) (by leq) f))).vertex i =
      f.vertex i.succ := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [const_comp, spineToSimplex_vertex _ (m + 1)]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i hij]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}
    (hij : i.succ.castSucc < j) :
    (X.spine m (by leq) (X.map (δ j).op
      (segal.spineToSimplex (m + 1) (by leq) f))).arrow i =
      f.arrow i.castSucc := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [mkOfSucc_δ_lt hij, spineToSimplex_arrow _ (m + 1)]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}
    (hij : j < i.succ.castSucc) :
    (X.spine m (by leq) (X.map (δ j).op
      (segal.spineToSimplex (m + 1) (by leq) f))).arrow i =
      f.arrow i.succ := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [mkOfSucc_δ_gt hij, spineToSimplex_arrow _ (m + 1)]

end

lemma spine_δ_arrow_eq {n : ℕ} {X : SSet.Truncated.{u} (n + 2)} (segal : StrictSegal X)
    (m : ℕ) (h : m ≤ n + 1 := by leq) (f : Path X (m + 1))
    {i : Fin m} {j : Fin (m + 2)} (hij : j = i.succ.castSucc) :
    (X.spine m (by leq) (X.map (δ j).op
      (segal.spineToSimplex (m + 1) (by leq) f))).arrow i =
        segal.spineToDiagonal 2 (by leq) (f.interval i 2 (by leq)) := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply]
  erw [← op_comp (C := SimplexCategory)]
  rw [mkOfSucc_δ_eq hij, spineToSimplex_edge _ (m + 1)]

end StrictSegal
end Truncated

/-- A simplicial set `X` is `SSet.StrictSegal` if the `n + 1`-truncation of `X`
is `SSet.Truncated.StrictSegal` for all `n : ℕ`. -/
abbrev StrictSegal (X : SSet.{u}) :=
  ∀ n : ℕ, truncation (n + 1) |>.obj X |>.StrictSegal

namespace StrictSegal

variable {X : SSet.{u}} (segal : StrictSegal X) {n : ℕ}

/-- The inverse to `spine X n`. -/
abbrev spineToSimplex : Path X n → X _[n] := segal n |>.spineToSimplex n

  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
lemma spine_spineToSimplex : X.spine n ∘ segal.spineToSimplex = id :=
  segal n |>.spine_spineToSimplex n

/-- `spineToSimplex` is a left inverse to `spine X n`. -/
lemma spineToSimplex_spine : segal.spineToSimplex ∘ X.spine n = id :=
  segal n |>.spineToSimplex_spine n

lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n (segal.spineToSimplex f) = f :=
  segal n |>.spine_spineToSimplex_apply n _ f

lemma spineToSimplex_spine_apply (Δ : X _[n]) :
    segal.spineToSimplex (X.spine n Δ) = Δ :=
  segal n |>.spineToSimplex_spine_apply n _ Δ

/-- The fields of `StrictSegal` define an equivalence between `X _[m]`
and `Path X m`. -/
abbrev spineEquiv (n : ℕ) : X _[n] ≃ Path X n := segal n |>.spineEquiv n

theorem spineInjective : Function.Injective (segal.spineEquiv n) :=
  segal n |>.spineInjective n

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (segal.spineToSimplex f) = f.vertex i :=
  segal n |>.spineToSimplex_vertex n _ i f

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (segal.spineToSimplex f) = f.arrow i :=
  segal n |>.spineToSimplex_arrow n _ i f

/-- In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex. -/
abbrev spineToDiagonal (f : Path X n) : X _[1] :=
  segal n |>.spineToDiagonal n (by leq) f

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (segal.spineToSimplex f) =
      (segal n).spineToSimplex l (by leq) (f.interval j l hjl) :=
  segal n |>.spineToSimplex_interval n _ f j l hjl

theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) :
    X.map (intervalEdge j l hjl).op (segal.spineToSimplex f) =
      (segal n).spineToDiagonal l (by leq) (f.interval j l hjl) :=
  segal n |>.spineToSimplex_edge n _ f j l hjl

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : i.castSucc < j) :
    (X.spine n (X.δ j (segal.spineToSimplex f))).vertex i = f.vertex i.castSucc :=
  segal (n + 1) |>.spine_δ_vertex_lt n (by leq) f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (segal.spineToSimplex f))).vertex i = f.vertex i.succ :=
  segal (n + 1) |>.spine_δ_vertex_ge n (by leq) f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (segal.spineToSimplex f))).arrow i = f.arrow i.castSucc :=
  segal (n + 1) |>.spine_δ_arrow_lt n (by leq) f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (segal.spineToSimplex f))).arrow i = f.arrow i.succ :=
  segal (n + 1) |>.spine_δ_arrow_gt n (by leq) f h

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (segal.spineToSimplex f))).arrow i =
      (segal (n + 1)).spineToDiagonal 2 (by leq) (f.interval i 2 (by leq)) :=
  segal (n + 1) |>.spine_δ_arrow_eq n (by leq) f h

end StrictSegal
end SSet

open SSet Truncated

/-- Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor.-/
noncomputable def CategoryTheory.Nerve.strictSegal
    (C : Type u) [Category.{v} C] : StrictSegal (nerve C) :=
  fun n ↦ {
    spineToSimplex m h F :=
      ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
        (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
          (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
    spine_spineToSimplex m h := by
      ext F i
      · exact ComposableArrows.ext₀ rfl
      · refine ComposableArrows.ext₁ ?_ ?_ ?_
        · exact Functor.congr_obj (F.arrow_src i).symm 0
        · exact Functor.congr_obj (F.arrow_tgt i).symm 0
        · dsimp [truncation, SimplicialObject.truncation]
          apply ComposableArrows.mkOfObjOfMapSucc_map_succ
    spineToSimplex_spine m h := by
      ext F
      fapply ComposableArrows.ext
      · intro i
        rfl
      · intro i hi
        dsimp [truncation, SimplicialObject.truncation]
        exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi }
