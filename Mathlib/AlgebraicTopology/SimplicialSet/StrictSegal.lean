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
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by leq) : Path X m → X _[m]ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by leq) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1 := by leq) :
    spineToSimplex m ∘ spine X m = id

/-- For an `n + 1`-truncated simplicial set `X`, `IsStrictSegal X` asserts the
mere existence of an inverse to `spine X m` for all `m ≤ n + 1`. -/
class IsStrictSegal : Prop where
  segal (m : ℕ) (h : m ≤ n + 1 := by leq) : Function.Bijective (X.spine m)

namespace StrictSegal

variable {X} (sx : StrictSegal X) (m : ℕ)

section spineToSimplex

variable (h : m ≤ n + 1 := by leq)

lemma spine_spineToSimplex_apply (f : Path X m) :
    X.spine m h (sx.spineToSimplex m h f) = f :=
  congr_fun (sx.spine_spineToSimplex m) f

lemma spineToSimplex_spine_apply (Δ : X _[m]ₙ₊₁) :
    sx.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (spineToSimplex_spine sx m) Δ

/-- The fields of `StrictSegal` define an equivalence between `X _[m]ₙ₊₁`
and `Path X m`. -/
def spineEquiv : X _[m]ₙ₊₁ ≃ Path X m where
  toFun := spine X m
  invFun := sx.spineToSimplex m
  left_inv := sx.spineToSimplex_spine_apply m
  right_inv := sx.spine_spineToSimplex_apply m

theorem spineInjective : Function.Injective (sx.spineEquiv m) :=
  Equiv.injective _

/-- The unique existence of an inverse to `spine X m` for all `m ≤ n + 1`
implies the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  segal m h := sx.spineEquiv m h |>.bijective

@[simp]
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (tr (const [0] [m] i)).op (sx.spineToSimplex m h f) =
      f.vertex i := by
  rw [← spine_vertex (h := h), spine_spineToSimplex_apply (h := h)]

@[simp]
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow (h := h), spine_spineToSimplex_apply (h := h)]

/-- In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex. -/
def spineToDiagonal : Path X m → X _[1]ₙ₊₁ :=
  X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

@[simp]
theorem spineToSimplex_interval (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (subinterval j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToSimplex l (by leq) (f.interval j l hjl) := by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply _ l]
  convert spine_map_subinterval X m h j l hjl (spineToSimplex _ m h f)
  exact sx.spine_spineToSimplex_apply m h f |>.symm

theorem spineToSimplex_edge (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (intervalEdge j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToDiagonal l (by leq) (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval (h := h), ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← tr_comp, diag_subinterval_eq]

end spineToSimplex

open Opposite in
/-- For any `σ : X ⟶ Y` between `n + 1`-truncated `StrictSegal` simplicial sets,
`spineToSimplex` commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)}
    (sx : StrictSegal X) (sy : StrictSegal Y)
    (m : ℕ) (h : m ≤ n := by leq) (f : Path X (m + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (m + 1) (by leq) (f.map σ) =
      σ.app (op [m + 1]ₙ₊₁) (sx.spineToSimplex (m + 1) (by leq) f) := by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp only [spineToSimplex_arrow, types_comp_apply, Path.map_arrow]

section spine_δ

variable (h : m ≤ n := by leq) (f : Path X (m + 1))
variable {i : Fin (m + 1)} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (hij : i.castSucc < j) :
    (X.spine m (by leq) (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) (by leq) f))).vertex i =
      f.vertex i.castSucc := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    const_comp, spineToSimplex_vertex _ (m + 1)]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
    OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (hij : j ≤ i.castSucc) :
    (X.spine m (by leq) (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) (by leq) f))).vertex i =
      f.vertex i.succ := by
  rw [spine_vertex X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    const_comp, spineToSimplex_vertex _ (m + 1)]
  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
    OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_le_castSucc j i hij]

variable {i : Fin m} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) :
    (X.spine m (by leq) (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) (by leq) f))).arrow i =
      f.arrow i.castSucc := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_lt hij, spineToSimplex_arrow _ (m + 1)]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) :
    (X.spine m (by leq) (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) (by leq) f))).arrow i =
      f.arrow i.succ := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_gt hij, spineToSimplex_arrow _ (m + 1)]

end spine_δ

variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) (m : ℕ)
  (h : m ≤ n + 1 := by leq) (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}

lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) :
    (X.spine m (by leq) (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) (by leq) f))).arrow i =
      sx.spineToDiagonal 2 (by leq) (f.interval i 2 (by leq)) := by
  rw [spine_arrow X m, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_eq hij, spineToSimplex_edge _ (m + 1)]

end StrictSegal
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` is `SSet.StrictSegal` if the `n + 1`-truncation of `X`
is `SSet.Truncated.StrictSegal` for all `n : ℕ`. -/
abbrev StrictSegal := ∀ n : ℕ, truncation (n + 1) |>.obj X |>.StrictSegal

/-- For `X` a simplicial set, `SSet.IsStrictSegal X` asserts that the `n + 1`
truncation of `X` satisfies `SSet.Truncated.IsStrictSegal` for all `n : ℕ`. -/
abbrev IsStrictSegal := ∀ n : ℕ, truncation (n + 1) |>.obj X |>.IsStrictSegal

namespace StrictSegal

variable {X} (sx : StrictSegal X) {n : ℕ}

/-- The inverse to `spine X n`. -/
abbrev spineToSimplex : Path X n → X _[n] := sx n |>.spineToSimplex n

  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
lemma spine_spineToSimplex : X.spine n ∘ sx.spineToSimplex = id :=
  sx n |>.spine_spineToSimplex n

/-- `spineToSimplex` is a left inverse to `spine X n`. -/
lemma spineToSimplex_spine : sx.spineToSimplex ∘ X.spine n = id :=
  sx n |>.spineToSimplex_spine n

lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  sx n |>.spine_spineToSimplex_apply n _ f

lemma spineToSimplex_spine_apply (Δ : X _[n]) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  sx n |>.spineToSimplex_spine_apply n _ Δ

/-- The fields of `StrictSegal` define an equivalence between `X _[m]`
and `Path X m`. -/
abbrev spineEquiv (n : ℕ) : X _[n] ≃ Path X n := sx n |>.spineEquiv n

theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  sx n |>.spineInjective n

/-- The unique existence of an inverse to `spine X n` forall `n : ℕ` implies
the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X :=
  fun n ↦ sx n |>.isStrictSegal

lemma spineEquiv_coe_fn (n : ℕ) : ⇑(sx.spineEquiv n) = X.spine n := rfl

lemma spineEquiv_symm_coe_fn (n : ℕ) :
    ⇑(sx.spineEquiv n).symm = sx.spineToSimplex := rfl

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (sx.spineToSimplex f) = f.vertex i :=
  sx n |>.spineToSimplex_vertex n _ i f

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i :=
  sx n |>.spineToSimplex_arrow n _ i f

/-- In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex. -/
abbrev spineToDiagonal : Path X n → X _[1] := sx n |>.spineToDiagonal n

lemma spineToDiagonal_def :
    sx.spineToDiagonal = X.map (diag n).op ∘ sx.spineToSimplex := rfl

section interval

variable (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n)

@[simp]
theorem spineToSimplex_interval :
    X.map (subinterval j l hjl).op (sx.spineToSimplex f) =
      (sx n).spineToSimplex l (by leq) (f.interval j l hjl) :=
  sx n |>.spineToSimplex_interval n _ f j l hjl

theorem spineToSimplex_edge :
    X.map (intervalEdge j l hjl).op (sx.spineToSimplex f) =
      (sx n).spineToDiagonal l (by leq) (f.interval j l hjl) :=
  sx n |>.spineToSimplex_edge n _ f j l hjl

end interval

/-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X)
    (sy : StrictSegal Y) {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) :=
  sx (n + 1) |>.spineToSimplex_map (sy _) n (by leq) f ((truncation _).map σ)

variable (f : Path X (n + 1))
variable {i : Fin (n + 1)} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i =
      f.vertex i.castSucc :=
  sx (n + 1) |>.spine_δ_vertex_lt n (by leq) f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ :=
  sx (n + 1) |>.spine_δ_vertex_ge n (by leq) f h

variable {i : Fin n} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc :=
  sx (n + 1) |>.spine_δ_arrow_lt n (by leq) f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ :=
  sx (n + 1) |>.spine_δ_arrow_gt n (by leq) f h

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i =
      (sx (n + 1)).spineToDiagonal 2 (by leq) (f.interval i 2 (by leq)) :=
  sx (n + 1) |>.spine_δ_arrow_eq n (by leq) f h

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
