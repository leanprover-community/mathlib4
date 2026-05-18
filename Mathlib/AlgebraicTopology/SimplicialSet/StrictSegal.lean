/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _⦋n⦌ → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open Opposite SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if
its `m`-simplices are uniquely determined by their spine for all `m ≤ n + 1`. -/
structure StrictSegal where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by lia) : Path X m → X _⦋m⦌ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1) :
    spineToSimplex m ∘ spine X m = id

/-- For an `n + 1`-truncated simplicial set `X`, `IsStrictSegal X` asserts the
mere existence of an inverse to `spine X m` for all `m ≤ n + 1`. -/
class IsStrictSegal (X : SSet.Truncated.{u} (n + 1)) : Prop where
  spine_bijective (X) (m : ℕ) (h : m ≤ n + 1 := by grind) : Function.Bijective (X.spine m)

export IsStrictSegal (spine_bijective)

lemma spine_injective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : ℕ} {h : m ≤ n + 1} :
    Function.Injective (X.spine m) :=
  (spine_bijective X m).injective

lemma spine_surjective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : ℕ} (p : X.Path m) (h : m ≤ n + 1 := by grind) :
    ∃ (x : X _⦋m⦌ₙ₊₁), X.spine m _ x = p :=
  (spine_bijective X m).surjective p

variable {X} in
lemma IsStrictSegal.ext [X.IsStrictSegal] {d : ℕ} {hd} {x y : X _⦋d + 1⦌ₙ₊₁}
    (h : ∀ (i : Fin (d + 1)),
      X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op x =
        X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op y) :
    x = y :=
  X.spine_injective (by ext i; apply h)

variable {X} in
lemma IsStrictSegal.hom_ext {Y : SSet.Truncated.{u} (n + 1)} [Y.IsStrictSegal]
    {f g : X ⟶ Y} (h : ∀ (x : X _⦋1⦌ₙ₊₁), f.app _ x = g.app _ x) : f = g := by
  ext ⟨⟨m, hm⟩⟩ x
  induction m using SimplexCategory.rec with | _ m
  obtain _ | m := m
  · have fac := δ_comp_σ_self (i := (0 : Fin 1))
    dsimp at fac
    simpa [← NatTrans.naturality_apply,
      ← Functor.map_comp_apply, ← op_comp,
      ← SimplexCategory.Truncated.Hom.tr_comp, fac] using
      congr_arg (Y.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ 0)).op)
        (h (X.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ 0)).op x))
  · exact IsStrictSegal.ext (fun i ↦ by simp [← NatTrans.naturality_apply, h])

namespace StrictSegal

/-- Given `IsStrictSegal X`, a choice of inverse to `spine X m` for all
`m ≤ n + 1` determines an inhabitant of `StrictSegal X`. -/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex m h :=
    Equiv.ofBijective (X.spine m) (X.spine_bijective m h) |>.invFun
  spine_spineToSimplex m _ :=
    funext <| Equiv.ofBijective (X.spine m) _ |>.right_inv
  spineToSimplex_spine m _ :=
    funext <| Equiv.ofBijective (X.spine m) _ |>.left_inv

variable {X} (sx : StrictSegal X)

section spineToSimplex

@[simp]
lemma spine_spineToSimplex_apply (m : ℕ) (h : m ≤ n + 1) (f : Path X m) :
    X.spine m h (sx.spineToSimplex m h f) = f :=
  congr_fun (sx.spine_spineToSimplex m h) f

@[simp]
lemma spineToSimplex_spine_apply (m : ℕ) (h : m ≤ n + 1) (Δ : X _⦋m⦌ₙ₊₁) :
    sx.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine m h) Δ

section autoParam

variable (m : ℕ) (h : m ≤ n + 1 := by lia)

set_option backward.privateInPublic true in
/-- The fields of `StrictSegal` define an equivalence between `X _⦋m⦌ₙ₊₁`
and `Path X m`. -/
def spineEquiv : X _⦋m⦌ₙ₊₁ ≃ Path X m where
  toFun := X.spine m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

set_option backward.privateInPublic true in
theorem spineInjective : Function.Injective (sx.spineEquiv m h) :=
  Equiv.injective _

set_option backward.privateInPublic true in
/-- In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex. -/
def spineToDiagonal : Path X m → X _⦋1⦌ₙ₊₁ :=
  X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

end autoParam

/-- The unique existence of an inverse to `spine X m` for all `m ≤ n + 1`
implies the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  spine_bijective m h := sx.spineEquiv m h |>.bijective

variable (m : ℕ) (h : m ≤ n + 1)

@[simp]
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op (sx.spineToSimplex m h f) =
      f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex_apply]

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
      sx.spineToDiagonal l (by lia) (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval, ← Functor.map_comp_apply, ← op_comp,
    ← tr_comp, diag_subinterval_eq]

end spineToSimplex

/-- For any `σ : X ⟶ Y` between `n + 1`-truncated `StrictSegal` simplicial sets,
`spineToSimplex` commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
    (sy : StrictSegal Y) (m : ℕ) (h : m ≤ n) (f : Path X (m + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (m + 1) _ (f.map σ) =
      σ.app (op ⦋m + 1⦌ₙ₊₁) (sx.spineToSimplex (m + 1) _ f) := by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp [-NatTrans.naturality]

section spine_δ

variable (m : ℕ) (h : m ≤ n) (f : Path X (m + 1))
variable {i : Fin (m + 1)} {j : Fin (m + 2)}

set_option backward.defeqAttrib.useBackward true in
/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (hij : i.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.castSucc := by
  rw [spine_vertex, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    SimplexCategory.const_comp, spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

set_option backward.defeqAttrib.useBackward true in
/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (hij : j ≤ i.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.succ := by
  rw [spine_vertex, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    SimplexCategory.const_comp, spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_le_castSucc j i hij]

variable {i : Fin m} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.castSucc := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_lt hij, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.succ := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_gt hij, spineToSimplex_arrow]

end spine_δ

variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) (m : ℕ)
  (h : m ≤ n + 1) (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}

lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i =
      sx.spineToDiagonal 2 (by lia) (f.interval i 2 (by lia)) := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_eq hij, spineToSimplex_edge]

end StrictSegal
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
structure StrictSegal where
  /-- The inverse to `spine X n`. -/
  spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌
  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
  spine_spineToSimplex (n : ℕ) : spine X n ∘ spineToSimplex = id
  /-- `spineToSimplex` is a left inverse to `spine X n`. -/
  spineToSimplex_spine (n : ℕ) : spineToSimplex ∘ spine X n = id

/-- For `X` a simplicial set, `IsStrictSegal X` asserts the mere existence of
an inverse to `spine X n` for all `n : ℕ`. -/
class IsStrictSegal : Prop where
  segal (n : ℕ) : Function.Bijective (spine X n)

namespace StrictSegal

/-- Given `IsStrictSegal X`, a choice of inverse to `spine X n` for all `n : ℕ`
determines an inhabitant of `StrictSegal X`. -/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex {n} :=
    Equiv.ofBijective (X.spine n) (IsStrictSegal.segal n) |>.invFun
  spine_spineToSimplex n :=
    funext <| Equiv.ofBijective (X.spine n) _ |>.right_inv
  spineToSimplex_spine n :=
    funext <| Equiv.ofBijective (X.spine n) _ |>.left_inv

variable {X} (sx : StrictSegal X)

/-- A `StrictSegal` structure on a simplicial set `X` restricts to a
`Truncated.StrictSegal` structure on the `n + 1`-truncation of `X`. -/
protected def truncation (n : ℕ) : truncation (n + 1) |>.obj X |>.StrictSegal where
  spineToSimplex _ _ := sx.spineToSimplex
  spine_spineToSimplex m _ := sx.spine_spineToSimplex m
  spineToSimplex_spine m _ := sx.spineToSimplex_spine m

instance [X.IsStrictSegal] (n : ℕ) :
    ((truncation (n + 1)).obj X).IsStrictSegal :=
  ((ofIsStrictSegal X).truncation n).isStrictSegal

@[simp]
lemma spine_spineToSimplex_apply {n : ℕ} (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  congr_fun (sx.spine_spineToSimplex n) f

@[simp]
lemma spineToSimplex_spine_apply {n : ℕ} (Δ : X _⦋n⦌) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine n) Δ

/-- The fields of `StrictSegal` define an equivalence between `X _⦋n⦌`
and `Path X n`. -/
def spineEquiv (n : ℕ) : X _⦋n⦌ ≃ Path X n where
  toFun := X.spine n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

variable {n : ℕ}

theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  Equiv.injective _

/-- The unique existence of an inverse to `spine X n` forall `n : ℕ` implies
the mere existence of such an inverse. -/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  segal n := sx.spineEquiv n |>.bijective

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (sx.spineToSimplex f) =
      f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex_apply]

/-- In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal (f : Path X n) : X _⦋1⦌ :=
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
  rw [← spineToSimplex_interval, ← Functor.map_comp_apply, ← op_comp,
    diag_subinterval_eq]

end interval

/-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`. -/
lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X)
    (sy : StrictSegal Y) {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) := by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality, types_comp_apply,
    spineToSimplex_arrow, spineToSimplex_arrow, Path.map_arrow]

variable (f : Path X (n + 1))
variable {i : Fin (n + 1)} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i =
      f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
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
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i =
      sx.spineToDiagonal (f.interval i 2 (by lia)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]

end StrictSegal

/-- Helper structure in order to show that a simplicial set is strict Segal. -/
structure StrictSegalCore (n : ℕ) where
  /-- Map which produces an `n + 1`-simplex from a `1`-simplex and an `n`-simplex when
  the target vertex of the `1`-simplex equals the zeroth simplex of the `n`-simplex. -/
  concat (x : X _⦋1⦌) (s : X _⦋n⦌) (h : X.δ 0 x = X.map (SimplexCategory.const _ _ 0).op s) :
    X _⦋n + 1⦌
  map_mkOfSucc_zero_concat x s h : X.map (mkOfSucc 0).op (concat x s h) = x
  δ₀_concat x s h : X.δ 0 (concat x s h) = s
  injective {x y : X _⦋n + 1⦌} (h : X.map (mkOfSucc 0).op x = X.map (mkOfSucc 0).op y)
    (h₀ : X.δ 0 x = X.δ 0 y) : x = y

namespace StrictSegalCore

variable {X} (h : ∀ n, X.StrictSegalCore n) {n : ℕ} (p : X.Path n)

/-- Auxiliary definition for `StrictSegalCore.spineToSimplex`. -/
def spineToSimplexAux : { s : X _⦋n⦌ // X.spine _ s = p } := by
  induction n with
  | zero => exact ⟨p.vertex 0, by aesop⟩
  | succ n hn =>
    refine ⟨(h n).concat (p.arrow 0) (hn (p.interval 1 n)).val ?_, ?_⟩
    · rw [p.arrow_tgt 0]
      exact Path.congr_vertex (hn (p.interval 1 n)).prop.symm 0
    · ext i
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · dsimp
        rw [map_mkOfSucc_zero_concat]
      · simpa [spine_arrow, ← SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp),
          op_comp, Functor.map_comp_apply, ← SimplicialObject.δ_def, δ₀_concat,
          ← p.arrow_interval 1 n i i.succ (by grind) (by grind)] using
            Path.congr_arrow (hn (p.interval 1 n)).prop i

/-- Auxiliary definition for `StrictSegal.ofCore`. -/
def spineToSimplex : X _⦋n⦌ := (spineToSimplexAux h p).val

@[simp]
lemma spine_spineToSimplex : X.spine n (spineToSimplex h p) = p := (spineToSimplexAux h p).prop

lemma spineToSimplex_zero (p : X.Path 0) : spineToSimplex h p = p.vertex 0 := rfl

lemma spineToSimplex_succ (p : X.Path (n + 1)) :
    spineToSimplex h p = (h n).concat (p.arrow 0) (spineToSimplex h (p.interval 1 n)) (by
      rw [p.arrow_tgt 0]
      exact Path.congr_vertex (spine_spineToSimplex h (p.interval 1 n)).symm 0) :=
  rfl

lemma map_mkOfSucc_zero_spineToSimplex (p : X.Path (n + 1)) :
    X.map (mkOfSucc 0).op (spineToSimplex h p) = p.arrow 0 := by
  rw [spineToSimplex_succ, map_mkOfSucc_zero_concat]

lemma δ₀_spineToSimplex (p : X.Path (n + 1)) :
    X.δ 0 (spineToSimplex h p) = spineToSimplex h (p.interval 1 n) := by
  rw [spineToSimplex_succ, δ₀_concat]

@[simp]
lemma spineToSimplex_spine (s : X _⦋n⦌) : spineToSimplex h (X.spine _ s) = s := by
  induction n with
  | zero => simp [spineToSimplex_zero]
  | succ n hn =>
    exact (h n).injective (map_mkOfSucc_zero_spineToSimplex _ _)
      (by rw [δ₀_spineToSimplex, ← hn (X.δ 0 s), spine_δ₀])

end StrictSegalCore

variable {X} in
/-- Given a simplicial set `X`, this constructs a `StrictSegal` structure for `X` from
`StrictSegalCore` structures for all `n : ℕ`. -/
def StrictSegal.ofCore (h : ∀ n, X.StrictSegalCore n) : X.StrictSegal where
  spineToSimplex := StrictSegalCore.spineToSimplex h
  spine_spineToSimplex := by aesop
  spineToSimplex_spine n := by aesop

end SSet

namespace CategoryTheory.Nerve

open SSet

variable (C : Type u) [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor. -/
def strictSegal : StrictSegal (nerve C) :=
  StrictSegal.ofCore (fun n ↦
    { concat f s h := s.precomp (f.hom ≫ eqToHom (Functor.congr_obj h 0))
      map_mkOfSucc_zero_concat f s h :=
        ComposableArrows.ext₁ rfl (Functor.congr_obj h 0).symm (by cat_disch)
      δ₀_concat f s h := rfl
      injective {f g} h h₀ :=
        ComposableArrows.ext_succ (Functor.congr_obj h 0) h₀
          ((Arrow.mk_eq_mk_iff _ _).1
            (DFunLike.congr_arg ComposableArrows.arrowEquiv h)).2.2 })

instance isStrictSegal : IsStrictSegal (nerve C) :=
  strictSegal C |>.isStrictSegal

end CategoryTheory.Nerve
