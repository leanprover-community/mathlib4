/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _[n] → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _[n]`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.
-/

universe v u

open CategoryTheory

open Simplicial SimplicialObject SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal where
  /-- The inverse to `X.spine n`.-/
  spineToSimplex {n : ℕ} : Path X n → X _[n]
  /-- `spineToSimplex` is a right inverse to `X.spine n`.-/
  spine_spineToSimplex {n : ℕ} (f : Path X n) : X.spine n (spineToSimplex f) = f
  /-- `spineToSimplex` is a left inverse to `X.spine n`.-/
  spineToSimplex_spine {n : ℕ} (Δ : X _[n]) : spineToSimplex (X.spine n Δ) = Δ

namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

/-- The fields of `StrictSegal` define an equivalence between `X _[n]` and `Path X n`.-/
def spineEquiv (n : ℕ) : X _[n] ≃ Path X n where
  toFun := spine X n
  invFun := spineToSimplex
  left_inv := spineToSimplex_spine
  right_inv := spine_spineToSimplex

theorem spineInjective {n : ℕ} : Function.Injective (spineEquiv (X := X) n) := Equiv.injective _

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex]

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal (f : Path X n) : X _[1] := diagonal X (spineToSimplex f)

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

/-- If we take the path along the spine of face `i` of a `spineToSimplex`, the
common vertices will agree with those of the original path `f`. In particular,
a vertex `j` with `j < i` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (f : Path X (n + 1)) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    (X.spine n (X.δ i (spineToSimplex f))).vertex j = f.vertex j.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt i j h]

/-- If we take the path along the spine of face `i` of a `spineToSimplex`, a
vertex `j` with `j ≥ i` can be identified with vertex `j + 1` in the original
path. -/
lemma spine_δ_vertex_ge (f : Path X (n + 1)) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).vertex j = f.vertex j.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc i j h]

/-- If we take the path along the spine of face `i` of a `spineToSimplex`, the
common arrows will agree with those of the original path `f`. In particular, an
arrow `j` with `j + 1 < i` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (f : Path X (n + 1)) {i : Fin (n + 2)} {j : Fin n}
    (h : j.succ.castSucc < i) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j = f.arrow j.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]

/-- If we take the path along the spine of face `i` of a `spineToSimplex`, an
arrow `j` with `j + 1 > i` can be identified with arrow `j + 1` in the original
path. -/
lemma spine_δ_arrow_gt (f : Path X (n + 1)) {i : Fin (n + 2)} {j : Fin n}
    (h : i < j.succ.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j = f.arrow j.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `j` and `j + 1`. -/
lemma spine_δ_arrow_eq (f : Path X (n + 1)) {i : Fin (n + 2)} {j : Fin n}
    (h : i = j.succ.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j =
      spineToDiagonal (Path.interval f j 2 (by omega)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]

/-- Any `StrictSegal` simplicial set is a `Quasicategory`. -/
instance : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
  exists spineToSimplex <| Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply spineInjective
  ext k
  · simp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
    rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
    let ksucc := k.succ.castSucc
    have hkj : ksucc < j ∨ j < ksucc ∨ j = ksucc := by omega
    rcases hkj with hlt | hgt | heq
    · rw [← spine_arrow, spine_δ_arrow_lt _ hlt]
      simp only [Path.map, spine_arrow, Fin.coe_eq_castSucc]
      apply congr_arg
      simp only [horn, horn.spineId, standardSimplex, uliftFunctor, Functor.comp_obj,
        yoneda_obj_obj, whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map,
        standardSimplex.objEquiv, Equiv.ulift, Equiv.coe_fn_symm_mk,
        Quiver.Hom.unop_op, horn.face_coe, Subtype.mk.injEq]
      rw [mkOfSucc_δ_lt hlt]
      rfl
    · rw [← spine_arrow, spine_δ_arrow_gt _ hgt]
      simp only [Path.map, spine_arrow, Fin.coe_eq_castSucc]
      apply congr_arg
      simp only [horn, horn.spineId, standardSimplex, uliftFunctor, Functor.comp_obj,
        yoneda_obj_obj, whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map,
        standardSimplex.objEquiv, Equiv.ulift, Equiv.coe_fn_symm_mk,
        Quiver.Hom.unop_op, horn.face_coe, Subtype.mk.injEq]
      rw [mkOfSucc_δ_gt hgt]
      rfl
    · /- The only inner horn of `Δ[2]` does not contain the diagonal edge. -/
      have hn0 : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro h1; subst h1
        have hk : k = 0 := by omega
        have hs : ksucc ≠ i := by omega
        have hi : i = 1 := by fin_cases i <;> (try contradiction); rfl
        subst hi hk
        exact hs rfl
      /- We construct the triangle in the standard simplex as a 2-simplex in
      the horn. While the triangle is not contained in the inner horn `Λ[2, 1]`,
      we can inhabit `Λ[n + 2, i]` by induction on `n`. -/
      let triangle : Λ[n + 2, i] _[2] := by
        cases n with
        | zero => contradiction
        | succ _ => exact horn.primitiveTriangle i h₀ hₙ k (by omega)
      /- The interval spanning from `k` to `k + 2` is equivalently the spine
      of the triangle with vertices `k`, `k + 1`, and `k + 2`. -/
      have hi : ((horn.spineId i h₀ hₙ).map σ₀).interval k 2 (by omega) =
          X.spine 2 (σ₀.app _ triangle) := by
        ext m
        simp [spine_arrow, Path.interval, Path.map]
        rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
        apply congr_arg
        simp only [horn, standardSimplex, uliftFunctor, Functor.comp_obj,
          whiskering_obj_obj_obj, yoneda_obj_obj, uliftFunctor_obj, ne_eq,
          whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map, len_mk,
          Nat.reduceAdd, Quiver.Hom.unop_op]
        cases n with
        | zero => contradiction
        | succ _ => fin_cases m <;> (ext x; fin_cases x <;> rfl)
      rw [← spine_arrow, spine_δ_arrow_eq _ heq, hi]
      simp only [spineToDiagonal, diagonal, spineToSimplex_spine]
      rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality, types_comp_apply]
      apply congr_arg
      simp only [horn, standardSimplex, uliftFunctor, Functor.comp_obj,
        whiskering_obj_obj_obj, yoneda_obj_obj, uliftFunctor_obj,
        uliftFunctor_map, whiskering_obj_obj_map, yoneda_obj_map, horn.face_coe,
        len_mk, Nat.reduceAdd, Quiver.Hom.unop_op, Subtype.mk.injEq, ULift.up_inj]
      ext z
      cases n with
      | zero => contradiction
      | succ _ =>
        fin_cases z <;>
        · simp only [standardSimplex.objEquiv, uliftFunctor_map, yoneda_obj_map,
            Quiver.Hom.unop_op, Equiv.ulift_symm_down]
          rw [mkOfSucc_δ_eq heq]
          rfl

end StrictSegal

end SSet

namespace Nerve

open SSet

variable {C : Type*} [Category C] {n : ℕ}

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor.-/
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

/-- By virtue of satisfying the `StrictSegal` condition, the nerve of a
category is a `Quasicategory`. -/
instance : Quasicategory (nerve C) := inferInstance

end Nerve
