/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Strict Segal simplicial sets are quasicategories

In `AlgebraicTopology.SimplicialSet.StrictSegal`, we define the strict Segal
condition on a simplicial set `X`. We say that `X` is strict Segal if its
simplices are uniquely determined by their spine.

In this file, we prove that any simplicial set satisfying the strict Segal
condition is a quasicategory.
-/

universe u

open CategoryTheory
open Simplicial SimplicialObject SimplexCategory

namespace SSet.StrictSegal

/-- Any `StrictSegal` simplicial set is a `Quasicategory`. -/
instance quasicategory {X : SSet.{u}} [StrictSegal X] : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
  use spineToSimplex <| Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by omega
  · rw [← spine_arrow, spine_δ_arrow_lt _ hlt]
    dsimp only [Path.map, spine_arrow, Fin.coe_eq_castSucc]
    apply congr_arg
    simp only [horn, horn.spineId, standardSimplex, uliftFunctor, Functor.comp_obj,
      yoneda_obj_obj, whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map,
      standardSimplex.objEquiv, Equiv.ulift, Equiv.coe_fn_symm_mk,
      Quiver.Hom.unop_op, horn.face_coe, Subtype.mk.injEq]
    rw [mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, spine_δ_arrow_gt _ hgt]
    dsimp only [Path.map, spine_arrow, Fin.coe_eq_castSucc]
    apply congr_arg
    simp only [horn, horn.spineId, standardSimplex, uliftFunctor, Functor.comp_obj,
      yoneda_obj_obj, whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map,
      standardSimplex.objEquiv, Equiv.ulift, Equiv.coe_fn_symm_mk,
      Quiver.Hom.unop_op, horn.face_coe, Subtype.mk.injEq]
    rw [mkOfSucc_δ_gt hgt]
    rfl
  · /- The only inner horn of `Δ[2]` does not contain the diagonal edge. -/
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain rfl : k = 0 := by omega
      fin_cases i <;> contradiction
    /- We construct the triangle in the standard simplex as a 2-simplex in
    the horn. While the triangle is not contained in the inner horn `Λ[2, 1]`,
    we can inhabit `Λ[n + 2, i] _[2]` by induction on `n`. -/
    let triangle : Λ[n + 2, i] _[2] := by
      cases n with
      | zero => contradiction
      | succ _ => exact horn.primitiveTriangle i h₀ hₙ k (by omega)
    /- The interval spanning from `k` to `k + 2` is equivalently the spine
    of the triangle with vertices `k`, `k + 1`, and `k + 2`. -/
    have hi : ((horn.spineId i h₀ hₙ).map σ₀).interval k 2 (by omega) =
        X.spine 2 (σ₀.app _ triangle) := by
      ext m
      dsimp [spine_arrow, Path.interval, Path.map]
      rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
      apply congr_arg
      simp only [horn, standardSimplex, uliftFunctor, Functor.comp_obj,
        whiskering_obj_obj_obj, yoneda_obj_obj, uliftFunctor_obj, ne_eq,
        whiskering_obj_obj_map, uliftFunctor_map, yoneda_obj_map, len_mk,
        Nat.reduceAdd, Quiver.Hom.unop_op]
      cases n with
      | zero => contradiction
      | succ _ => ext x; fin_cases x <;> fin_cases m <;> rfl
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

end SSet.StrictSegal
