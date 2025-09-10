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
theorem quasicategory {X : SSet.{u}} (sx : StrictSegal X) : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
  use sx.spineToSimplex <| Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by omega
  · rw [← spine_arrow, spine_δ_arrow_lt sx _ hlt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [Subcomplex.yonedaEquiv_coe, Subpresheaf.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, stdSimplex.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, spine_δ_arrow_gt sx _ hgt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [Subcomplex.yonedaEquiv_coe, Subpresheaf.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, stdSimplex.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_gt hgt]
    rfl
  · obtain _ | n := n
    · /- The only inner horn of `Δ[2]` does not contain the diagonal edge. -/
      obtain rfl : k = 0 := by omega
      fin_cases i <;> contradiction
    · /- We construct the triangle in the standard simplex as a 2-simplex in
      the horn. While the triangle is not contained in the inner horn `Λ[2, 1]`,
      it suffices to inhabit `Λ[n + 3, i] _⦋2⦌`. -/
      let triangle : (Λ[n + 3, i] : SSet.{u}) _⦋2⦌ :=
        horn.primitiveTriangle i h₀ hₙ k (by omega)
      /- The interval spanning from `k` to `k + 2` is equivalently the spine
      of the triangle with vertices `k`, `k + 1`, and `k + 2`. -/
      have hi : ((horn.spineId i h₀ hₙ).map σ₀).interval k 2 (by omega) =
          X.spine 2 (σ₀.app _ triangle) := by
        ext m
        dsimp [spine_arrow, Path.map_interval, Path.map_arrow]
        rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
        apply congr_arg
        apply Subtype.ext
        ext a : 1
        fin_cases a <;> fin_cases m <;> rfl
      rw [← spine_arrow, spine_δ_arrow_eq sx _ heq, hi]
      simp only [spineToDiagonal, diagonal, spineToSimplex_spine_apply]
      rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality, types_comp_apply]
      apply congr_arg
      apply Subtype.ext
      ext z : 1
      dsimp [horn.face]
      rw [Subcomplex.yonedaEquiv_coe, Subpresheaf.lift_ι, stdSimplex.map_apply,
        Quiver.Hom.unop_op, stdSimplex.map_apply, Quiver.Hom.unop_op]
      dsimp [CosimplicialObject.δ]
      rw [stdSimplex.yonedaEquiv_map]
      simp only [Equiv.apply_symm_apply, triangle]
      rw [mkOfSucc_δ_eq heq]
      fin_cases z <;> rfl

/-- Any simplicial set satisfying `IsStrictSegal` is a `Quasicategory`. -/
instance quasicategory' (X : SSet.{u}) [IsStrictSegal X] : Quasicategory X :=
  quasicategory <| ofIsStrictSegal X

end SSet.StrictSegal
