/-
Copyright (c) 2025 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Boundary of the standard simplex

In `AlgebraicTopology.SimplicialSet.Basic`, we define the boundary `∂Δ[n]` of
the `n`th standard simplex as the simplicial set consisting of all
`m`-simplices of `Δ[n]` that are not surjective when viewed as monotone
functions from `[m]` to `[n]`.

In this file, we provide a description of `∂Δ[n]` as a colimit of the standard
simplices, following the proof of [Kerodon, 0504](https://kerodon.net/tag/0504).
-/

open Fin CategoryTheory Limits Simplicial SimplexCategory

namespace SSet.boundary
open standardSimplex

/-- The boundary `∂Δ[n]` is the coequalizer of a parallel pair of morphisms
between two coproducts of the standard simplices indexed over `Fin (n + 3)`. -/
def diagram (n : ℕ) : MultispanIndex SSet where
  L := { (i, j) : Fin (n + 2) × Fin (n + 2) | i ≤ j }
  R := Fin (n + 3)
  fstFrom p := p.1.1.castSucc
  sndFrom p := p.1.2.succ
  left _ := Δ[n]
  right _ := Δ[n + 1]
  fst p := standardSimplex.map <| δ p.1.2
  snd p := standardSimplex.map <| δ p.1.1

/-- The boundary `∂Δ[n]` forms a cone under the coequalizer diagram above. -/
abbrev cocone (n : ℕ) : Multicofork (diagram n) := by
  refine Multicofork.ofπ (diagram n) ∂Δ[n + 2] ?_ ?_
  · intro k
    refine {
      app := fun m α ↦ ⟨standardSimplex.map (δ k) |>.app m α, ?_⟩
      naturality := fun a b f ↦ rfl }
    apply succAbove_not_surjective ∘ Function.Surjective.of_comp
  · intro ⟨⟨i, j⟩, h⟩
    ext m α
    apply Subtype.ext
    rw [NatTrans.comp_app, NatTrans.comp_app]
    dsimp only [diagram, Set.coe_setOf, Set.mem_setOf_eq, types_comp_apply]
    rw [← FunctorToTypes.comp, ← Functor.map_comp, ← δ_comp_δ h]
    rfl

/-- By definition, an `m`-simplex in `∂Δ[n]` is not surjective when viewed as
a monotone function from `[m]` to `[n]`. We use the axiom of choice to pick
`i : Fin (n + 1)` such that `i` is not in the image of `α`. -/
noncomputable def skips {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj m) :
    Fin (n + 1) := Classical.choose <| not_forall.mp α.property

/-- Our chosen element of `Fin (n + 1)` is indeed not in the image of `α`. -/
lemma skips_spec {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj m) :
    ∀ k : Fin (m.unop.len + 1), asOrderHom α.1 k ≠ skips α :=
  not_exists.mp <| Classical.choose_spec <| not_forall.mp α.2

/-- -/
abbrev factor_δ₂ {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 2)) (j : Fin (n + 3)) : Δ[n].obj m :=
  factor_δ (factor_δ α j) i

lemma δ_factor_δ₂_le {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i j : Fin (n + 2)} (h : i ≤ j) (hi : ∀ x, asOrderHom α x ≠ i.castSucc)
    (hj : ∀ x, asOrderHom α x ≠ j.succ) :
    (standardSimplex.map (δ i)).app m (factor_δ₂ α i j.succ) =
      factor_δ α j.succ := by
  simp only [standardSimplex.factor_δ, predAbove_zero_succ]
  apply standardSimplex.factor_δ_spec
  intro k; specialize hi k; specialize hj k
  simp only [σ, asOrderHom, yoneda_obj_obj, standardSimplex, uliftFunctor,
    Functor.comp_obj, mkHom, Functor.comp_map,
    SimplicialObject.whiskering_obj_map_app, uliftFunctor_map, yoneda_map_app,
    comp_toOrderHom, len_mk, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderHom.coe_mk, Function.comp_apply, ne_eq]
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact hi ∘ (predAbove_eq_lt_iff h _).mp
  · exact not_or.mpr (And.intro hi hj) ∘ (predAbove_eq_self_iff i _).mp

lemma δ_factor_δ₂_ge {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i j : Fin (n + 2)} (h : i ≤ j) (hi : ∀ x, asOrderHom α x ≠ i.castSucc)
    (hj : ∀ x, asOrderHom α x ≠ j.succ) :
    (standardSimplex.map (δ j)).app m (factor_δ₂ α i j.succ) =
      factor_δ α i.castSucc := by
  simp only [standardSimplex.factor_δ, standardSimplex, uliftFunctor,
    Functor.comp_obj, SimplicialObject.whiskering_obj_obj_obj, yoneda_obj_obj,
    uliftFunctor_obj, Functor.comp_map, SimplicialObject.whiskering_obj_map_app,
    uliftFunctor_map, yoneda_map_app, Category.assoc, ULift.up_inj]
  rw [σ_predAbove_zero_comp_σ_predAbove_zero_assoc h]
  change factor_δ (m := m.unop.len) (_ ≫ σ _) _ ≫ δ _ = _
  apply SimplexCategory.factor_δ_spec
  intro k; specialize hi k; specialize hj k
  dsimp [σ]
  rcases lt_or_eq_of_le h with (h | rfl)
  · refine hj ∘ (predAbove_eq_gt_iff ?_ _).mp
    refine lt_of_le_of_lt ?_ h
    exact castSucc_le_castSucc_iff.mp <| castSucc_predAbove_le _ _
  · cases' i using cases with i
    · exact not_or.mpr (And.intro hi hj) ∘ (predAbove_eq_self_iff 0 _).mp
    · rw [← succ_castSucc, predAbove_zero_succ]
      exact hj ∘ (predAbove_eq_gt_iff (castSucc_lt_succ i) _).mp

lemma π_factor_δ_lt {n : ℕ} (X : Multicofork (diagram n)) {m : SimplexCategoryᵒᵖ}
    (α : Δ[n + 2].obj m) {i j : Fin (n + 3)} (h : i < j)
    (hi : ∀ x, asOrderHom α x ≠ i) (hj : ∀ x, asOrderHom α x ≠ j) :
    (X.π i).app m (factor_δ α i) = (X.π j).app m (factor_δ α j) := by
  have hlast := ne_last_of_lt h
  have h0 := ne_zero_of_lt h
  have hle := castPred_le_pred_iff hlast h0 |>.mpr h
  let ij : { (i, j) : Fin (n + 2) × Fin (n + 2) | i ≤ j } :=
    ⟨(i.castPred hlast, j.pred h0), hle⟩
  rw [← castSucc_castPred i hlast] at hi ⊢
  rw [← succ_pred j h0] at hj ⊢
  rw [← δ_factor_δ₂_le α hle hi hj, ← δ_factor_δ₂_ge α hle hi hj,
    ← FunctorToTypes.comp, ← FunctorToTypes.comp]
  exact X.condition ij ▸ rfl

lemma π_factor_δ {n : ℕ} (X : Multicofork (diagram n))
    {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 3)) (hi : ∀ x, asOrderHom α x ≠ i)
    (j : Fin (n + 3)) (hj : ∀ x, asOrderHom α x ≠ j) :
    (X.π i).app m (factor_δ α i) = (X.π j).app m (factor_δ α j) := by
  rcases lt_trichotomy i j with (h | rfl | h)
  · exact π_factor_δ_lt X α h hi hj
  · rfl
  · exact π_factor_δ_lt X α h hj hi |>.symm

/-- -/
noncomputable def isColimit (n : ℕ) : IsColimit (cocone n) := by
  refine Multicofork.IsColimit.mk (cocone n) ?_ ?_ ?_
  · intro X
    refine {
      app := fun m α ↦ X.π (skips α) |>.app m <| factor_δ α.1 (skips α),
      naturality := ?_ }
    intro a b f
    ext α
    dsimp only [Multicofork.ofπ_pt, types_comp_apply] at α ⊢
    rw [π_factor_δ X _ _ _ (skips α)]
    · rw [← types_comp_apply _ (X.pt.map f), ← NatTrans.naturality]
      rfl
    · intro k; apply skips_spec α
    · exact skips_spec <| ∂Δ[n + 2].map f α
  · intro X k
    ext m α
    dsimp only [diagram] at k α
    change (X.π _).app _ (factor_δ ((standardSimplex.map _).app _ _) _) = _
    rw [π_factor_δ X _ _ _ k]
    · rw [standardSimplex.factor_δ_δ_eq α]
    · intro j; exact Fin.succAbove_ne k _
    · exact skips_spec <| cocone n |>.π k |>.app m α
  · intro X f h
    ext m α
    simp only [Multicofork.ofπ_pt, ← h (skips α)]
    apply congr_arg (f.app m) ∘ Subtype.ext
    exact standardSimplex.factor_δ_spec _ _ (skips_spec α) |>.symm

end SSet.boundary
