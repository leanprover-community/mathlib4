/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.n_reflects_iso
! leanprover-community/mathlib commit 88bca0ce5d22ebfd9e73e682e51d60ea13b48347
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN
import Mathbin.AlgebraicTopology.DoldKan.Decomposition
import Mathbin.CategoryTheory.Idempotents.HomologicalComplex
import Mathbin.CategoryTheory.Idempotents.KaroubiKaroubi

/-!

# N₁ and N₂ reflects isomorphisms

In this file, it is shown that the functors
`N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)` and
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ))`
reflect isomorphisms for any preadditive category `C`.

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents

open Opposite

open Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

open MorphComponents

instance : ReflectsIsomorphisms (n₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun X Y f => by
    intro
    -- restating the result in a way that allows induction on the degree n
    suffices ∀ n : ℕ, is_iso (f.app (op [n]))
      by
      haveI : ∀ Δ : SimplexCategoryᵒᵖ, is_iso (f.app Δ) := fun Δ => this Δ.unop.len
      apply nat_iso.is_iso_of_is_iso_app
    -- restating the assumption in a more practical form
    have h₁ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N₁.map f)))
    have h₂ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N₁.map f)))
    have h₃ := fun n =>
      karoubi.homological_complex.p_comm_f_assoc (inv (N₁.map f)) n (f.app (op [n]))
    simp only [N₁_map_f, karoubi.comp_f, HomologicalComplex.comp_f,
      alternating_face_map_complex.map_f, N₁_obj_p, karoubi.id_eq, assoc] at h₁ h₂ h₃
    -- we have to construct an inverse to f in degree n, by induction on n
    intro n
    induction' n with n hn
    -- degree 0
    · use (inv (N₁.map f)).f.f 0
      have h₁₀ := h₁ 0
      have h₂₀ := h₂ 0
      dsimp at h₁₀ h₂₀
      simp only [id_comp, comp_id] at h₁₀ h₂₀
      tauto
    -- induction step
    · haveI := hn
      use φ {
            a := P_infty.f (n + 1) ≫ (inv (N₁.map f)).f.f (n + 1)
            b := fun i => inv (f.app (op [n])) ≫ X.σ i }
      simp only [morph_components.id, ← id_φ, ← pre_comp_φ, pre_comp, ← post_comp_φ, post_comp,
        P_infty_f_naturality_assoc, is_iso.hom_inv_id_assoc, assoc, is_iso.inv_hom_id_assoc,
        simplicial_object.σ_naturality, h₁, h₂, h₃]
      tauto⟩

theorem compatibility_n₂_n₁_karoubi :
    n₂ ⋙ (karoubiChainComplexEquivalence C ℕ).Functor =
      karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C ⋙
        n₁ ⋙
          (karoubiChainComplexEquivalence (Karoubi C) ℕ).Functor ⋙
            Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse _ :=
  by
  refine' CategoryTheory.Functor.ext (fun P => _) fun P Q f => _
  · refine' HomologicalComplex.ext _ _
    · ext n
      · dsimp
        simp only [karoubi_P_infty_f, comp_id, P_infty_f_naturality, id_comp]
      · rfl
    · rintro _ n (rfl : n + 1 = _)
      ext
      have h := (alternating_face_map_complex.map P.p).comm (n + 1) n
      dsimp [N₂, karoubi_chain_complex_equivalence, karoubi_karoubi.inverse,
        karoubi_homological_complex_equivalence.functor.obj] at h⊢
      simp only [karoubi.comp_f, assoc, karoubi.eq_to_hom_f, eq_to_hom_refl, id_comp, comp_id,
        karoubi_alternating_face_map_complex_d, karoubi_P_infty_f, ←
        HomologicalComplex.Hom.comm_assoc, ← h, app_idem_assoc]
  · ext n
    dsimp [karoubi_karoubi.inverse, karoubi_functor_category_embedding,
      karoubi_functor_category_embedding.map]
    simp only [karoubi.comp_f, karoubi_P_infty_f, HomologicalComplex.eqToHom_f, karoubi.eq_to_hom_f,
      assoc, comp_id, P_infty_f_naturality, app_p_comp,
      karoubi_chain_complex_equivalence_functor_obj_X_p, N₂_obj_p_f, eq_to_hom_refl,
      P_infty_f_naturality_assoc, app_comp_p, P_infty_f_idem_assoc]
#align algebraic_topology.dold_kan.compatibility_N₂_N₁_karoubi AlgebraicTopology.DoldKan.compatibility_n₂_n₁_karoubi

/-- We deduce that `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms from the fact that
`N₁ : simplicial_object (karoubi C) ⥤ karoubi (chain_complex (karoubi C) ℕ)` does. -/
instance : ReflectsIsomorphisms (n₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun X Y f => by
    intro
    -- The following functor `F` reflects isomorphism because it is
    -- a composition of four functors which reflects isomorphisms.
    -- Then, it suffices to show that `F.map f` is an isomorphism.
    let F :=
      karoubi_functor_category_embedding SimplexCategoryᵒᵖ C ⋙
        N₁ ⋙
          (karoubi_chain_complex_equivalence (karoubi C) ℕ).Functor ⋙
            functor.map_homological_complex (karoubi_karoubi.equivalence C).inverse
              (ComplexShape.down ℕ)
    have : is_iso (F.map f) := by
      dsimp only [F]
      rw [← compatibility_N₂_N₁_karoubi, functor.comp_map]
      apply functor.map_is_iso
    exact is_iso_of_reflects_iso f F⟩

end DoldKan

end AlgebraicTopology

