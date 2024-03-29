/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Decomposition
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.CategoryTheory.Idempotents.KaroubiKaroubi

#align_import algebraic_topology.dold_kan.n_reflects_iso from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# N₁ and N₂ reflects isomorphisms

In this file, it is shown that the functors
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and
`N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ))`
reflect isomorphisms for any preadditive category `C`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents Opposite Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C]

open MorphComponents

instance : ReflectsIsomorphisms (N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun {X Y} f => by
    intro
    -- restating the result in a way that allows induction on the degree n
    suffices ∀ n : ℕ, IsIso (f.app (op [n])) by
      haveI : ∀ Δ : SimplexCategoryᵒᵖ, IsIso (f.app Δ) := fun Δ => this Δ.unop.len
      apply NatIso.isIso_of_isIso_app
    -- restating the assumption in a more practical form
    have h₁ := HomologicalComplex.congr_hom (Karoubi.hom_ext_iff.mp (IsIso.hom_inv_id (N₁.map f)))
    have h₂ := HomologicalComplex.congr_hom (Karoubi.hom_ext_iff.mp (IsIso.inv_hom_id (N₁.map f)))
    have h₃ := fun n =>
      Karoubi.HomologicalComplex.p_comm_f_assoc (inv (N₁.map f)) n (f.app (op [n]))
    simp only [N₁_map_f, Karoubi.comp_f, HomologicalComplex.comp_f,
      AlternatingFaceMapComplex.map_f, N₁_obj_p, Karoubi.id_eq, assoc] at h₁ h₂ h₃
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
    · haveI := hn
      use φ { a := PInfty.f (n + 1) ≫ (inv (N₁.map f)).f.f (n + 1)
              b := fun i => inv (f.app (op [n])) ≫ X.σ i }
      simp only [MorphComponents.id, ← id_φ, ← preComp_φ, preComp, ← postComp_φ, postComp,
        PInfty_f_naturality_assoc, IsIso.hom_inv_id_assoc, assoc, IsIso.inv_hom_id_assoc,
        SimplicialObject.σ_naturality, h₁, h₂, h₃, and_self]⟩

theorem compatibility_N₂_N₁_karoubi :
    N₂ ⋙ (karoubiChainComplexEquivalence C ℕ).functor =
      karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C ⋙
        N₁ ⋙ (karoubiChainComplexEquivalence (Karoubi C) ℕ).functor ⋙
            Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse _ := by
  refine' CategoryTheory.Functor.ext (fun P => _) fun P Q f => _
  · refine' HomologicalComplex.ext _ _
    · ext n
      · rfl
      · dsimp
        simp only [karoubi_PInfty_f, comp_id, PInfty_f_naturality, id_comp, eqToHom_refl]
    · rintro _ n (rfl : n + 1 = _)
      ext
      have h := (AlternatingFaceMapComplex.map P.p).comm (n + 1) n
      dsimp [N₂, karoubiChainComplexEquivalence,
        KaroubiHomologicalComplexEquivalence.Functor.obj] at h ⊢
      simp only [assoc, Karoubi.eqToHom_f, eqToHom_refl, comp_id,
        karoubi_alternatingFaceMapComplex_d, karoubi_PInfty_f,
        ← HomologicalComplex.Hom.comm_assoc, ← h, app_idem_assoc]
  · ext n
    dsimp [KaroubiKaroubi.inverse, Functor.mapHomologicalComplex]
    simp only [karoubi_PInfty_f, HomologicalComplex.eqToHom_f, Karoubi.eqToHom_f,
      assoc, comp_id, PInfty_f_naturality, app_p_comp,
      karoubiChainComplexEquivalence_functor_obj_X_p, N₂_obj_p_f, eqToHom_refl,
      PInfty_f_naturality_assoc, app_comp_p, PInfty_f_idem_assoc]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.compatibility_N₂_N₁_karoubi AlgebraicTopology.DoldKan.compatibility_N₂_N₁_karoubi

/-- We deduce that `N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms from the fact that
`N₁ : SimplicialObject (Karoubi C) ⥤ Karoubi (ChainComplex (Karoubi C) ℕ)` does. -/
instance : ReflectsIsomorphisms (N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun f => by
    intro
    -- The following functor `F` reflects isomorphism because it is
    -- a composition of four functors which reflects isomorphisms.
    -- Then, it suffices to show that `F.map f` is an isomorphism.
    let F₁ := karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C
    let F₂ : SimplicialObject (Karoubi C) ⥤ _ := N₁
    let F₃ := (karoubiChainComplexEquivalence (Karoubi C) ℕ).functor
    let F₄ := Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse
      (ComplexShape.down ℕ)
    let F := F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄
    -- Porting note: we have to help Lean4 find the `ReflectsIsomorphisms` instances
    -- could this be fixed by setting better instance priorities?
    haveI : ReflectsIsomorphisms F₁ := reflectsIsomorphisms_of_full_and_faithful _
    haveI : ReflectsIsomorphisms F₂ := by infer_instance
    haveI : ReflectsIsomorphisms F₃ := reflectsIsomorphisms_of_full_and_faithful _
    haveI : ReflectsIsomorphisms ((KaroubiKaroubi.equivalence C).inverse) :=
      reflectsIsomorphisms_of_full_and_faithful _
    have : IsIso (F.map f) := by
      simp only [F]
      rw [← compatibility_N₂_N₁_karoubi, Functor.comp_map]
      apply Functor.map_isIso
    exact isIso_of_reflects_iso f F⟩

end DoldKan

end AlgebraicTopology
