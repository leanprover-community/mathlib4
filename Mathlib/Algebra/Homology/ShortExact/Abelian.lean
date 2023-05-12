/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang, Pierre-Alexandre Bazin

! This file was ported from Lean 3 source module algebra.homology.short_exact.abelian
! leanprover-community/mathlib commit 356447fe00e75e54777321045cdff7c9ea212e60
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.ShortExact.Preadditive
import Mathbin.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Short exact sequences in abelian categories

In an abelian category, a left-split or right-split short exact sequence admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}

variable [Abelian 𝒜]

open ZeroObject

theorem isIso_of_shortExact_of_isIso_of_isIso (h : ShortExact f g) (h' : ShortExact f' g')
    (i₁ : A ⟶ A') (i₂ : B ⟶ B') (i₃ : C ⟶ C') (comm₁ : i₁ ≫ f' = f ≫ i₂) (comm₂ : i₂ ≫ g' = g ≫ i₃)
    [IsIso i₁] [IsIso i₃] : IsIso i₂ := by
  obtain ⟨_⟩ := h
  obtain ⟨_⟩ := h'
  skip
  refine'
            @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso 𝒜 _ _ 0 _ _ _ 0 _ _ _ 0 f g 0 f'
              g' 0 i₁ i₂ i₃ _ comm₁ comm₂ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ <;>
          try simp <;>
        try apply exact_zero_left_of_mono <;>
      try assumption <;>
    rwa [← epi_iff_exact_zero_right]
#align category_theory.is_iso_of_short_exact_of_is_iso_of_is_iso CategoryTheory.isIso_of_shortExact_of_isIso_of_isIso

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk' (h : ShortExact f g) (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl)
    (h2 : i ≫ biprod.snd = g) : Splitting f g
    where
  Iso := by
    refine' @as_iso _ _ _ _ i (id _)
    refine'
      is_iso_of_short_exact_of_is_iso_of_is_iso h _ _ _ _ (h1.trans (category.id_comp _).symm).symm
        (h2.trans (category.comp_id _).symm)
    constructor
    apply exact_inl_snd
  comp_iso_eq_inl := by rwa [as_iso_hom]
  iso_comp_snd_eq := h2
#align category_theory.splitting.mk' CategoryTheory.Splitting.mk'

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : A ⊞ C ⟶ B` such that `p ≫ i = f` where `p` is the canonical map
`biprod.inl : A ⟶ A ⊞ C`, and `i ≫ g` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk'' (h : ShortExact f g) (i : A ⊞ C ⟶ B) (h1 : biprod.inl ≫ i = f)
    (h2 : i ≫ g = biprod.snd) : Splitting f g
    where
  Iso := by
    refine' (@as_iso _ _ _ _ i (id _)).symm
    refine'
      is_iso_of_short_exact_of_is_iso_of_is_iso _ h _ _ _ (h1.trans (category.id_comp _).symm).symm
        (h2.trans (category.comp_id _).symm)
    constructor
    apply exact_inl_snd
  comp_iso_eq_inl := by rw [iso.symm_hom, as_iso_inv, is_iso.comp_inv_eq, h1]
  iso_comp_snd_eq := by rw [iso.symm_hom, as_iso_inv, is_iso.inv_comp_eq, h2]
#align category_theory.splitting.mk'' CategoryTheory.Splitting.mk''

/-- A short exact sequence that is left split admits a splitting. -/
def LeftSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : Splitting f g :=
  Splitting.mk' h.ShortExact (biprod.lift h.LeftSplit.some g)
    (by
      ext
      · simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec
      · simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w])
    (by simp only [biprod.lift_snd])
#align category_theory.left_split.splitting CategoryTheory.LeftSplit.splitting

/-- A short exact sequence that is right split admits a splitting. -/
def RightSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : Splitting f g :=
  Splitting.mk'' h.ShortExact (biprod.desc f h.RightSplit.some) (biprod.inl_desc _ _)
    (by
      ext
      · rw [biprod.inl_snd, ← category.assoc, biprod.inl_desc, h.exact.w]
      · rw [biprod.inr_snd, ← category.assoc, biprod.inr_desc, h.right_split.some_spec])
#align category_theory.right_split.splitting CategoryTheory.RightSplit.splitting

end CategoryTheory

