/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang, Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Homology.ShortExact.Preadditive
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

#align_import algebra.homology.short_exact.abelian from "leanprover-community/mathlib"@"356447fe00e75e54777321045cdff7c9ea212e60"

/-!
# Short exact sequences in abelian categories

In an abelian category, a left-split or right-split short exact sequence admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type*} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}

variable [Abelian 𝒜]

open ZeroObject

theorem isIso_of_shortExact_of_isIso_of_isIso (h : ShortExact f g) (h' : ShortExact f' g')
    (i₁ : A ⟶ A') (i₂ : B ⟶ B') (i₃ : C ⟶ C')
    (comm₁ : i₁ ≫ f' = f ≫ i₂ := by aesop_cat)
    (comm₂ : i₂ ≫ g' = g ≫ i₃ := by aesop_cat) [IsIso i₁] [IsIso i₃] : IsIso i₂ := by
  obtain ⟨_⟩ := h
  obtain ⟨_⟩ := h'
  refine @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono 𝒜 _ _ 0 _ _ _ 0 _ _ _ 0 f g 0 f' g'
      0 i₁ i₂ i₃ ?_ comm₁ comm₂ 0 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ _ _
  all_goals try simp
  all_goals try assumption
  all_goals try apply exact_zero_left_of_mono
  all_goals rwa [← epi_iff_exact_zero_right ]
#align category_theory.is_iso_of_short_exact_of_is_iso_of_is_iso CategoryTheory.isIso_of_shortExact_of_isIso_of_isIso

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk' (h : ShortExact f g) (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl)
    (h2 : i ≫ biprod.snd = g) : Splitting f g :=
  have : IsIso i := isIso_of_shortExact_of_isIso_of_isIso h ⟨exact_inl_snd A C⟩ (𝟙 _) i (𝟙 _)
  { iso := asIso i
    comp_iso_eq_inl := h1
    iso_comp_snd_eq := h2 }
#align category_theory.splitting.mk' CategoryTheory.Splitting.mk'

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : A ⊞ C ⟶ B` such that `p ≫ i = f` where `p` is the canonical map
`biprod.inl : A ⟶ A ⊞ C`, and `i ≫ g` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk'' (h : ShortExact f g) (i : A ⊞ C ⟶ B) (h1 : biprod.inl ≫ i = f)
    (h2 : i ≫ g = biprod.snd) : Splitting f g :=
  have : IsIso i := isIso_of_shortExact_of_isIso_of_isIso ⟨exact_inl_snd A C⟩ h (𝟙 _) i (𝟙 _)
  { iso := (asIso i).symm
    comp_iso_eq_inl := by rw [Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, h1]
    iso_comp_snd_eq := by rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, h2] }
#align category_theory.splitting.mk'' CategoryTheory.Splitting.mk''

/-- A short exact sequence that is left split admits a splitting. -/
def LeftSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : Splitting f g :=
  Splitting.mk' h.shortExact (biprod.lift h.left_split.choose g)
    (by
      ext
      · simpa only [biprod.inl_fst, biprod.lift_fst, Category.assoc] using h.left_split.choose_spec
      · simp only [biprod.inl_snd, biprod.lift_snd, Category.assoc, h.exact.w])
    (by simp only [biprod.lift_snd])
#align category_theory.left_split.splitting CategoryTheory.LeftSplit.splitting

/-- A short exact sequence that is right split admits a splitting. -/
def RightSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : Splitting f g :=
  Splitting.mk'' h.shortExact (biprod.desc f h.right_split.choose) (biprod.inl_desc _ _)
    (by
      ext
      · rw [biprod.inl_snd, ← Category.assoc, biprod.inl_desc, h.exact.w]
      · rw [biprod.inr_snd, ← Category.assoc, biprod.inr_desc, h.right_split.choose_spec])
#align category_theory.right_split.splitting CategoryTheory.RightSplit.splitting

end CategoryTheory
