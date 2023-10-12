/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import algebra.homology.short_exact.preadditive from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Short exact sequences, and splittings.

`CategoryTheory.ShortExact f g` is the proposition that `0 ⟶ A -f⟶ B -g⟶ C ⟶ 0` is an exact
sequence.

We define when a short exact sequence is left-split, right-split, and split.

## See also

In `Mathlib.Algebra.Homology.ShortExact.Abelian` we show that in an abelian category a left-split
short exact sequences admits a splitting.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type*} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasKernels 𝒜] [HasImages 𝒜]

/-- If `f : A ⟶ B` and `g : B ⟶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is an exact sequence. -/
structure ShortExact : Prop where
  [mono : Mono f]
  [epi : Epi g]
  exact : Exact f g
#align category_theory.short_exact CategoryTheory.ShortExact

/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure LeftSplit : Prop where
  left_split : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A
  [epi : Epi g]
  exact : Exact f g
#align category_theory.left_split CategoryTheory.LeftSplit

theorem LeftSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : ShortExact f g where
  mono := let ⟨_φ, hφ⟩ := h.left_split; mono_of_mono_fac hφ
  __ := h
#align category_theory.left_split.short_exact CategoryTheory.LeftSplit.shortExact

/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure RightSplit : Prop where
  right_split : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C
  [mono : Mono f]
  exact : Exact f g
#align category_theory.right_split CategoryTheory.RightSplit

theorem RightSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : ShortExact f g where
  epi := let ⟨_χ, hχ⟩ := h.right_split; epi_of_epi_fac hχ
  __ := h
#align category_theory.right_split.short_exact CategoryTheory.RightSplit.shortExact

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜]

/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure Split : Prop where
  split : ∃ (φ : B ⟶ A) (χ : C ⟶ B),
    f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B
#align category_theory.split CategoryTheory.Split

variable [HasKernels 𝒜] [HasImages 𝒜]

theorem exact_of_split {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {χ : C ⟶ B} {φ : B ⟶ A} (hfg : f ≫ g = 0)
    (H : φ ≫ f + g ≫ χ = 𝟙 B) : Exact f g where
  w := hfg
  epi := by
    set ψ : (kernelSubobject g : 𝒜) ⟶ imageSubobject f :=
      Subobject.arrow _ ≫ φ ≫ factorThruImageSubobject f
    suffices : ψ ≫ imageToKernel f g hfg = 𝟙 _
    · exact epi_of_epi_fac this
    rw [← cancel_mono (Subobject.arrow _)]
    simp only [imageToKernel_arrow, imageSubobject_arrow_comp, Category.id_comp, Category.assoc]
    calc
      (kernelSubobject g).arrow ≫ φ ≫ f = (kernelSubobject g).arrow ≫ 𝟙 B := by
        rw [← H, Preadditive.comp_add]
        simp only [add_zero, zero_comp, kernelSubobject_arrow_comp_assoc]
      _ = (kernelSubobject g).arrow := Category.comp_id _
#align category_theory.exact_of_split CategoryTheory.exact_of_split

section

variable {f g}

theorem Split.exact (h : Split f g) : Exact f g := by
  obtain ⟨φ, χ, -, -, h1, -, h2⟩ := h
  exact exact_of_split h1 h2
#align category_theory.split.exact CategoryTheory.Split.exact

theorem Split.leftSplit (h : Split f g) : LeftSplit f g where
  left_split := let ⟨φ, _χ, h1, _⟩ := h; ⟨φ, h1⟩
  epi := let ⟨_φ, _χ, _, h2, _⟩ := h; epi_of_epi_fac h2
  exact := h.exact
#align category_theory.split.left_split CategoryTheory.Split.leftSplit

theorem Split.rightSplit (h : Split f g) : RightSplit f g where
  right_split := let ⟨_φ, χ, _, h1, _⟩ := h; ⟨χ, h1⟩
  mono := let ⟨_φ, _χ, h1, _⟩ := h; mono_of_mono_fac h1
  exact := h.exact
#align category_theory.split.right_split CategoryTheory.Split.rightSplit

theorem Split.shortExact (h : Split f g) : ShortExact f g :=
  h.leftSplit.shortExact
#align category_theory.split.short_exact CategoryTheory.Split.shortExact

end

theorem Split.map {𝒜 ℬ : Type*} [Category 𝒜] [Preadditive 𝒜] [Category ℬ] [Preadditive ℬ]
    (F : 𝒜 ⥤ ℬ) [Functor.Additive F] {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} (h : Split f g) :
    Split (F.map f) (F.map g) := by
  obtain ⟨φ, χ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨F.map φ, F.map χ, ?_⟩⟩
  simp only [← F.map_comp, ← F.map_id]
  rw [← F.map_add] -- porting note: `simp only` fails to use this lemma
  simp only [F.map_zero, *, true_and]
#align category_theory.split.map CategoryTheory.Split.map

/-- The sequence `A ⟶ A ⊞ B ⟶ B` is exact. -/
theorem exact_inl_snd [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
  exact_of_split biprod.inl_snd biprod.total
#align category_theory.exact_inl_snd CategoryTheory.exact_inl_snd

/-- The sequence `B ⟶ A ⊞ B ⟶ A` is exact. -/
theorem exact_inr_fst [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inr : B ⟶ A ⊞ B) biprod.fst :=
  exact_of_split biprod.inr_fst ((add_comm _ _).trans biprod.total)
#align category_theory.exact_inr_fst CategoryTheory.exact_inr_fst

end Preadditive

/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊞ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
-- porting note: was @[nolint has_nonempty_instance]
structure Splitting [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜] where
  iso : B ≅ A ⊞ C
  comp_iso_eq_inl : f ≫ iso.hom = biprod.inl
  iso_comp_snd_eq : iso.hom ≫ biprod.snd = g
#align category_theory.splitting CategoryTheory.Splitting

variable {f g}

namespace Splitting

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜]

attribute [reassoc (attr := simp)] comp_iso_eq_inl iso_comp_snd_eq

variable (h : Splitting f g)

@[reassoc (attr := simp)]
theorem inl_comp_iso_eq : biprod.inl ≫ h.iso.inv = f := by rw [Iso.comp_inv_eq, h.comp_iso_eq_inl]
#align category_theory.splitting.inl_comp_iso_eq CategoryTheory.Splitting.inl_comp_iso_eq

@[reassoc (attr := simp)]
theorem iso_comp_eq_snd : h.iso.inv ≫ g = biprod.snd := by rw [Iso.inv_comp_eq, h.iso_comp_snd_eq]
#align category_theory.splitting.iso_comp_eq_snd CategoryTheory.Splitting.iso_comp_eq_snd

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.section : C ⟶ B` is the morphism satisfying `h.section ≫ g = 𝟙 C`. -/
def «section» : C ⟶ B := biprod.inr ≫ h.iso.inv
#align category_theory.splitting.section CategoryTheory.Splitting.section

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.retraction : B ⟶ A` is the morphism satisfying `f ≫ h.retraction = 𝟙 A`. -/
def retraction : B ⟶ A := h.iso.hom ≫ biprod.fst
#align category_theory.splitting.retraction CategoryTheory.Splitting.retraction

@[reassoc (attr := simp)]
theorem section_π : h.section ≫ g = 𝟙 C := by simp [Splitting.section]
#align category_theory.splitting.section_π CategoryTheory.Splitting.section_π

@[reassoc (attr := simp)]
theorem ι_retraction : f ≫ h.retraction = 𝟙 A := by simp [retraction]
#align category_theory.splitting.ι_retraction CategoryTheory.Splitting.ι_retraction

@[reassoc (attr := simp)]
theorem section_retraction : h.section ≫ h.retraction = 0 := by
  delta Splitting.section retraction
  simp
#align category_theory.splitting.section_retraction CategoryTheory.Splitting.section_retraction

/-- The retraction in a splitting is a split mono. -/
protected def splitMono : SplitMono f :=
  ⟨h.retraction, by simp⟩
#align category_theory.splitting.split_mono CategoryTheory.Splitting.splitMono

/-- The section in a splitting is a split epi. -/
protected def splitEpi : SplitEpi g :=
  ⟨h.section, by simp⟩
#align category_theory.splitting.split_epi CategoryTheory.Splitting.splitEpi

@[reassoc (attr := simp)]
theorem inr_iso_inv : biprod.inr ≫ h.iso.inv = h.section :=
  rfl
#align category_theory.splitting.inr_iso_inv CategoryTheory.Splitting.inr_iso_inv

@[reassoc (attr := simp)]
theorem iso_hom_fst : h.iso.hom ≫ biprod.fst = h.retraction :=
  rfl
#align category_theory.splitting.iso_hom_fst CategoryTheory.Splitting.iso_hom_fst

/-- A short exact sequence of the form `X -f⟶ Y -0⟶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splittingOfIsIsoZero {X Y Z : 𝒜} (f : X ⟶ Y) [IsIso f] (hZ : IsZero Z) :
    Splitting f (0 : Y ⟶ Z) :=
  ⟨(asIso f).symm ≪≫ isoBiprodZero hZ, by simp [hZ.eq_of_tgt _ 0], by simp⟩
#align category_theory.splitting.splitting_of_is_iso_zero CategoryTheory.Splitting.splittingOfIsIsoZero

protected theorem mono : Mono f := mono_of_mono_fac h.ι_retraction
#align category_theory.splitting.mono CategoryTheory.Splitting.mono

protected theorem epi : Epi g := epi_of_epi_fac h.section_π
#align category_theory.splitting.epi CategoryTheory.Splitting.epi

instance : Mono h.section := by
  delta Splitting.section
  infer_instance

instance : Epi h.retraction := by
  delta retraction
  apply epi_comp

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

variable (h : Splitting f g)

theorem split_add : h.retraction ≫ f + g ≫ h.section = 𝟙 _ := by
  delta Splitting.section retraction
  rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv]
  simp only [Category.comp_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Limits.biprod.total, Preadditive.comp_add, Preadditive.add_comp,
    Splitting.comp_iso_eq_inl, Splitting.iso_comp_eq_snd_assoc]
#align category_theory.splitting.split_add CategoryTheory.Splitting.split_add

@[reassoc]
theorem retraction_ι_eq_id_sub : h.retraction ≫ f = 𝟙 _ - g ≫ h.section :=
  eq_sub_iff_add_eq.mpr h.split_add
#align category_theory.splitting.retraction_ι_eq_id_sub CategoryTheory.Splitting.retraction_ι_eq_id_sub

@[reassoc]
theorem π_section_eq_id_sub : g ≫ h.section = 𝟙 _ - h.retraction ≫ f :=
  eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.split_add)
#align category_theory.splitting.π_section_eq_id_sub CategoryTheory.Splitting.π_section_eq_id_sub

theorem splittings_comm (h h' : Splitting f g) :
    h'.section ≫ h.retraction = -h.section ≫ h'.retraction := by
  haveI := h.mono
  rw [← cancel_mono f]
  simp [retraction_ι_eq_id_sub]
#align category_theory.splitting.splittings_comm CategoryTheory.Splitting.splittings_comm

theorem split : Split f g :=
  ⟨⟨h.retraction, h.section, h.ι_retraction, h.section_π, by
    rw [← h.inl_comp_iso_eq, Category.assoc, h.iso_comp_eq_snd, biprod.inl_snd],
    h.section_retraction, h.split_add⟩⟩
#align category_theory.splitting.split CategoryTheory.Splitting.split

@[reassoc]
theorem comp_eq_zero : f ≫ g = 0 :=
  h.split.1.choose_spec.choose_spec.2.2.1
#align category_theory.splitting.comp_eq_zero CategoryTheory.Splitting.comp_eq_zero

variable [HasKernels 𝒜] [HasImages 𝒜] [HasZeroObject 𝒜] [HasCokernels 𝒜]

protected theorem exact : Exact f g := by
  rw [exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _]
  · exact exact_inl_snd _ _
  · refine Arrow.isoMk (Iso.refl _) h.iso ?_
    simp only [Iso.refl_hom, Arrow.mk_hom, Category.id_comp, comp_iso_eq_inl]
    rfl
  · refine Arrow.isoMk h.iso (Iso.refl _) ?_
    dsimp
    simp
  · rfl
#align category_theory.splitting.exact CategoryTheory.Splitting.exact

protected theorem shortExact : ShortExact f g where
  mono := h.mono
  epi := h.epi
  exact := h.exact
#align category_theory.splitting.short_exact CategoryTheory.Splitting.shortExact

end Preadditive

end Splitting

end CategoryTheory
