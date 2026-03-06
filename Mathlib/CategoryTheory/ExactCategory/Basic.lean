/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact categorires

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

namespace IsPullback

variable {C : Type _} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

lemma of_hasBinaryBiproduct_fst_snd (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] :
    IsPullback biprod.fst biprod.snd (0 : X₁ ⟶ 0) (0 : X₂ ⟶ 0) where
  w := by simp
  isLimit' :=
    ⟨{  lift := fun s => biprod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)
        fac := fun s => by rintro (_|_|_) <;> aesop_cat
        uniq := fun s m hm => by
          apply biprod.hom_ext
          · simpa using hm WalkingCospan.left
          · simpa using hm WalkingCospan.right }⟩

end IsPullback

variable (C : Type*) [Category* C] [Preadditive C]

namespace ShortComplex

variable {C}
variable (S : ObjectProperty (ShortComplex C))

def fAdmissible : MorphismProperty C := fun _ Y f =>
  ∃ (Z : C) (g : Y ⟶ Z) (zero : f ≫ g = 0), S (ShortComplex.mk f g zero)

lemma fAdmissible_respectsIso [S.IsClosedUnderIsomorphisms] : (fAdmissible S).RespectsIso where
  precomp := by
    rintro X X' Y e he f ⟨Z, g, zero, mem⟩
    have : IsIso e := he
    refine ⟨Z, g, by rw [assoc, zero, comp_zero], S.prop_of_iso ?_ mem⟩
    exact ShortComplex.isoMk (asIso e).symm (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat)
  postcomp := by
    rintro X Y Y' e he f ⟨Z, g, zero, mem⟩
    have : IsIso e := he
    refine ⟨Z, inv e ≫ g, by rw [assoc, IsIso.hom_inv_id_assoc, zero], S.prop_of_iso ?_ mem⟩
    exact ShortComplex.isoMk (Iso.refl _) (asIso e) (Iso.refl _) (by aesop_cat) (by aesop_cat)

def gAdmissible : MorphismProperty C := fun Y _ g =>
  ∃ (X : C) (f : X ⟶ Y) (zero : f ≫ g = 0), S (ShortComplex.mk f g zero)

lemma gAdmissible_respectsIso [S.IsClosedUnderIsomorphisms] : (gAdmissible S).RespectsIso where
  precomp := by
    rintro Y Y' Z e he g ⟨X, f, zero, mem⟩
    have : IsIso e := he
    refine ⟨X, f ≫ inv e, by rw [assoc, IsIso.inv_hom_id_assoc, zero], S.prop_of_iso ?_ mem⟩
    exact ShortComplex.isoMk (Iso.refl _) (asIso e).symm (Iso.refl _) (by aesop_cat) (by aesop_cat)
  postcomp := by
    rintro Y Z Z' e he g ⟨X, f, zero, mem⟩
    have : IsIso e := he
    refine ⟨X, f, by rw [reassoc_of% zero, zero_comp], S.prop_of_iso ?_ mem⟩
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso e) (by aesop_cat) (by aesop_cat)

end ShortComplex

-- this should be refactored as a property of some `ObjectProperty`
-- see _Exact Categories_, Theo Bühler, Expo. Math 28 (2010), 1-69
class ExactCategory [HasZeroObject C] [HasBinaryBiproducts C] where
  shortExact' : ObjectProperty (ShortComplex C)
  respectsIso_shortExact' : shortExact'.IsClosedUnderIsomorphisms
  shortExact_kernel' :
    ∀ S (_ : shortExact' S), Nonempty (IsLimit (KernelFork.ofι _ S.zero))
  shortExact_cokernel' :
    ∀ S (_ : shortExact' S), Nonempty (IsColimit (CokernelCofork.ofπ _ S.zero))
  isMultiplicative_admissibleMono :
    (ShortComplex.fAdmissible shortExact').IsMultiplicative
  isMultiplicative_admissibleEpi:
    (ShortComplex.gAdmissible shortExact').IsMultiplicative
  admissibleMono_coquarrable :
    ShortComplex.fAdmissible shortExact' ≤ MorphismProperty.coquarrable C
  admissibleEpi_quarrable :
    ShortComplex.gAdmissible shortExact' ≤ MorphismProperty.quarrable C
  admissibleMono_stableUnderCobaseChange :
    (ShortComplex.fAdmissible shortExact').IsStableUnderCobaseChange
  admissibleEpi_stableUnderBaseChange :
    (ShortComplex.gAdmissible shortExact').IsStableUnderBaseChange

variable [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  {X Y Z X' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace ExactCategory

def shortExact : ObjectProperty (ShortComplex C) := ExactCategory.shortExact'

instance : (ShortComplex.fAdmissible (shortExact C)).IsMultiplicative :=
  isMultiplicative_admissibleMono

instance : (ShortComplex.gAdmissible (shortExact C)).IsMultiplicative :=
  isMultiplicative_admissibleEpi

instance : (ShortComplex.fAdmissible (shortExact C)).IsStableUnderCobaseChange :=
  admissibleMono_stableUnderCobaseChange

instance : (ShortComplex.gAdmissible (shortExact C)).IsStableUnderBaseChange :=
  admissibleEpi_stableUnderBaseChange

end ExactCategory

open ExactCategory

instance respectsIso_shortExact : (shortExact C).IsClosedUnderIsomorphisms  :=
  respectsIso_shortExact'

variable {C}

noncomputable def isLimit_kernelFork_of_shortExact (S : ShortComplex C) (hS : shortExact C S) :
    IsLimit (KernelFork.ofι _ S.zero) :=
  (shortExact_kernel' _ hS).some

noncomputable def isColimit_cokernelCofork_of_shortExact
    (S : ShortComplex C) (hS : shortExact C S) :
    IsColimit (CokernelCofork.ofπ _ S.zero) :=
  (shortExact_cokernel' _ hS).some

class AdmissibleMono : Prop where
  mem' : (ShortComplex.fAdmissible (shortExact C)) f

lemma AdmissibleMono.mem [AdmissibleMono f] : (ShortComplex.fAdmissible (shortExact C)) f :=
  AdmissibleMono.mem'

class AdmissibleEpi : Prop where
  mem' : (ShortComplex.gAdmissible (shortExact C)) g

lemma AdmissibleEpi.mem [AdmissibleEpi f] : (ShortComplex.gAdmissible (shortExact C)) f :=
  AdmissibleEpi.mem'

namespace ExactCategory

instance [AdmissibleMono f] [AdmissibleMono g] : AdmissibleMono (f ≫ g) :=
  ⟨MorphismProperty.comp_mem _ _ _ (AdmissibleMono.mem f) (AdmissibleMono.mem g)⟩

instance [AdmissibleEpi f] [AdmissibleEpi g] : AdmissibleEpi (f ≫ g) :=
  ⟨MorphismProperty.comp_mem _ _ _ (AdmissibleEpi.mem f) (AdmissibleEpi.mem g)⟩

instance [AdmissibleMono f] : Mono f := by
  obtain ⟨Z, g, zero, mem⟩ := AdmissibleMono.mem f
  exact mono_of_isLimit_fork (isLimit_kernelFork_of_shortExact _ mem)

instance [AdmissibleEpi g] : Epi g := by
  obtain ⟨Z, f, zero, mem⟩ := AdmissibleEpi.mem g
  exact epi_of_isColimit_cofork (isColimit_cokernelCofork_of_shortExact _ mem)

instance [hg : IsIso g] : AdmissibleEpi g where
  mem' := by
    refine (MorphismProperty.arrow_mk_iso_iff
      (ShortComplex.gAdmissible (shortExact C)) ?_).1 (MorphismProperty.id_mem _ Y)
    exact Arrow.isoMk (Iso.refl _) (asIso g) (by aesop_cat)

instance [hg : IsIso f] : AdmissibleMono f where
  mem' := by
    refine (MorphismProperty.arrow_mk_iso_iff
      (ShortComplex.fAdmissible (shortExact C)) ?_).1 (MorphismProperty.id_mem _ X)
    exact Arrow.isoMk (Iso.refl _) (asIso f) (by aesop_cat)

instance [AdmissibleEpi g] (f : Z' ⟶ Z) : HasPullback g f :=
  MorphismProperty.quarrable.hasPullback g (admissibleEpi_quarrable g (AdmissibleEpi.mem g)) f

instance [AdmissibleEpi g] (f : Z' ⟶ Z) : HasPullback f g :=
  MorphismProperty.quarrable.hasPullback' g (admissibleEpi_quarrable g (AdmissibleEpi.mem g)) f

instance [AdmissibleEpi g] (f : Z' ⟶ Z) : AdmissibleEpi (pullback.snd g f) where
  mem' :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g f) (AdmissibleEpi.mem g)

instance [AdmissibleEpi g] (f : Z' ⟶ Z) : AdmissibleEpi (pullback.fst f g) where
  mem' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip (AdmissibleEpi.mem g)

instance [AdmissibleMono f] (g : X ⟶ X') : HasPushout f g :=
  MorphismProperty.coquarrable.hasPushout f (admissibleMono_coquarrable f (AdmissibleMono.mem f)) g

instance [AdmissibleMono f] (g : X ⟶ X') : HasPushout g f :=
  MorphismProperty.coquarrable.hasPushout' f (admissibleMono_coquarrable f (AdmissibleMono.mem f)) g

instance [AdmissibleMono f] (g : X ⟶ X') : AdmissibleMono (pushout.inl g f) where
  mem' := MorphismProperty.of_isPushout (IsPushout.of_hasPushout g f) (AdmissibleMono.mem f)

instance [AdmissibleMono f] (g : X ⟶ X') : AdmissibleMono (pushout.inr f g) where
  mem' := MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip (AdmissibleMono.mem f)

lemma shortExact_of_admissibleMono_of_isColimit (S : ShortComplex C)
    (hf : AdmissibleMono S.f) (hS : IsColimit (CokernelCofork.ofπ _ S.zero)) :
    shortExact C S := by
  obtain ⟨X₃', g', zero, mem⟩ := hf.mem
  refine ObjectProperty.prop_of_iso _ ?_ mem
  have hg' := isColimit_cokernelCofork_of_shortExact _ mem
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso hg' hS) (by aesop_cat) ?_
  have eq := IsColimit.comp_coconePointUniqueUpToIso_hom hg' hS WalkingParallelPair.one
  dsimp at eq ⊢
  rw [eq, id_comp]

lemma shortExact_of_admissibleEpi_of_isLimit (S : ShortComplex C)
    (hg : AdmissibleEpi S.g) (hS : IsLimit (KernelFork.ofι _ S.zero)) :
    shortExact C S := by
  obtain ⟨X₁', f', zero, mem⟩ := hg.mem
  refine ObjectProperty.prop_of_iso _ ?_ mem
  have hf' := isLimit_kernelFork_of_shortExact _ mem
  refine ShortComplex.isoMk (IsLimit.conePointUniqueUpToIso hf' hS) (Iso.refl _) (Iso.refl _)
    ?_ (by aesop_cat)
  have eq := IsLimit.conePointUniqueUpToIso_hom_comp hf' hS WalkingParallelPair.zero
  dsimp at eq ⊢
  rw [eq, comp_id]

instance (X : C) : AdmissibleEpi (0 : X ⟶ 0) := by
  obtain ⟨Z, g, zero, mem'⟩ := AdmissibleMono.mem (𝟙 X)
  have : AdmissibleEpi g := ⟨_, _, _, mem'⟩
  have hZ : IsZero Z := by
    rw [IsZero.iff_id_eq_zero, ← cancel_epi g]
    simpa only [comp_id, comp_zero, id_comp] using zero
  rw [(isZero_zero C).eq_of_tgt 0 (g ≫ hZ.isoZero.hom)]
  infer_instance

instance (X : C) : AdmissibleMono (0 : 0 ⟶ X) := by
  obtain ⟨Z, f, zero, mem'⟩ := AdmissibleEpi.mem (𝟙 X)
  have : AdmissibleMono f := ⟨_, _, _, mem'⟩
  have hZ : IsZero Z := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono f]
    simpa only [comp_id, zero_comp, id_comp] using zero
  rw [(isZero_zero C).eq_of_src 0 (hZ.isoZero.inv ≫ f)]
  infer_instance

instance (X₁ X₂ : C) : AdmissibleEpi (biprod.snd : X₁ ⊞ X₂ ⟶ X₂) where
  mem' :=
    MorphismProperty.of_isPullback
    (IsPullback.of_hasBinaryBiproduct_fst_snd X₁ X₂) (AdmissibleEpi.mem _)

instance (X₁ X₂ : C) : AdmissibleEpi (biprod.fst : X₁ ⊞ X₂ ⟶ X₁) := by
  have eq : (biprod.fst : X₁ ⊞ X₂ ⟶ X₁) = (biprod.braiding X₁ X₂).hom ≫ biprod.snd := by aesop_cat
  rw [eq]
  infer_instance

lemma binaryBiproduct_shortExact (X₁ X₂ : C) :
    shortExact C (ShortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) := by
  apply shortExact_of_admissibleEpi_of_isLimit
  · dsimp
    infer_instance
  · exact(ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).fIsKernel

instance (X₁ X₂ : C) : AdmissibleMono (biprod.inl : _ ⟶ X₁ ⊞ X₂) where
  mem' := ⟨_, _, _, binaryBiproduct_shortExact X₁ X₂⟩

instance (X₁ X₂ : C) : AdmissibleMono (biprod.inr : _ ⟶ X₁ ⊞ X₂) := by
  rw [show biprod.inr = biprod.inl ≫ (biprod.braiding X₁ X₂).inv by aesop_cat]
  infer_instance

instance {Y' : C} (f : X ⟶ Y) (g : Y' ⟶ Y) [hf : AdmissibleMono f] [AdmissibleEpi g] :
    AdmissibleMono (pullback.snd f g) := by
  have hf' := hf
  obtain ⟨Z, p, hp, mem⟩ := hf'
  have hf'' : IsLimit (KernelFork.ofι f hp) := isLimit_kernelFork_of_shortExact _ mem
  have : AdmissibleEpi p := ⟨_, _, _, mem⟩
  let S := ShortComplex.mk (pullback.snd f g) (g ≫ p) (by
    rw [← pullback.condition_assoc, hp, comp_zero])
  have hS : shortExact C S := by
    apply shortExact_of_admissibleEpi_of_isLimit
    · dsimp
      infer_instance
    · exact KernelFork.IsLimit.ofι _ _
        (fun a ha => pullback.lift (KernelFork.IsLimit.lift' hf'' (a ≫ g)
          (by rw [assoc, ha])).1 a (by exact (KernelFork.IsLimit.lift' _ _ _).2))
        (fun a ha => by dsimp; simp [S])
        (fun a ha b hb => by
          apply pullback.hom_ext
          · dsimp
            rw [← cancel_mono f, assoc, pullback.condition, reassoc_of% hb]
            simpa using (KernelFork.IsLimit.lift' hf'' (a ≫ g) (by rw [assoc, ha])).2.symm
          · simp [hb, S])
  exact ⟨_, _, _, hS⟩

lemma shortExact_of_isZero_of_isIso (S : ShortComplex C) (h₁ : IsZero S.X₁) (_ : IsIso S.g) :
    shortExact C S :=
  shortExact_of_admissibleEpi_of_isLimit S inferInstance
    (KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance h₁)

lemma shortExact_of_isIso_of_isZero (S : ShortComplex C) (h₃ : IsZero S.X₃) (_ : IsIso S.f) :
    shortExact C S :=
  shortExact_of_admissibleMono_of_isColimit S inferInstance
    (CokernelCofork.IsColimit.ofEpiOfIsZero _ inferInstance h₃)

lemma shortExact_of_isZero (S : ShortComplex C)
    (h₁ : IsZero S.X₁) (h₂ : IsZero S.X₂) (h₃ : IsZero S.X₃) : shortExact C S :=
  shortExact_of_isZero_of_isIso _ h₁ ⟨⟨0, h₂.eq_of_src _ _, h₃.eq_of_src _ _⟩⟩

end ExactCategory

end CategoryTheory
