/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Localization with respect to a Serre class

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace Limits

variable [HasZeroMorphisms C]

lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (kernel.ι f), ← cancel_mono f,
    assoc, assoc, kernel.condition, comp_zero, zero_comp]

lemma isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] :
    IsZero (cokernel f) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π f), ← cancel_epi f,
    cokernel.condition_assoc, zero_comp, comp_zero, comp_zero]

end Limits

variable [Abelian C]

namespace ObjectProperty

variable (P : ObjectProperty C) [P.IsSerreClass]

def serreW : MorphismProperty C := fun _ _ f ↦ P (kernel f) ∧ P (cokernel f)

lemma serreW_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.serreW f ↔ P (cokernel f) := by
  dsimp [serreW]
  have := P.prop_of_isZero (isZero_kernel_of_mono f)
  tauto

lemma serreW_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.serreW f ↔ P (kernel f) := by
  dsimp [serreW]
  have := P.prop_of_isZero (isZero_cokernel_of_epi f)
  tauto

lemma serreW_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P (cokernel f)) : P.serreW f := by
  rwa [serreW_iff_of_mono]

lemma serreW_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P (kernel f)) : P.serreW f := by
  rwa [serreW_iff_of_epi]

lemma serreW_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.serreW f :=
  P.serreW_of_epi _ (P.prop_of_isZero (isZero_kernel_of_mono f))

instance : P.serreW.IsMultiplicative where
  id_mem _ := P.serreW_of_isIso _
  comp_mem f g hf hg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf.1 hg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf.2 hg.2⟩

instance : P.serreW.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩

instance : P.serreW.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    ⟨P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf.1,
      P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf.2⟩

@[nolint unusedArguments]
structure SerreWLocalization (P : ObjectProperty C) [P.IsSerreClass] : Type u where
  obj : C

namespace SerreWLocalization

variable {P} (X Y : P.SerreWLocalization)

namespace Hom

structure DefDomain  where
  src : C
  i : src ⟶ X.obj
  [mono_i : Mono i]
  hi : P.serreW i
  tgt : C
  p : Y.obj ⟶ tgt
  [epi_p : Epi p]
  hp : P.serreW p

namespace DefDomain

attribute [instance] mono_i epi_p

variable {X Y} (d₁ d₂ d₃ : DefDomain X Y)

structure Hom where
  ι : d₁.src ⟶ d₂.src
  ι_i : ι ≫ d₂.i = d₁.i := by aesop_cat
  π : d₂.tgt ⟶ d₁.tgt
  p_π : d₂.p ≫ π = d₁.p := by aesop_cat

namespace Hom

attribute [reassoc (attr := simp)] ι_i p_π

@[simps]
def id (d : DefDomain X Y) : Hom d d where
  ι := 𝟙 _
  π := 𝟙 _

variable {d₁ d₂ d₃} in
@[simps]
def comp (φ : Hom d₁ d₂) (ψ : Hom d₂ d₃) : Hom d₁ d₃ where
  ι := φ.ι ≫ ψ.ι
  π := ψ.π ≫ φ.π

variable (φ : Hom d₁ d₂)

instance : Mono φ.ι := mono_of_mono_fac φ.ι_i

instance : Epi φ.π := epi_of_epi_fac φ.p_π

instance : Subsingleton (Hom d₁ d₂) where
  allEq φ ψ := by
    suffices φ.ι = ψ.ι ∧ φ.π = ψ.π by cases φ; cases ψ; aesop
    constructor
    · simp [← cancel_mono d₂.i]
    · simp [← cancel_epi d₂.p]

instance : Category (DefDomain X Y) where
  id := Hom.id
  comp := Hom.comp

end Hom

lemma exists_min (d₁ d₂ : DefDomain X Y) :
    ∃ (d : DefDomain X Y), Nonempty (d ⟶ d₁) ∧ Nonempty (d ⟶ d₂) := by
  let d : DefDomain X Y :=
    { src := pullback d₁.i d₂.i
      i := pullback.fst _ _ ≫ d₁.i
      hi := by
        refine MorphismProperty.comp_mem _ _ _ ?_ d₁.hi
        sorry
      tgt := pushout d₁.p d₂.p
      p := d₁.p ≫ pushout.inl _ _
      hp := by
        refine MorphismProperty.comp_mem _ _ _ d₁.hp ?_
        sorry }
  refine ⟨d, ⟨{ ι := pullback.fst _ _, π := pushout.inl _ _ }⟩, ⟨
    { ι := pullback.snd _ _,
      ι_i := pullback.condition.symm
      π := pushout.inr _ _
      p_π := pushout.condition.symm }⟩⟩

end DefDomain


end Hom

end SerreWLocalization

end ObjectProperty

end CategoryTheory
