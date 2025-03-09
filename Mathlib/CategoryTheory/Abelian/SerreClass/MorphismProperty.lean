/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# The classes of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.serreW : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.serreW` is multiplicative, satisfies the two out
of three property and is stable under retracts.

## TODO

* show that localized category with respect to `P.serreW` is abelian.

-/

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
def serreW [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (kernel f) ∧ P (cokernel f)

variable [P.IsSerreClass]

lemma serreW_iff {X Y : C} (f : X ⟶ Y) :
    P.serreW f ↔ P (kernel f) ∧ P (cokernel f) := Iff.rfl

lemma serreW_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : P.serreW f ↔ P (cokernel f) := by
  have := P.prop_of_isZero (isZero_kernel_of_mono f)
  rw [serreW_iff]
  tauto

lemma serreW_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.serreW f ↔ P (kernel f) := by
  have := P.prop_of_isZero (isZero_cokernel_of_epi f)
  rw [serreW_iff]
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

lemma le_kernel_of_serreW_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : P.serreW.IsInvertedBy F) :
    P ≤ F.kernel := by
  intro X hX
  simp only [prop_inverseImage_iff]
  let f : 0 ⟶ X := 0
  have := hF _ ((P.serreW_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  refine (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

lemma serreW_isInvertedBy_iff (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    P.serreW.IsInvertedBy F ↔ P ≤ F.kernel := by
  refine ⟨P.le_kernel_of_serreW_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ ↦ ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel f)).map F).epi_f (((hF _ h₂).eq_of_tgt _ _))
  exact isIso_of_mono_of_epi (F.map f)

end ObjectProperty

end CategoryTheory
