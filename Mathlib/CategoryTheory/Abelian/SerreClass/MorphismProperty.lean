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
# The class of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.isoModSerre : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.isoModSerre` is multiplicative, satisfies the two out
of three property and is stable under retracts. (Similarly, we define
`P.monoModSerre` and `P.epiModSerre`.)

## TODO

* show that a localized category with respect to `P.isoModSerre` is abelian.

-/

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of monomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` satisfies `P`. -/
@[nolint unusedArguments]
def monoModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (kernel f)

/-- The class of epimorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `cokernel f` satisfies `P`. -/
@[nolint unusedArguments]
def epiModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (cokernel f)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  P.monoModSerre ⊓ P.epiModSerre

variable [P.IsSerreClass]

lemma monoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.monoModSerre f ↔ P (kernel f) := Iff.rfl

lemma monomorphisms_le_monoModSerre : monomorphisms C ≤ P.monoModSerre :=
  fun _ _ f (_ : Mono f) ↦ P.prop_of_isZero (isZero_kernel_of_mono f)

lemma monoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.monoModSerre f :=
  P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)

lemma epiModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.epiModSerre f ↔ P (cokernel f) := Iff.rfl

lemma epimorphisms_le_epiModSerre : epimorphisms C ≤ P.epiModSerre :=
  fun _ _ f (_ : Epi f) ↦ P.prop_of_isZero (isZero_cokernel_of_epi f)

lemma epiModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.epiModSerre f :=
  P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

lemma isoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f := Iff.rfl

lemma isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.isoModSerre f ↔ P.epiModSerre f := by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto

lemma isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.isoModSerre f ↔ P.monoModSerre f := by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto

lemma isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_mono]

lemma isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_epi]

lemma isomorphisms_le_isoModSerre : isomorphisms C ≤ P.isoModSerre :=
  fun _ _ f (_ : IsIso f) ↦ ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩

lemma isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f :=
  P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)

instance : P.monoModSerre.IsMultiplicative where
  id_mem _ := P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg

instance : P.epiModSerre.IsMultiplicative where
  id_mem _ := P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg

instance : P.isoModSerre.IsMultiplicative := by
  dsimp only [isoModSerre]
  infer_instance

instance : P.monoModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

instance : P.epiModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf

instance : P.isoModSerre.IsStableUnderRetracts := by
  dsimp only [isoModSerre]
  infer_instance

instance : P.isoModSerre.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩

lemma le_kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : P.isoModSerre.IsInvertedBy F) :
    P ≤ F.kernel := by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

lemma isoModSerre_isInvertedBy_iff (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    P.isoModSerre.IsInvertedBy F ↔ P ≤ F.kernel := by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ ↦ ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel f)).map F).epi_f (((hF _ h₂).eq_of_tgt _ _))
  exact isIso_of_mono_of_epi (F.map f)

end ObjectProperty

end CategoryTheory
