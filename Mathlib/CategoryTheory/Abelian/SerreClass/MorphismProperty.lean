/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# The classes of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.isoModSerre : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.isoModSerre` is multiplicative, satisfies the two out
of three property and is stable under retracts.

## TODO

* show that a localized category with respect to `P.isoModSerre` is abelian.

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (kernel f) ∧ P (cokernel f)

variable [P.IsSerreClass]

lemma isoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.isoModSerre f ↔ P (kernel f) ∧ P (cokernel f) := Iff.rfl

lemma isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.isoModSerre f ↔ P (cokernel f) := by
  have := P.prop_of_isZero (isZero_kernel_of_mono f)
  rw [isoModSerre_iff]
  tauto

lemma isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.isoModSerre f ↔ P (kernel f) := by
  have := P.prop_of_isZero (isZero_cokernel_of_epi f)
  rw [isoModSerre_iff]
  tauto

lemma isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P (cokernel f)) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_mono]

lemma isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P (kernel f)) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_epi]

lemma isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f :=
  P.isoModSerre_of_epi _ (P.prop_of_isZero (isZero_kernel_of_mono f))

instance : P.isoModSerre.IsMultiplicative where
  id_mem _ := P.isoModSerre_of_isIso _
  comp_mem f g hf hg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf.1 hg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf.2 hg.2⟩

instance : P.isoModSerre.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩

instance : P.isoModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    ⟨P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf.1,
      P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf.2⟩

end ObjectProperty

end CategoryTheory
