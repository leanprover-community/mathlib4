/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Bousfield localizations with respect to Serre classes

If `G : D ⥤ C` is an exact functor between abelian categories,
with a fully faithful right adjoint `F`, then `G` identifies
`C` to the localization of `D` with respect to the
class of morphisms `G.kernel.isoModSerre`, i.e. `D`
is the localization of `C` with respect to the Serre class
`G.kernel` consisting of the objects in `D`
that are sent to a zero object by `G`.
(We also translate this in terms of a left Bousfield localization.)

-/

namespace CategoryTheory

open Localization Limits MorphismProperty

variable {C D : Type*} [Category C] [Category D]
  [Abelian C] [Abelian D] (G : D ⥤ C)
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

namespace Abelian

lemma isoModSerre_kernel_eq_inverseImage_isomorphisms :
    G.kernel.isoModSerre = (isomorphisms C).inverseImage G := by
  ext X Y f
  refine ⟨(G.kernel.isoModSerre_isInvertedBy_iff G).2 (by rfl) _, fun hf ↦ ?_⟩
  simp only [inverseImage_iff, isomorphisms.iff] at hf
  constructor
  · exact KernelFork.IsLimit.isZero_of_mono
      (KernelFork.mapIsLimit _ (kernelIsKernel f) G)
  · exact CokernelCofork.IsColimit.isZero_of_epi
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) G)

variable {G}

lemma isoModSerre_kernel_eq_leftBousfield_W_of_rightAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.kernel.isoModSerre = LeftBousfield.W (· ∈ Set.range F.obj) := by
  rw [LeftBousfield.W_eq_inverseImage_isomorphisms adj,
    isoModSerre_kernel_eq_inverseImage_isomorphisms]

lemma isLocalization_isoModSerre_kernel_of_leftAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.IsLocalization G.kernel.isoModSerre := by
  rw [isoModSerre_kernel_eq_inverseImage_isomorphisms G]
  exact adj.isLocalization

end Abelian

end CategoryTheory
