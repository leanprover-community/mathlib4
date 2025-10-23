/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry
open AlgebraicGeometry

variable {S : Scheme.{u}}

@[simp]
lemma CategoryTheory.PreZeroHypercover.quasiCompact_shrink_iff (E : PreZeroHypercover.{w} S) :
    E.shrink.QuasiCompact ↔ E.QuasiCompact :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := E.quasiCompact_shrink_iff.symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def Scheme.qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
lemma CategoryTheory.PreZeroHypercover.presieve₀_mem_qcPrecoverage_iff
    {E : PreZeroHypercover.{w} S} : E.presieve₀ ∈ Scheme.qcPrecoverage S ↔ E.QuasiCompact := by
  rw [← PreZeroHypercover.presieve₀_shrink, Scheme.qcPrecoverage,
    E.shrink.presieve₀_mem_precoverage_iff]
  exact E.quasiCompact_shrink_iff

namespace Scheme

instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily <| by
  intro X Y f hf
  rw [qcCoverFamily_property, Scheme.quasiCompactCover_iff]
  infer_instance

instance : qcPrecoverage.IsStableUnderBaseChange := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

instance : qcPrecoverage.IsStableUnderComposition := by
  refine .of_preZeroHypercoverFamily ?_
  intro X E F hE hF
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

/-- If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage. -/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P ≤ qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  simp only [CategoryTheory.PreZeroHypercover.presieve₀_mem_qcPrecoverage_iff]
  refine .of_isOpenMap fun i ↦ hP _ (Scheme.Cover.map_prop E i)

lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage ≤ qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenEmbedding.isOpenMap

end Scheme

end AlgebraicGeometry
