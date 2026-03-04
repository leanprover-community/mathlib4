/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

@[simp]
lemma quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E.shrink ↔ QuasiCompactCover E :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
lemma presieve₀_mem_qcPrecoverage_iff {E : PreZeroHypercover.{w} S} :
    E.presieve₀ ∈ Scheme.qcPrecoverage S ↔ QuasiCompactCover E := by
  rw [← PreZeroHypercover.presieve₀_shrink, Scheme.qcPrecoverage,
    E.shrink.presieve₀_mem_precoverage_iff]
  simp

instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily fun X Y f hf ↦ by
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
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

instance : qcPrecoverage.IsStableUnderSup := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

/-- If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage. -/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P ≤ qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i ↦ hP _ (Scheme.Cover.map_prop E i)

lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage ≤ qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenEmbedding.isOpenMap

end AlgebraicGeometry.Scheme
