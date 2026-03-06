/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Notation

/-! # `mfderiv` and scalar multiplication -/

open Set
open scoped Manifold ContDiff

@[expose] public section mfderiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : M → F} {s : M → 𝕜} {x : M}

theorem MDifferentiableAt.differentiableAt_comp_chartAt_symm
    (hs : MDiffAt f x) :
    letI φ := chartAt H x;
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm ∘ I.symm) (range I) (I (φ x)) := by
  have hφ := mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x) (I := I)
  rw [← extChartAt_to_inv x (I := I)] at hs
  have := hs.comp_mdifferentiableWithinAt (extChartAt I x x) hφ
  exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp this

lemma mfderiv_smul (hf : MDiffAt f x)
    (hs : MDiffAt s x) (v : TangentSpace I x) :
    letI dsxv := NormedSpace.fromTangentSpace (s x) (mfderiv% s x v)
    letI dfxv := NormedSpace.fromTangentSpace (f x) (mfderiv% f x v)
    mfderiv% (s • f) x v = (s x) • dfxv + dsxv • f x := by
  set φ := chartAt H x
  -- TODO: inlining hs' or hf' breaks the proof, why?
  have hs' : DifferentiableWithinAt 𝕜 (s ∘ φ.symm ∘ I.symm) (range I) (I (φ x)) :=
    hs.differentiableAt_comp_chartAt_symm
  have aux := hs.differentiableAt_comp_chartAt_symm
  have hf' : DifferentiableWithinAt 𝕜 (f ∘ φ.symm ∘ I.symm) (range I) (I (φ x)) :=
    hf.differentiableAt_comp_chartAt_symm
  -- `have := hs.differentiableAt_comp_chartAt_symm` looks identical apart from unfolding φ
  have hsf : MDiffAt (s • f) x := hs.smul hf
  simp? [mfderiv, hsf, hs, hf] says
    simp only [Pi.smul_apply', mfderiv, hsf, ↓reduceIte, writtenInExtChartAt, extChartAt,
      OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe, Function.comp_apply,
      hf, hs]
  -- Use the defeq that `chartAt (s x)` and `chartAt (f x)` are the identity.
  erw [fderivWithin_smul I.uniqueDiffWithinAt_image hs' hf']
  simp [φ.left_inv (ChartedSpace.mem_chart_source x)]
  rfl
