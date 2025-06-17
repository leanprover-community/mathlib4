/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# The derivative of a linear equivalence

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous linear equivalences.

We also prove the usual formula for the derivative of the inverse function, assuming it exists.
The inverse function theorem is in `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`.
-/

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E} {c : F}

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable (iso : E ≃L[𝕜] F)

@[fun_prop]
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasStrictFDerivAt

@[fun_prop]
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  iso.toContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.toContinuousLinearMap.fderivWithin hxs

@[fun_prop]
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn

theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun H => ?_, fun H => iso.differentiable.differentiableAt.comp_differentiableWithinAt x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt x H
  rwa [← Function.comp_assoc iso.symm iso f, iso.symm_comp_self] at this

theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← differentiableWithinAt_univ,
    iso.comp_differentiableWithinAt_iff]

theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s := by
  rw [DifferentiableOn, DifferentiableOn]
  simp only [iso.comp_differentiableWithinAt_iff]

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← differentiableOn_univ]
  exact iso.comp_differentiableOn_iff

theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x := by
  refine ⟨fun H => ?_, fun H => iso.hasFDerivAt.comp_hasFDerivWithinAt x H⟩
  simpa [Function.comp_def, ← ContinuousLinearMap.comp_assoc]
    using iso.symm.hasFDerivAt.comp_hasFDerivWithinAt x H

theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x := by
  refine ⟨fun H => ?_, fun H => iso.hasStrictFDerivAt.comp x H⟩
  convert iso.symm.hasStrictFDerivAt.comp x H using 1 <;>
    ext z <;> apply (iso.symm_apply_apply _).symm

theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff]

theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔
      HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x := by
  rw [← iso.comp_hasFDerivWithinAt_iff, ← ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm,
    ContinuousLinearMap.id_comp]

theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff']

theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiableWithinAt_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.comp_zero]

theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) := by
  rw [← fderivWithin_univ, ← fderivWithin_univ]
  exact iso.comp_fderivWithin uniqueDiffWithinAt_univ

lemma _root_.fderivWithin_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G))
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) s x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderivWithin 𝕜 f s x) := by
  change fderivWithin 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) s x = _
  rw [ContinuousLinearEquiv.comp_fderivWithin _ hs]

lemma _root_.fderiv_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) (x : E) :
    fderiv 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  change fderiv 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) x = _
  rw [ContinuousLinearEquiv.comp_fderiv]

lemma _root_.fderiv_continuousLinearEquiv_comp' (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) :
    fderiv 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) =
      fun x ↦ (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  ext x : 1
  exact fderiv_continuousLinearEquiv_comp L f x

theorem comp_right_differentiableWithinAt_iff {f : F → G} {s : Set F} {x : E} :
    DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWithinAt 𝕜 f s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.differentiableWithinAt (mapsTo_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) := by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiableWithinAt
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp_assoc, iso.self_comp_symm] at this

theorem comp_right_differentiableAt_iff {f : F → G} {x : E} :
    DifferentiableAt 𝕜 (f ∘ iso) x ↔ DifferentiableAt 𝕜 f (iso x) := by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiableWithinAt_iff,
    preimage_univ]

theorem comp_right_differentiableOn_iff {f : F → G} {s : Set F} :
    DifferentiableOn 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun H y hy => ?_, fun H y hy => iso.comp_right_differentiableWithinAt_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y, ← comp_right_differentiableWithinAt_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy

theorem comp_right_differentiable_iff {f : F → G} :
    Differentiable 𝕜 (f ∘ iso) ↔ Differentiable 𝕜 f := by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiableOn_iff, preimage_univ]

theorem comp_right_hasFDerivWithinAt_iff {f : F → G} {s : Set F} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f f' s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.hasFDerivWithinAt (mapsTo_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by
    rw [Function.comp_assoc, iso.self_comp_symm]
    rfl
  have B : f' = (f'.comp (iso : E →L[𝕜] F)).comp (iso.symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm, ContinuousLinearMap.comp_id]
  rw [A, B]
  apply H.comp (iso x) iso.symm.hasFDerivWithinAt
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy

theorem comp_right_hasFDerivAt_iff {f : F → G} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) x ↔ HasFDerivAt f f' (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_hasFDerivWithinAt_iff, preimage_univ]

theorem comp_right_hasFDerivWithinAt_iff' {f : F → G} {s : Set F} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f (f'.comp (iso.symm : F →L[𝕜] E)) s (iso x) := by
  rw [← iso.comp_right_hasFDerivWithinAt_iff, ContinuousLinearMap.comp_assoc,
    iso.coe_symm_comp_coe, ContinuousLinearMap.comp_id]

theorem comp_right_hasFDerivAt_iff' {f : F → G} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) f' x ↔ HasFDerivAt f (f'.comp (iso.symm : F →L[𝕜] E)) (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_hasFDerivWithinAt_iff', preimage_univ]

theorem comp_right_fderivWithin {f : F → G} {s : Set F} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) :
    fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x =
      (fderivWithin 𝕜 f s (iso x)).comp (iso : E →L[𝕜] F) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by
      intro h'
      exact h (iso.comp_right_differentiableWithinAt_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.zero_comp]

theorem comp_right_fderiv {f : F → G} {x : E} :
    fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F) := by
  rw [← fderivWithin_univ, ← fderivWithin_univ, ← iso.comp_right_fderivWithin, preimage_univ]
  exact uniqueDiffWithinAt_univ

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable (iso : E ≃ₗᵢ[𝕜] F)

@[fun_prop]
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasStrictFDerivAt

@[fun_prop]
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).hasFDerivWithinAt

@[fun_prop]
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasFDerivAt

@[fun_prop]
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs

@[fun_prop]
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn

theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff

theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiableAt_iff

theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiableOn_iff

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff

theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff

theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff

theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff

theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'

theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'

theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderivWithin hxs

theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv

theorem comp_fderiv' {f : G → E} :
    fderiv 𝕜 (iso ∘ f) = fun x ↦ (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) := by
  ext x : 1
  exact LinearIsometryEquiv.comp_fderiv iso

end LinearIsometryEquiv

/-- If `f (g y) = y` for `y` in a neighborhood of `a` within `t`,
`g` maps a neighborhood of `a` within `t` to a neighborhood of `g a` within `s`,
and `f` has an invertible derivative `f'` at `g a` within `s`,
then `g` has the derivative `f'⁻¹` at `a` within `t`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasFDerivWithinAt.of_local_left_inverse {g : F → E} {f' : E ≃L[𝕜] F} {a : F} {t : Set F}
    (hg : Tendsto g (𝓝[t] a) (𝓝[s] (g a))) (hf : HasFDerivWithinAt f (f' : E →L[𝕜] F) s (g a))
    (ha : a ∈ t) (hfg : ∀ᶠ y in 𝓝[t] a, f (g y) = y) :
    HasFDerivWithinAt g (f'.symm : F →L[𝕜] E) t a := by
  have : (fun x : F => g x - g a - f'.symm (x - a)) =O[𝓝[t] a]
      fun x : F => f' (g x - g a) - (x - a) :=
    ((f'.symm : F →L[𝕜] E).isBigO_comp _ _).congr (fun x ↦ by simp) fun _ ↦ rfl
  refine .of_isLittleO <| this.trans_isLittleO ?_
  clear this
  refine ((hf.isLittleO.comp_tendsto hg).symm.congr' (hfg.mono ?_) .rfl).trans_isBigO ?_
  · intro p hp
    simp [hp, hfg.self_of_nhdsWithin ha]
  · refine ((hf.isBigO_sub_rev f'.antilipschitz).comp_tendsto hg).congr'
      (Eventually.of_forall fun _ => rfl) (hfg.mono ?_)
    rintro p hp
    simp only [(· ∘ ·), hp, hfg.self_of_nhdsWithin ha]

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) a := by
  replace hg := hg.prodMap' hg
  replace hfg := hfg.prodMk_nhds hfg
  have :
    (fun p : F × F => g p.1 - g p.2 - f'.symm (p.1 - p.2)) =O[𝓝 (a, a)] fun p : F × F =>
      f' (g p.1 - g p.2) - (p.1 - p.2) := by
    refine ((f'.symm : F →L[𝕜] E).isBigO_comp _ _).congr (fun x => ?_) fun _ => rfl
    simp
  refine .of_isLittleO <| this.trans_isLittleO ?_
  clear this
  refine ((hf.isLittleO.comp_tendsto hg).symm.congr'
    (hfg.mono ?_) (Eventually.of_forall fun _ => rfl)).trans_isBigO ?_
  · rintro p ⟨hp1, hp2⟩
    simp [hp1, hp2]
  · refine (hf.isBigO_sub_rev.comp_tendsto hg).congr' (Eventually.of_forall fun _ => rfl)
      (hfg.mono ?_)
    rintro p ⟨hp1, hp2⟩
    simp only [(· ∘ ·), hp1, hp2, Prod.map]

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : F →L[𝕜] E) a := by
  simp only [← hasFDerivWithinAt_univ, ← nhdsWithin_univ] at hf hfg ⊢
  exact hf.of_local_left_inverse (.inf hg (by simp)) (mem_univ _) hfg

/-- If `f` is a partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.hasStrictFDerivAt_symm (f : PartialHomeomorph E F) {f' : E ≃L[𝕜] F}
    {a : F} (ha : a ∈ f.target) (htff' : HasStrictFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasStrictFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

/-- If `f` is a partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.hasFDerivAt_symm (f : PartialHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.target) (htff' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

theorem HasFDerivWithinAt.eventually_ne (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ c := by
  rcases eq_or_ne (f x) c with rfl | hc
  · rw [nhdsWithin, diff_eq, ← inf_principal, ← inf_assoc, eventually_inf_principal]
    have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
      isBigO_iff.2 <| hf'.imp fun C hC => Eventually.of_forall fun z => hC _
    have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.isLittleO.trans_isBigO A
    simpa [not_imp_not, sub_eq_zero] using (A.trans this.isBigO_symm).eq_zero_imp
  · exact (h.continuousWithinAt.eventually_ne hc).filter_mono <| by gcongr; apply diff_subset

theorem HasFDerivAt.eventually_ne (h : HasFDerivAt f f' x) (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ c := by
  simpa only [compl_eq_univ_diff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'

end

section

/-
  In the special case of a normed space over the reals,
  we can use scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {f' : E →L[ℝ] F} {x : E}

theorem has_fderiv_at_filter_real_equiv {L : Filter E} :
    Tendsto (fun x' : E => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
      Tendsto (fun x' : E => ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) := by
  symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_congr fun x' => ?_
  simp [norm_smul]

theorem HasFDerivAt.lim_real (hf : HasFDerivAt f f' x) (v : E) :
    Tendsto (fun c : ℝ => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v)) := by
  apply hf.lim v
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩

end

open scoped Pointwise

section TangentCone

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F} {x : E}

/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
theorem HasFDerivWithinAt.mapsTo_tangent_cone (h : HasFDerivWithinAt f f' s x) :
    MapsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x)) := by
  rintro v ⟨c, d, dtop, clim, cdlim⟩
  refine
    ⟨c, fun n => f (x + d n) - f x, mem_of_superset dtop ?_, clim, h.lim atTop dtop clim cdlim⟩
  simp +contextual [-mem_image, mem_image_of_mem]

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt (h : HasFDerivWithinAt f f' s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) := by
  refine ⟨h'.dense_of_mapsTo f'.continuous hs.1 ?_, h.continuousWithinAt.mem_closure_image hs.2⟩
  show
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) ≤
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'
  rw [Submodule.span_le]
  exact h.mapsTo_tangent_cone.mono Subset.rfl Submodule.subset_span

theorem UniqueDiffOn.image {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueDiffOn 𝕜 (f '' s) :=
  forall_mem_image.2 fun x hx => (hf' x hx).uniqueDiffWithinAt (hs x hx) (hd x hx)

theorem HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv (e' : E ≃L[𝕜] F)
    (h : HasFDerivWithinAt f (e' : E →L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.uniqueDiffWithinAt hs e'.surjective.denseRange

theorem ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun _ _ => e.hasFDerivWithinAt) fun _ _ => e.surjective.denseRange

@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) :
    UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩

@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) :
    UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s := by
  rw [← e.image_symm_eq_preimage, e.symm.uniqueDiffOn_image_iff]

protected theorem UniqueDiffWithinAt.smul (h : UniqueDiffWithinAt 𝕜 s x) {c : 𝕜} (hc : c ≠ 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) :=
  (ContinuousLinearEquiv.smulLeft <| Units.mk0 c hc).hasFDerivWithinAt
    |>.uniqueDiffWithinAt_of_continuousLinearEquiv _ h

protected theorem UniqueDiffWithinAt.smul_iff {c : 𝕜} (hc : c ≠ 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) ↔ UniqueDiffWithinAt 𝕜 s x :=
  ⟨fun h ↦ by simpa [hc] using h.smul (inv_ne_zero hc), (.smul · hc)⟩

end TangentCone

section SMulLeft

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F} {x : E}

theorem fderivWithin_const_smul_field {R : Type*} [DivisionRing R] [Module R F]
    [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · lift c to Rˣ using IsUnit.mk0 _ hc
    have : SMulCommClass Rˣ 𝕜 F := .symm _ _ _
    exact (ContinuousLinearEquiv.smulLeft c).comp_fderivWithin hs

theorem hasFDerivWithinAt_comp_smul_smul_iff {c : 𝕜} :
    HasFDerivWithinAt (f <| c • ·) (c • f') s x ↔ HasFDerivWithinAt f f' (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hasFDerivWithinAt_const, HasFDerivWithinAt.of_subsingleton (subsingleton_zero_smul_set _)]
  · lift c to 𝕜ˣ using IsUnit.mk0 c hc
    have A : f'.comp ((ContinuousLinearEquiv.smulLeft c : E ≃L[𝕜] E) : E →L[𝕜] E) = c • f' := by
      ext; simp
    rw [← Units.smul_def c x, ← ContinuousLinearEquiv.smulLeft_apply_apply (R₁ := 𝕜),
      ← ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff, A]
    simp [Function.comp_def, ← Units.smul_def, ← preimage_smul_inv, preimage_preimage]

theorem hasFDerivWithinAt_comp_smul_iff_smul {c : 𝕜} (hc : c ≠ 0) :
    HasFDerivWithinAt (f <| c • ·) f' s x ↔ HasFDerivWithinAt (c • f) f' (c • s) (c • x) := by
  simp only [← hasFDerivWithinAt_comp_smul_smul_iff, Pi.smul_apply]
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  exact (ContinuousLinearEquiv.smulLeft c).comp_hasFDerivWithinAt_iff.symm

theorem fderivWithin_comp_smul_eq_fderivWithin_smul (c : 𝕜) :
    fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c • f) (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · classical
    simp only [fderivWithin, DifferentiableWithinAt, hasFDerivWithinAt_comp_smul_iff_smul hc]

theorem fderivWithin_comp_smul (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (f <| c • ·) s x = c • fderivWithin 𝕜 f (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field]
    exact hs.smul hc

theorem fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x) := by
  rw [← fderivWithin_univ, fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]

end SMulLeft
