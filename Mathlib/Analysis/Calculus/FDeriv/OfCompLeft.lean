/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Inverse function theorem, the "easy half"
-/

public section

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {f' : E →L[𝕜] F} {s : Set E}
  {g : G → E} {h : G → F} {h' : G →L[𝕜] F} {a : G} {t : Set G}

theorem HasFDerivWithinAt.of_comp_of_leftInverse {f'symm : F →L[𝕜] E}
    (hst : Tendsto g (𝓝[t] a) (𝓝[s] (g a))) (hf : HasFDerivWithinAt f f' s (g a))
    (hh : HasFDerivWithinAt h h' t a) (hcomp : f ∘ g =ᶠ[𝓝[t] a] h)
    (hf'symm : Function.LeftInverse f'symm f') (ha : a ∈ t) :
    HasFDerivWithinAt g (f'symm ∘L h') t a := by
  refine .of_isLittleOTVS ?_
  calc (fun x' ↦ g x' - g a - (f'symm ∘L h') (x' - a))
    _ =O[𝕜; 𝓝[t] a] fun x' ↦ f' (g x' - g a) - h' (x' - a) :=
      f'symm.isBigOTVS_comp.congr_left <| by simp [hf'symm _]
    _ =o[𝕜; 𝓝[t] a] (· - a) := ?_
  refine hf.isLittleOTVS.comp_tendsto hst |>.symm |>.trans_isBigOTVS ?_ |>.triangle ?_
  · refine hf.isThetaTVS_sub
      (Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)).isInducing
      |>.symm.isBigOTVS.comp_tendsto hst |>.trans ?_
    refine hh.isBigOTVS_sub.congr' (hcomp.mono fun x hx ↦ ?_) .rfl
    simp [← hx, ← hcomp.self_of_nhdsWithin ha]
  · refine hh.isLittleOTVS.congr' (hcomp.mono fun x hx ↦ ?_) .rfl
    simp [← hx, ← hcomp.self_of_nhdsWithin ha]

theorem HasFDerivWithinAt.of_comp (hst : Tendsto g (𝓝[t] a) (𝓝[s] (g a)))
    (hf : HasFDerivWithinAt f f' s (g a)) (hh : HasFDerivWithinAt h h' t a)
    (hcomp : f ∘ g =ᶠ[𝓝[t] a] h) (hf' : f'.IsInvertible) (ha : a ∈ t) :
    HasFDerivWithinAt g (f'.inverse ∘L h') t a :=
  .of_comp_of_leftInverse hst hf hh hcomp hf'.inverse_apply_self ha

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
  simpa using hf.of_comp hg (hasFDerivWithinAt_id ..) hfg (by simp) ha

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

theorem HasFDerivAt.of_comp_left {g : G → E} {h : G → F} {h' : G →L[𝕜] F} {a : G}
    (hst : ContinuousAt g a) (hf : HasFDerivAt f f' (g a)) (hh : HasFDerivAt h h' a)
    (hf' : f'.IsInvertible) (hcomp : f ∘ g =ᶠ[𝓝 a] h) :
    HasFDerivAt g (f'.inverse.comp h') a := by
  simp only [← hasFDerivWithinAt_univ, ← nhdsWithin_univ] at *
  refine hf.of_comp_left ?_ hh hcomp hf' trivial
  simpa

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : F →L[𝕜] E) a := by
  simp only [← hasFDerivWithinAt_univ, ← nhdsWithin_univ] at hf hfg ⊢
  exact hf.of_local_left_inverse (.inf hg (by simp)) (Set.mem_univ _) hfg

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem OpenPartialHomeomorph.hasStrictFDerivAt_symm (f : OpenPartialHomeomorph E F)
    {f' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
    (htff' : HasStrictFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasStrictFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem OpenPartialHomeomorph.hasFDerivAt_symm (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F}
    {a : F} (ha : a ∈ f.target) (htff' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)
