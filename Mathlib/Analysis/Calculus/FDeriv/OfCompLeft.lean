/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Inverse function theorem, the "easy half"
-/

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

public section

section OfComp

variable {f : E → F} {g : F → G} {h : E → G}
  {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {h' : E →L[𝕜] G} {g'symm : G →L[𝕜] F}
  {lE : Filter (E × E)} {lF : Filter (F × F)}
  {a : E} {s : Set E} {t : Set F}

private theorem HasFDerivAtFilter.of_comp_aux (hg_emb : Topology.IsEmbedding g')
    (htendsto : Tendsto (Prod.map f f) lE lF)
    (hh : HasFDerivAtFilter h h' lE)
    (hg : HasFDerivAtFilter g g' lF)
    (hcomp : Prod.map (g ∘ f) (g ∘ f) =ᶠ[lE] Prod.map h h)
    (ho : (fun (x, y) ↦ f x - f y - f' (x - y)) =O[𝕜; lE]
      (fun (x, y) ↦ g' (f x - f y) - h' (x - y))) :
    HasFDerivAtFilter f f' lE := by
  refine .of_isLittleOTVS <| ho.trans_isLittleOTVS <| .triangle (.symm ?_) hh.isLittleOTVS
  refine (hg.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl |>.trans_isBigOTVS ?_
  · refine hcomp.mono ?_
    simp +contextual
  · refine hg.isThetaTVS_sub hg_emb.isInducing |>.symm.isBigOTVS.comp_tendsto htendsto |>.trans ?_
    refine hh.isBigOTVS_sub.congr' (hcomp.mono ?_) .rfl
    simp +contextual

/-!
### Left inverse

In this section, we prove that `f` has derivative `g'⁻¹ ∘ h'`
whenever `h = g ∘ f` has derivative `h'` and `g'⁻¹` is a left inverse to `g'`.
-/

theorem HasFDerivAtFilter.of_comp_of_leftInverse
    (hf : Tendsto (Prod.map f f) lE lF) (hg : HasFDerivAtFilter g g' lF)
    (hh : HasFDerivAtFilter h h' lE) (hcomp : (Prod.map (g ∘ f) (g ∘ f)) =ᶠ[lE] Prod.map h h)
    (hg'symm : Function.LeftInverse g'symm g') :
    HasFDerivAtFilter f (g'symm ∘L h') lE := by
  apply of_comp_aux (g := g) (g' := g') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hg'symm (map_continuous _) (map_continuous _)
  · refine g'symm.isBigOTVS_comp.congr_left ?_
    simp [hg'symm _]

theorem HasFDerivWithinAt.of_comp_of_leftInverse
    (hst : Tendsto f (𝓝[s] a) (𝓝[t] (f a))) (hg : HasFDerivWithinAt g g' t (f a))
    (hh : HasFDerivWithinAt h h' s a) (hcomp : g ∘ f =ᶠ[𝓝[s] a] h)
    (hg'symm : Function.LeftInverse g'symm g') (ha : a ∈ s) :
    HasFDerivWithinAt f (g'symm ∘L h') s a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hg hh ?_ hg'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)

theorem HasFDerivAt.of_comp_of_leftInverse
    (hst : ContinuousAt f a) (hg : HasFDerivAt g g' (f a))
    (hh : HasFDerivAt h h' a) (hcomp : g ∘ f =ᶠ[𝓝 a] h)
    (hg'symm : Function.LeftInverse g'symm g') :
    HasFDerivAt f (g'symm ∘L h') a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hg hh ?_ hg'symm
  · exact hst.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

theorem HasStrictFDerivAt.of_comp_of_leftInverse
    (hst : ContinuousAt f a) (hg : HasStrictFDerivAt g g' (f a))
    (hh : HasStrictFDerivAt h h' a) (hcomp : g ∘ f =ᶠ[𝓝 a] h)
    (hg'symm : Function.LeftInverse g'symm g') :
    HasStrictFDerivAt f (g'symm ∘L h') a :=
  HasFDerivAtFilter.of_comp_of_leftInverse (hst.prodMap_nhds hst) hg hh
    (hcomp.prodMap_nhds hcomp) hg'symm


/-!
### Embedding

In this section we show that `f` has derivative `f'`
provided that `h = g ∘ f` has derivative `g' ∘ f'`, where `g'` is a topological embedding.
-/

theorem HasFDerivAtFilter.of_comp_of_isEmbedding
    (hf : Tendsto (Prod.map f f) lE lF) (hg : HasFDerivAtFilter g g' lF)
    (hg' : Topology.IsEmbedding g') (hh : HasFDerivAtFilter h (g' ∘L f') lE)
    (hcomp : (Prod.map (g ∘ f) (g ∘ f)) =ᶠ[lE] Prod.map h h) :
    HasFDerivAtFilter f f' lE := by
  apply of_comp_aux (g := g) (g' := g') <;> try assumption
  refine g'.isThetaTVS_comp hg'.isInducing |>.symm.isBigOTVS.congr_right ?_
  simp

theorem HasFDerivWithinAt.of_comp_of_isEmbedding
    (hf : Tendsto f (𝓝[s] a) (𝓝[t] (f a))) (hg : HasFDerivWithinAt g g' t (f a))
    (hg' : Topology.IsEmbedding g') (hh : HasFDerivWithinAt h (g' ∘L f') s a)
    (hcomp : (g ∘ f) =ᶠ[𝓝[s] a] h) (ha : a ∈ s) :
    HasFDerivWithinAt f f' s a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hg hg' hh ?_
  · exact hf.prodMap (by simp)
  · exact hcomp.prodMap <| hcomp.self_of_nhdsWithin ha

theorem HasFDerivAt.of_comp_of_isEmbedding
    (hf : ContinuousAt f a) (hg : HasFDerivAt g g' (f a))
    (hg' : Topology.IsEmbedding g') (hh : HasFDerivAt h (g' ∘L f') a)
    (hcomp : (g ∘ f) =ᶠ[𝓝 a] h) :
    HasFDerivAt f f' a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hg hg' hh ?_
  · exact hf.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

theorem HasStrictFDerivAt.of_comp_of_isEmbedding
    (hf : ContinuousAt f a) (hg : HasStrictFDerivAt g g' (f a))
    (hg' : Topology.IsEmbedding g') (hh : HasStrictFDerivAt h (g' ∘L f') a)
    (hcomp : (g ∘ f) =ᶠ[𝓝 a] h) :
    HasStrictFDerivAt f f' a :=
  HasFDerivAtFilter.of_comp_of_isEmbedding (hf.prodMap hf) hg hg' hh (hcomp.prodMap_nhds hcomp)

end OfComp

/-!
### Local left inverse (equivalence)
-/

section LeftInverse

variable {f : E → F} {g : F → E} {g' : F ≃L[𝕜] E} {a : E} {s : Set E} {t : Set F}

/-- If `g (f x) = x` for `x` in some neighborhood of `a`, `f` is continuous at `a`,
and `g` has an invertible derivative `g'` at `f a`, then `f` has the derivative `g'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFDerivAt.of_local_left_inverse
    (hf : ContinuousAt f a) (hg : HasFDerivAt g (g' : F →L[𝕜] E) (f a))
    (hgf : ∀ᶠ y in 𝓝 a, g (f y) = y) : HasFDerivAt f (g'.symm : E →L[𝕜] F) a :=
  hg.of_comp_of_leftInverse (g'symm := (g'.symm : E →L[𝕜] F)) hf (hasFDerivAt_id _) hgf
    g'.symm_apply_apply

/-- If `g (f x) = x` for `x` in a neighborhood of `a` within `s`,
`f` maps a neighborhood of `a` within `s` to a neighborhood of `f a` within `t`,
and `g` has an invertible derivative `g'` at `f a` within `t`,
then `f` has the derivative `g'⁻¹` at `a` within `s`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasFDerivWithinAt.of_local_left_inverse
    (hf : Tendsto f (𝓝[s] a) (𝓝[t] (f a))) (hg : HasFDerivWithinAt g (g' : F →L[𝕜] E) t (f a))
    (ha : a ∈ s) (hgf : ∀ᶠ x in 𝓝[s] a, g (f x) = x) :
    HasFDerivWithinAt f (g'.symm : E →L[𝕜] F) s a :=
  hg.of_comp_of_leftInverse (g'symm := (g'.symm : E →L[𝕜] F)) hf (hasFDerivWithinAt_id _ _) hgf
    g'.symm_apply_apply ha

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) a :=
  hf.of_comp_of_leftInverse (g'symm := (f'.symm : F →L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
    f'.symm_apply_apply

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
