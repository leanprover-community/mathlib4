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

In this file we prove several versions of the following theorem.
Consider three functions `f : F → G`, `g : E → F`, and `h : E → G`,
together with "candidate derivatives" `f' : F →L[𝕜] G`, `g' : E →L[𝕜] F`, and `h' : E →L[𝕜] G`.
Suppose that

- `f ∘ g = h` in a neighborhood of `a`;
- `h` has derivative `h'` at `a`;
- `f` has derivative `f'` at `g a`;
- `g` is continuous at `a`;
- either `f'` has a right inverse `f'⁻¹` and `g' = f'⁻¹ ∘ h'`,
  or `f'` is a topological embedding and `h' = f' ∘ g'`.

Then `g` has derivative `g'` at `a`.
We prove these theorems for different differentiability predicates,
then specialize it to the cases when `f'` is a linear equivalence and/or `h = id`.
-/

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

public section

section OfComp

variable {g : E → F} {f : F → G} {h : E → G}
  {g' : E →L[𝕜] F} {f' : F →L[𝕜] G} {h' : E →L[𝕜] G} {f'symm : G →L[𝕜] F}
  {lE : Filter (E × E)} {lF : Filter (F × F)}
  {a : E} {s : Set E} {t : Set F}

private theorem HasFDerivAtFilter.of_comp_aux (hf_emb : Topology.IsEmbedding f')
    (htendsto : Tendsto (Prod.map g g) lE lF)
    (hh : HasFDerivAtFilter h h' lE)
    (hf : HasFDerivAtFilter f f' lF)
    (hcomp : Prod.map (f ∘ g) (f ∘ g) =ᶠ[lE] Prod.map h h)
    (ho : (fun (x, y) ↦ g x - g y - g' (x - y)) =O[𝕜; lE]
      (fun (x, y) ↦ f' (g x - g y) - h' (x - y))) :
    HasFDerivAtFilter g g' lE := by
  refine .of_isLittleOTVS <| ho.trans_isLittleOTVS <| .triangle (.symm ?_) hh.isLittleOTVS
  refine (hf.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl |>.trans_isBigOTVS ?_
  · refine hcomp.mono ?_
    simp +contextual
  · refine hf.isThetaTVS_sub hf_emb.isInducing |>.symm.isBigOTVS.comp_tendsto htendsto |>.trans ?_
    refine hh.isBigOTVS_sub.congr' (hcomp.mono ?_) .rfl
    simp +contextual

/-!
### Left inverse

In this section, we prove that `g` has derivative `f'⁻¹ ∘ h'`
whenever `h = f ∘ g` has derivative `h'` and `f'⁻¹` is a left inverse to `f'`.
-/

theorem HasFDerivAtFilter.of_comp_of_leftInverse
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hh : HasFDerivAtFilter h h' lE) (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAtFilter g (f'symm ∘L h') lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)
  · refine f'symm.isBigOTVS_comp.congr_left ?_
    simp [hf'symm _]

theorem HasFDerivWithinAt.of_comp_of_leftInverse
    (hst : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hh : HasFDerivWithinAt h h' s a) (hcomp : f ∘ g =ᶠ[𝓝[s] a] h)
    (hf'symm : Function.LeftInverse f'symm f') (ha : a ∈ s) :
    HasFDerivWithinAt g (f'symm ∘L h') s a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)

theorem HasFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hh : HasFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAt g (f'symm ∘L h') a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hgc.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

theorem HasStrictFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hh : HasStrictFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasStrictFDerivAt g (f'symm ∘L h') a :=
  HasFDerivAtFilter.of_comp_of_leftInverse (hgc.prodMap_nhds hgc) hf hh
    (hcomp.prodMap_nhds hcomp) hf'symm


/-!
### Embedding

In this section we show that `g` has derivative `g'`
provided that `h = f ∘ g` has derivative `f' ∘ g'`, where `f'` is a topological embedding.
-/

theorem HasFDerivAtFilter.of_comp_of_isEmbedding
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAtFilter h (f' ∘L g') lE)
    (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h) :
    HasFDerivAtFilter g g' lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  refine f'.isThetaTVS_comp hf'.isInducing |>.symm.isBigOTVS.congr_right ?_
  simp

theorem HasFDerivWithinAt.of_comp_of_isEmbedding
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivWithinAt h (f' ∘L g') s a)
    (hcomp : (f ∘ g) =ᶠ[𝓝[s] a] h) (ha : a ∈ s) :
    HasFDerivWithinAt g g' s a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.prodMap (by simp)
  · exact hcomp.prodMap <| hcomp.self_of_nhdsWithin ha

theorem HasFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasFDerivAt g g' a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds

theorem HasStrictFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasStrictFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasStrictFDerivAt g g' a :=
  HasFDerivAtFilter.of_comp_of_isEmbedding (hg.prodMap hg) hf hf' hh (hcomp.prodMap_nhds hcomp)

end OfComp

/-!
### Local left inverse (equivalence)
-/

section LeftInverse

variable {g : E → F} {f : F → E} {f' : F ≃L[𝕜] E} {a : E} {s : Set E} {t : Set F}

/-- If `f (g x) = x` for `x` in some neighborhood of `a`, `g` is continuous at `a`,
and `f` has an invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFDerivAt.of_local_left_inverse
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : F →L[𝕜] E) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : E →L[𝕜] F) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E →L[𝕜] F)) hg (hasFDerivAt_id _) hfg
    f'.symm_apply_apply

/-- If `f (g x) = x` for `x` in a neighborhood of `a` within `s`,
`g` maps a neighborhood of `a` within `s` to a neighborhood of `g a` within `t`,
and `f` has an invertible derivative `f'` at `g a` within `t`,
then `g` has the derivative `f'⁻¹` at `a` within `s`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasFDerivWithinAt.of_local_left_inverse
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f (f' : F →L[𝕜] E) t (g a))
    (ha : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, f (g x) = x) :
    HasFDerivWithinAt g (f'.symm : E →L[𝕜] F) s a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E →L[𝕜] F)) hg (hasFDerivWithinAt_id _ _) hfg
    f'.symm_apply_apply ha

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : F →L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
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
