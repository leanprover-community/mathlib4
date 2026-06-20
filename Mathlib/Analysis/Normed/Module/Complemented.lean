/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sharvil Kesarwani
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Complemented subspaces of Banach spaces

A submodule `p` of a topological module `E` over `R` is called *complemented*
(`Submodule.ClosedComplemented`) if there exists a continuous linear projection `f : E →ₗ[R] p`,
`∀ x : p, f x = x`.

All results in this file rely on the open mapping theorem, hence the Banach space assumption.

## Main results

* `Submodule.isTopCompl_iff_isCompl_isClosed`: in a Banach space, two submodules are topological
  complements (`Submodule.IsTopCompl`) if and only if they are algebraic complements (`IsCompl`)
* `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`: in a Banach space. a
  submodule is complemented if and only if it is closed and admits a closed algebraic complement.

## TODO

Generalize these results to metrizable complete topological vector spaces, once the open mapping
theorem is available in that setting.

## Tags

complemented subspace, Banach space
-/

@[expose] public section


variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

open LinearMap (ker range)

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
nonrec def equivProdOfSurjectiveOfIsCompl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) : E ≃L[𝕜] F × G :=
  (f.equivProdOfSurjectiveOfIsCompl (g : E →ₗ[𝕜] G) hf hg hfg).toContinuousLinearEquivOfContinuous
    (f.continuous.prodMk g.continuous)

@[simp]
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.prod g := rfl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_toLinearEquiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : f.range = ⊤) (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv =
      LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg := rfl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end ContinuousLinearMap

namespace Submodule

variable [CompleteSpace E] {p q : Subspace 𝕜 E}

theorem IsCompl.isTopCompl_of_isClosed (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : IsTopCompl p q := by
  haveI := hp.completeSpace_coe; haveI := hq.completeSpace_coe
  rw [isTopCompl_iff_continuous_symm_prodEquivOfIsCompl h]
  exact (p.prodEquivOfIsCompl q h).continuous_symm (continuous_prodEquivOfIsCompl h)

open Submodule in
theorem isTopCompl_iff_isCompl_isClosed :
    IsTopCompl p q ↔ IsCompl p q ∧ IsClosed (p : Set E) ∧ IsClosed (q : Set E) :=
  ⟨fun h ↦ ⟨h.isCompl, h.isClosed, h.isClosed'⟩, fun h ↦ h.1.isTopCompl_of_isClosed h.2.1 h.2.2⟩

variable (p q)

/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
@[deprecated prodEquivOfIsTopCompl (since := "2026-06-07")]
def prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E := by
  haveI := hp.completeSpace_coe; haveI := hq.completeSpace_coe
  refine (p.prodEquivOfIsCompl q h).toContinuousLinearEquivOfContinuous ?_
  exact (p.subtypeL.coprod q.subtypeL).continuous

/-- Projection to a closed submodule along a closed complement. -/
@[deprecated projectionOntoL (since := "2026-06-07")]
def linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L ↑(prodEquivOfClosedCompl p q h hp hq).symm

variable {p q}

@[deprecated "Use `coe_prodEquivOfIsTopCompl` instead" (since := "2026-06-07")]
theorem coe_prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquivOfIsCompl q h := rfl

@[deprecated "Use `coe_symm_prodEquivOfIsTopCompl` instead" (since := "2026-06-07")]
theorem coe_prodEquivOfClosedCompl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (p.prodEquivOfIsCompl q h).symm := rfl

@[deprecated "Use `toLinearMap_projectionOntoL` instead" (since := "2026-06-07")]
theorem coe_continuous_linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    (p.linearProjOfClosedCompl q h hp hq : E →ₗ[𝕜] p) = p.projectionOnto q h := rfl

@[deprecated "Use `coe_projectionOntoL` instead" (since := "2026-06-07")]
theorem coe_continuous_linearProjOfClosedCompl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : ⇑(p.linearProjOfClosedCompl q h hp hq) = p.projectionOnto q h :=
  rfl

theorem ClosedComplemented.of_isCompl_isClosed (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  (IsCompl.isTopCompl_of_isClosed h hp hq).closedComplemented

alias IsCompl.closedComplemented_of_isClosed := ClosedComplemented.of_isCompl_isClosed

theorem closedComplemented_iff_isClosed_exists_isClosed_isCompl :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ q : Submodule 𝕜 E, IsClosed (q : Set E) ∧ IsCompl p q :=
  ⟨fun h => ⟨h.isClosed, h.exists_isClosed_isCompl⟩,
    fun ⟨hp, ⟨_, hq, hpq⟩⟩ => .of_isCompl_isClosed hpq hp hq⟩

end Submodule
