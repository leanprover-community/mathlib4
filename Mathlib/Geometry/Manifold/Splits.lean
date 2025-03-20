/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Module.Complemented

/-! # Linear maps which split

TODO: better doc-string, move this to a better place


-/

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

/-- A continuous linear map `f : E → F` *splits* iff it is injective, has closed range and
its image has a closed complement. -/
def ContinuousLinearMap.Splits (f : E →L[𝕜] F) : Prop :=
  Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented (LinearMap.range f)

-- XXX: should this be about ContinuousLinearMapClass?
namespace ContinuousLinearMap.Splits

variable {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

lemma injective (h : f.Splits) : Injective f := h.1

lemma isClosed_range (h : f.Splits) : IsClosed (Set.range f) := h.2.1

lemma closedComplemented (h : f.Splits) : Submodule.ClosedComplemented (LinearMap.range f) :=
  h.2.2

/-- Choice of a closed complement of `range f` -/
def complement (h : f.Splits) : Submodule 𝕜 F :=
  Classical.choose h.closedComplemented.exists_isClosed_isCompl

lemma complement_isClosed (h : f.Splits) : IsClosed (X := F) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).1

lemma complement_isCompl (h : f.Splits) : IsCompl (LinearMap.range f) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).2

/-- TODO! add missing documentation -/
def foo (h : f.Splits) : F ≃L[𝕜] E × h.complement :=
  -- use `Submodule.ClosedComplemented.exists_submodule_equiv_prod `, or so!
  -- choose a complement E' of im f (in Lean: is h.complement)
  -- put F ≅ range f ⊕ h.complement → E ⊕ h.complement,
  -- where the last map is (f.equivImage).symm ⊕ id
  sorry

lemma foo_bar (h : f.Splits) : h.foo ∘ f = (·, 0) :=
  -- compute using the definition above... perhaps without the noncomputable?
  sorry

/-- A continuous linear equivalence splits. -/
lemma _root_.ContinuousLinearEquiv.splits (f : E ≃L[𝕜] F) : f.toContinuousLinearMap.Splits := by
  refine ⟨?_, ?_, ?_⟩
  · rw [f.coe_coe]
    apply EquivLike.injective
  · rw [f.coe_coe, EquivLike.range_eq_univ]
    exact isClosed_univ
  · erw [LinearMap.range_eq_top_of_surjective f (EquivLike.surjective f)]
    exact Submodule.closedComplemented_top

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap (hf : f.Splits) (hg : g.Splits) : (f.prodMap g).Splits := by
  refine ⟨hf.injective.prodMap hg.injective, ?_, ?_⟩
  · rw [coe_prodMap', range_prod_map]
    exact (hf.isClosed_range).prod hg.isClosed_range
  · have : LinearMap.range (f.prodMap g) = (LinearMap.range f).prod (LinearMap.range g) := by
      -- seems to be missing...
      sorry
    rw [this]
    sorry -- also missing: Submodule.ClosedComplemented.prod

-- Outline of missing ingredient:
-- Thm. X, Y Banach, f:X\to Y continuous linear. Then
-- f injective with closed range <=> \exists 0 < c, ∀ x, c|x| ≤ |f x|
-- Reduce: range (g ∘ f) below, and also g(F') below are closed:
--   (if s ⊆ G is closed, then g(s) is closed, uses injectivity and the open mapping theorem)

-- XXX: is this completeness hypothesis required?
/-- The composition of split continuous linear maps splits. -/
lemma comp [CompleteSpace G] {g : F →L[𝕜] G} (hf : f.Splits) (hg : g.Splits) : (g.comp f).Splits := by
  have h1 : IsClosed (range ⇑(g.comp f)) := sorry
  refine ⟨hg.injective.comp hf.injective, h1, ?_⟩
  · let F' := hf.complement
    let G' := hg.complement
    rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
    refine ⟨h1, (F'.map g) + G', ?_, ?_⟩
    · -- missing (also missing hypotheses?): sum of closed submodules is closed
      sorry
    · sorry

lemma compCLE_left [CompleteSpace F] {f₀ : F' ≃L[𝕜] E} (hf : f.Splits) :
    (f.comp f₀.toContinuousLinearMap).Splits :=
  f₀.splits.comp hf

lemma compCLE_right [CompleteSpace F'] {g : F ≃L[𝕜] F'} (hf : f.Splits) :
    (g.toContinuousLinearMap.comp f).Splits :=
  hf.comp g.splits

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [FiniteDimensional 𝕜 F] {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

/-- If `f : E → F` is injective and `F` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

/-- If `f : E → F` is injective, `E` is finite-dimensional and `F` is Banach, then `f` splits. -/
lemma of_injective_of_finiteDimensional_of_completeSpace
    [FiniteDimensional 𝕜 E] [CompleteSpace F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

-- If `f : E → F` is injective, `E` and `F` are Banach and `f` is Fredholm, then `f` splits.

end RCLike

end ContinuousLinearMap.Splits

end
