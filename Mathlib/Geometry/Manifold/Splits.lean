/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-! # Linear maps which split

TODO: better doc-string, move this to a better place


-/

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

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
lemma prodMap (h : f.Splits) (h' : g.Splits) : (f.prodMap g).Splits := by
  refine ⟨h.injective.prodMap h'.injective, ?_, ?_⟩
  · rw [coe_prodMap', range_prod_map]
    exact (h.isClosed_range).prod h'.isClosed_range
  · have : LinearMap.range (f.prodMap g) = (LinearMap.range f).prod (LinearMap.range g) := by
      -- seems to be missing...
      sorry
    rw [this]
    sorry -- also missing: Submodule.ClosedComplemented.prod

lemma of_injective_of_findim [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
  refine ⟨hf, ?_, ?_⟩
  · sorry
  · sorry -- apply Submodule.ClosedComplemented.of_finiteDimensional (range f)

end ContinuousLinearMap.Splits

end
