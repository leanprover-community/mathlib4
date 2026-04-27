/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth, Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# TODO
-/

@[expose] public section

open LinearMap (ker range)
open Topology ContinuousLinearMap Function

namespace Submodule

variable {R : Type*} [Ring R] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open ContinuousLinearMap

/-- Two submodules `p` and `q` are *topological complements* if they are algebraic complements and
the projection on `p` parallel to `q` is continuous -/
structure IsTopCompl (p q : Submodule R M) : Prop where
  isCompl : IsCompl p q
  continuous_projection : Continuous (IsCompl.projection isCompl)

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p q : Submodule R M}

section IsTopCompl

theorem _root_.IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (IsCompl.projection h) :=
  ⟨IsTopCompl.continuous_projection, fun h' ↦ ⟨h, h'⟩⟩

protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [IsCompl.projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection

theorem _root_.IsIdempotentElem.isTopCompl {f : M →L[R] M} (hf : IsIdempotentElem f) :
    IsTopCompl f.range f.ker := by
  rw [← isIdempotentElem_toLinearMap_iff] at hf
  refine ⟨LinearMap.IsIdempotentElem.isCompl hf, ?_⟩
  rw [← LinearMap.IsIdempotentElem.eq_isCompl_projection hf]
  exact f.continuous

theorem isTopCompl_bot_top :
    IsTopCompl (⊥ : Submodule R M) ⊤ := by
  have : IsIdempotentElem (0 : M →L[R] M) := .zero
  simpa using this.isTopCompl

theorem isTopCompl_top_bot :
    IsTopCompl (⊤ : Submodule R M) ⊥ := by
  have : IsIdempotentElem (.id R M : M →L[R] M) := .one
  simpa using this.isTopCompl

open LinearMap in
theorem _root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.IsTopCompl f₂.ker :=
  let p := f₁ ∘L f₂
  have p_idem : IsIdempotentElem p := by ext x; simp [p, h (f₂ x)]
  have range_p : p.range = f₁.range := range_comp_of_range_eq_top _ <|
    range_eq_top_of_surjective _ h.surjective
  have ker_p : p.ker = f₂.ker := ker_comp_of_ker_eq_bot _ <|
    ker_eq_bot_of_injective h.injective
  range_p ▸ ker_p ▸ p_idem.isTopCompl

theorem _root_.ContinuousLinearMap.isTopCompl_of_proj {f : M →L[R] p} (hf : ∀ x : p, f x = x) :
    IsTopCompl p f.ker := by
  simpa using p.subtypeL.isTopCompl_range_ker_of_leftInverse f hf

section projectionOnto

protected noncomputable def IsTopCompl.projectionOnto (h : IsTopCompl p q) : M →L[R] p :=
  ⟨p.linearProjOfIsCompl q h.isCompl, by
    rw [IsInducing.subtypeVal.continuous_iff]
    exact h.continuous_projection⟩

@[simp]
theorem IsTopCompl.projectionOnto_toLinearMap (h : IsTopCompl p q) :
    (h.projectionOnto : M →ₗ[R] p) = p.linearProjOfIsCompl q h.isCompl :=
  rfl

@[simp]
theorem IsTopCompl.projectionOnto_apply_left (h : IsTopCompl p q) (x : p) :
    h.projectionOnto x = x :=
  linearProjOfIsCompl_apply_left h.isCompl x

@[simp]
theorem IsTopCompl.range_projectionOnto (h : IsTopCompl p q) : h.projectionOnto.range = ⊤ :=
  linearProjOfIsCompl_range h.isCompl

theorem IsTopCompl.projectionOnto_surjective (h : IsTopCompl p q) : Surjective h.projectionOnto :=
  linearProjOfIsCompl_surjective h.isCompl

@[simp]
theorem IsTopCompl.projectionOnto_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    h.projectionOnto x = 0 ↔ x ∈ q :=
  linearProjOfIsCompl_apply_eq_zero_iff h.isCompl

alias ⟨_, IsTopCompl.projectionOnto_apply_eq_zero_of_mem_right⟩ :=
  IsTopCompl.projectionOnto_apply_eq_zero_iff

@[simp]
theorem IsTopCompl.projectionOnto_apply_right (h : IsTopCompl p q) (x : q) :
    h.projectionOnto x = 0 :=
  h.projectionOnto_apply_eq_zero_of_mem_right x.2

theorem IsTopCompl.ker_projectionOnto (h : IsTopCompl p q) :
    ker (h.projectionOnto : M →ₗ[R] p) = q :=
  linearProjOfIsCompl_ker h.isCompl

theorem IsTopCompl.isQuotientMap_projectionOnto (h : IsTopCompl p q) :
    IsQuotientMap h.projectionOnto :=
  .of_inverse continuous_subtype_val h.projectionOnto.continuous h.projectionOnto_apply_left

-- TODO: more API

end projectionOnto

section projection

protected noncomputable def IsTopCompl.projection (h : IsTopCompl p q) : M →L[R] M :=
  p.subtypeL ∘L h.projectionOnto

@[simp]
theorem IsTopCompl.projection_toLinearMap (h : IsTopCompl p q) :
    (h.projection : M →ₗ[R] M) = IsCompl.projection h.isCompl :=
  rfl

theorem IsTopCompl.projection_apply (h : IsTopCompl p q) (x : M) :
    h.projection x = h.projectionOnto x :=
  rfl

@[simp]
theorem IsTopCompl.coe_projectionOnto_apply (h : IsTopCompl p q) (x : M) :
    (h.projectionOnto x : M) = h.projection x :=
  rfl

@[simp]
theorem IsTopCompl.projection_apply_mem (h : IsTopCompl p q) (x : M) :
    h.projection x ∈ p :=
  SetLike.coe_mem _

@[simp]
theorem IsTopCompl.projection_apply_left (h : IsTopCompl p q) (x : p) :
    h.projection x = x :=
  IsCompl.projection_apply_left h.isCompl x

@[simp]
theorem IsTopCompl.range_projection (h : IsTopCompl p q) :
    h.projection.range = p :=
  IsCompl.projection_range h.isCompl

@[simp]
theorem IsTopCompl.projection_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    h.projection x = 0 ↔ x ∈ q :=
  IsCompl.projection_apply_eq_zero_iff h.isCompl

alias ⟨_, IsTopCompl.projection_apply_eq_zero_of_mem_right⟩ :=
  IsTopCompl.projection_apply_eq_zero_iff

@[simp]
theorem IsTopCompl.projection_apply_right (h : IsTopCompl p q) (x : q) :
    h.projection x = 0 :=
  h.projection_apply_eq_zero_of_mem_right x.2

@[simp]
theorem IsTopCompl.projection_isIdempotentElem (h : IsTopCompl p q) :
    IsIdempotentElem h.projection := by
  simp [← isIdempotentElem_toLinearMap_iff]

theorem IsTopCompl.projection_add_projection_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    h.projection x + h.symm.projection x = x :=
  IsCompl.projection_add_projection_eq_self h.isCompl x

theorem IsTopCompl.projection_add_projection_eq_id [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    h.projection + h.symm.projection = .id R M := by
  ext
  apply h.projection_add_projection_eq_self

lemma IsTopCompl.projection_eq_self_sub_projection [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    h.symm.projection x = x - h.projection x := by
  rw [eq_sub_iff_add_eq, projection_add_projection_eq_self]

lemma IsTopCompl.projection_eq_id_sub_projection [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    h.symm.projection = .id R M - h.projection := by
  ext
  apply h.projection_eq_self_sub_projection

/-- The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`. -/
@[simp] lemma IsTopCompl.projection_eq_self_iff [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    h.projection x = x ↔ x ∈ p :=
  IsCompl.projection_eq_self_iff h.isCompl x

end projection

section closed_hausdorff

theorem IsTopCompl.closedComplemented (h : IsTopCompl p q) : ClosedComplemented p :=
  ⟨h.projectionOnto, h.projectionOnto_apply_left⟩

/-- A variant of `Submodule.IsTopCompl.isClosed`. This has the very mild advantage over
`h.symm.isClosed` that it doesn't assume `ContinuousSub M`. -/
theorem IsTopCompl.isClosed' [T1Space p] (h : IsTopCompl p q) : IsClosed (q : Set M) := by
  rw [← ker_projectionOnto h]
  exact isClosed_ker _

protected theorem IsTopCompl.isClosed [T1Space q] [ContinuousSub M] (h : IsTopCompl p q) :
    IsClosed (p : Set M) :=
  h.symm.isClosed'

protected theorem IsTopCompl.t3Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T3Space p := by
  have : IsClosed ({0} : Set p) := by
    rw [← h.isQuotientMap_projectionOnto.isClosed_preimage]
    rwa [← h.ker_projectionOnto] at hq
  have : T1Space p := IsTopologicalAddGroup.t1Space _ this
  rw [RegularSpace.t3Space_iff_t0Space]
  infer_instance

protected theorem IsTopCompl.t2Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T2Space p :=
  have := h.t3Space hq
  inferInstance

end closed_hausdorff

end IsTopCompl

section ClosedComplemented

theorem ClosedComplemented.exists_isTopCompl (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsTopCompl p q :=
  Exists.elim h fun f hf => ⟨_, f.isTopCompl_of_proj hf⟩

theorem closedComplemented_iff_exists_isTopCompl :
    ClosedComplemented p ↔ ∃ q, IsTopCompl p q :=
  ⟨ClosedComplemented.exists_isTopCompl, fun H ↦ H.elim fun _ hq ↦ hq.closedComplemented⟩

@[deprecated ClosedComplemented.exists_isTopCompl (since := "2026-04-27")]
theorem ClosedComplemented.exists_isClosed_isCompl [T1Space p] (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

/-- An arbitrary choice of topological complement of a closed complemented submodule. -/
noncomputable def ClosedComplemented.complement (h : ClosedComplemented p) : Submodule R M :=
  Classical.choose h.exists_isTopCompl

theorem ClosedComplemented.isTopCompl_complement (h : ClosedComplemented p) :
    IsTopCompl p h.complement :=
  Classical.choose_spec h.exists_isTopCompl

theorem ClosedComplemented.isCompl_complement (h : ClosedComplemented p) : IsCompl p h.complement :=
  h.isTopCompl_complement.isCompl

theorem ClosedComplemented.isClosed_complement [T1Space p] (h : ClosedComplemented p) :
    IsClosed (h.complement : Set M) :=
  h.isTopCompl_complement.isClosed'

protected theorem ClosedComplemented.isClosed [ContinuousSub M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) :=
  h.isTopCompl_complement.isClosed

@[simp]
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  isTopCompl_bot_top.closedComplemented

@[simp]
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  isTopCompl_top_bot.closedComplemented

theorem _root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.ClosedComplemented :=
  f₁.isTopCompl_range_ker_of_leftInverse f₂ h |>.closedComplemented

theorem _root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse [ContinuousSub M]
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.RightInverse f₂ f₁) :
    f₁.ker.ClosedComplemented :=
  f₂.isTopCompl_range_ker_of_leftInverse f₁ h.leftInverse |>.symm.closedComplemented

end ClosedComplemented

end Submodule
