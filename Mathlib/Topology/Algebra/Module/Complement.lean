/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Topological complements of submodules

Let `M` be a topological `R`-module. Two submodules `p, q` of `M` are said to be
*topological complements* (`Submodule.IsTopCompl`) if they are algebraic complements and the
algebraic isomorphism `M ≃ p × q` is an homeomorphism.

Not all submodules of `M` admit such a topological complements (even if they admit algebraic
complements). In the litterature, such a submodule is called *topologically complemented*
or *direct*. One may also find the terminology *closed complemented* because,
in a Banach space, a closed algebraic complement is automatically a topological complement.
This is the terminology we use for now (`Submodule.ClosedComplemented`), but we should eventually
change to something less misleading.

## Main definitions

* `Submodule.IsTopCompl`: we say that two submodules are *topological complements* if they are
  algebraic complements and the projection on `p` along `q` is continuous. This is equivalent
  to the definition given above.
* `Submodule.ClosedComplemented`: we say that a submodule is (topologically) *complemented* if
  there exists a continuous projection `M →ₗ[R] p`.
* `Submodule.IsTopCompl.projectionOnto`: if `h : IsTopCompl p q`, `h.projectionOnto` is the
  continuous linear projection `M →L[R] p` along `q`. This is the continuous version of
  `Submodule.linearProjOfIsCompl`.
* `Submodule.IsTopCompl.projection`: if `h : IsTopCompl p q`, `h.projection` is the continuous
  linear projection `M →L[R] M` onto `p` along `q`. This is the continuous version of
  `Submodule.IsCompl.projection`.
* `Submodule.ClosedComplemented.complement`: an arbitrary topological complement of a topologically
  complemented submodule.

## Main statements

* `IsIdempotentElem.isTopCompl`: the range and kernel of a continuous projection are topological
  complements.
* `Submodule.IsTopCompl.isClosed`: if `p` and `q` are topological complements in a Hausdorff space,
  they are closed.

## Implementation details

In the definition of `Submodule.IsTopCompl`, we choose to ask for the continuity of the projection
on the left submdule along the right one, because it is a simpler map to work with than the
map `M ≃ p × q`.

Because the condition is symmetric, a lot of lemmas could have a left and a right variation.
In general we only include the left version, the right one being accessible through
`Submodule.IsTopCompl.symm`.

## TODO

There is still a significant part of the algebraic API which should be ported to the
topological setting. Notably, we should:
* show that `Submodule.prodEquivOfIsCompl` is an homeomorphism if and only if
  the two subspaces are topological complements, and bundle it as a `ContinuousLinearEquiv` when
  this is the case. (See the existing `ClosedComplemented.exists_submodule_equiv_prod`).
* show that `Submodule.quotientEquivOfIsCompl` is an homeomorphism if and only if
  the two subspaces are topological complements, and bundle it as a `ContinuousLinearEquiv` when
  this is the case.
* define `ContinuousLinearMap.ofIsTopCompl`, analogous to `LinearMap.ofIsCompl`.

-/

@[expose] public section

open LinearMap (ker range)
open Topology ContinuousLinearMap Function Submodule

namespace Submodule

variable {R : Type*} [Ring R] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open ContinuousLinearMap

/-- Two submodules `p` and `q` are *topological complements* if they are algebraic complements and
the projection on `p` along `q` is continuous. -/
structure IsTopCompl (p q : Submodule R M) : Prop where
  isCompl : IsCompl p q
  continuous_projection : Continuous isCompl.projection

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p q : Submodule R M}

section IsTopCompl

theorem IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous h.projection :=
  ⟨IsTopCompl.continuous_projection, fun h' ↦ ⟨h, h'⟩⟩

theorem IsCompl.isTopCompl_iff_linearProjOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.linearProjOfIsCompl q h) := by
  rw [h.isTopCompl_iff, IsInducing.subtypeVal.continuous_iff]
  rfl

protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [h.isCompl.projection_eq_id_sub_projection]
    exact continuous_id.sub h.continuous_projection

theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl {f : M →L[R] M}
    (hf : IsIdempotentElem f) :
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

/-- If `h : IsTopCompl p q`, `h.projectionOnto` is the continuous linear projection `M →L[R] p`
along `q`. This is the continuous version of `Submodule.linearProjOfIsCompl`.

See also `Submodule.IsTopCompl.projection` for the same projection as an element of `M →L[R] M`. -/
protected noncomputable def IsTopCompl.projectionOnto (h : IsTopCompl p q) : M →L[R] p :=
  ⟨p.linearProjOfIsCompl q h.isCompl, by
    rw [IsInducing.subtypeVal.continuous_iff]
    exact h.continuous_projection⟩

@[simp]
theorem IsTopCompl.toLinearMap_projectionOnto (h : IsTopCompl p q) :
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

@[simp]
theorem IsTopCompl.ker_projectionOnto (h : IsTopCompl p q) :
    ker (h.projectionOnto : M →ₗ[R] p) = q :=
  linearProjOfIsCompl_ker h.isCompl

theorem IsTopCompl.isQuotientMap_projectionOnto (h : IsTopCompl p q) :
    IsQuotientMap h.projectionOnto :=
  .of_inverse continuous_subtype_val h.projectionOnto.continuous h.projectionOnto_apply_left

end projectionOnto

section projection

/-- If `h : IsTopCompl p q`, `h.projection` is the continuous linear projection `M →L[R] M` onto
`p` along `q`. This is the continuous version of `Submodule.IsCompl.projection`.

See also `Submodule.IsTopCompl.projectionOnto` for the same projection as an element of
`M →L[R] p`. -/
protected noncomputable def IsTopCompl.projection (h : IsTopCompl p q) : M →L[R] M :=
  p.subtypeL ∘L h.projectionOnto

@[simp]
theorem IsTopCompl.toLinearMap_projection (h : IsTopCompl p q) :
    (h.projection : M →ₗ[R] M) = h.isCompl.projection :=
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
  h.isCompl.projection_apply_left x

@[simp]
theorem IsTopCompl.range_projection (h : IsTopCompl p q) :
    h.projection.range = p :=
  h.isCompl.projection_range

@[simp]
theorem IsTopCompl.projection_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    h.projection x = 0 ↔ x ∈ q :=
  h.isCompl.projection_apply_eq_zero_iff

alias ⟨_, IsTopCompl.projection_apply_eq_zero_of_mem_right⟩ :=
  IsTopCompl.projection_apply_eq_zero_iff

@[simp]
theorem IsTopCompl.projection_apply_right (h : IsTopCompl p q) (x : q) :
    h.projection x = 0 :=
  h.projection_apply_eq_zero_of_mem_right x.2

@[simp]
theorem IsTopCompl.ker_projection (h : IsTopCompl p q) :
    ker (h.projection : M →ₗ[R] M) = q :=
  h.isCompl.projection_ker

@[simp]
theorem IsTopCompl.isIdempotentElem_projection (h : IsTopCompl p q) :
    IsIdempotentElem h.projection := by
  simp [← isIdempotentElem_toLinearMap_iff]

theorem IsTopCompl.projection_add_projection_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    h.projection x + h.symm.projection x = x :=
  h.isCompl.projection_add_projection_eq_self x

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
  h.isCompl.projection_eq_self_iff x

end projection

section closed_hausdorff

theorem IsTopCompl.closedComplemented (h : IsTopCompl p q) : ClosedComplemented p :=
  ⟨h.projectionOnto, h.projectionOnto_apply_left⟩

/-- A variant of `Submodule.IsTopCompl.isClosed`. This has the very mild advantage over
`h.symm.isClosed` that it doesn't assume `ContinuousSub M`. -/
theorem IsTopCompl.isClosed' [T1Space p] (h : IsTopCompl p q) : IsClosed (q : Set M) := by
  rw [← ker_projectionOnto h]
  exact isClosed_ker _

/-- If `p` and `q` are topological complements and `q` is Hausdorff, then `p` is closed. -/
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

/-- If `p` and `q` are topological complements and `q` is closed, then `p` is Hausdorff. -/
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

theorem ClosedComplemented.exists_isClosed_isCompl [T1Space p] (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

/-- An arbitrary choice of topological complement of a topologically complemented submodule. -/
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

/-- If `p` is a closed complemented submodule,
then there exists a submodule `q` and a continuous linear equivalence `M ≃L[R] (p × q)` such that
`e (x : p) = (x, 0)`, `e (y : q) = (0, y)`, and `e.symm x = x.1 + x.2`.

In fact, the properties of `e` imply the properties of `e.symm` and vice versa,
but we provide both for convenience. -/
lemma ClosedComplemented.exists_submodule_equiv_prod [IsTopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    ∃ (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (∀ x : p, e x = (x, 0)) ∧ (∀ y : q, e y = (0, y)) ∧ (∀ x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ ↦ by ext <;> simp [hf], fun _ ↦ by ext <;> simp, fun _ ↦ rfl⟩

end ClosedComplemented

end Submodule
