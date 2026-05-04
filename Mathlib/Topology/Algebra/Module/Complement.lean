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
complements). In the literature, such a submodule is called *topologically complemented*
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
@[pp_nodot]
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

theorem IsTopCompl.continuous_linearProjOfIsCompl (h : IsTopCompl p q) :
    Continuous (p.linearProjOfIsCompl q h.isCompl) :=
  h.isCompl.isTopCompl_iff_linearProjOfIsCompl.mp h

protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [h.isCompl.projection_eq_id_sub_projection]
    exact continuous_id.sub h.continuous_projection

open LinearMap in
theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl {f : M →L[R] M}
    (hf : IsIdempotentElem f) : IsTopCompl f.range f.ker where
  isCompl := hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_isCompl_projection ▸ f.continuous

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

variable (p q) in
/-- If `h : IsTopCompl p q`, `h.projectionOnto` is the continuous linear projection `M →L[R] p`
along `q`. This is the continuous version of `Submodule.linearProjOfIsCompl`.

See also `Submodule.IsTopCompl.projection` for the same projection as an element of `M →L[R] M`. -/
noncomputable def projectionOntoL (h : IsTopCompl p q) : M →L[R] p :=
  ⟨p.linearProjOfIsCompl q h.isCompl, h.continuous_linearProjOfIsCompl⟩

@[simp]
theorem toLinearMap_projectionOntoL (h : IsTopCompl p q) :
    p.projectionOntoL q h = p.linearProjOfIsCompl q h.isCompl :=
  rfl

@[simp]
theorem projectionOntoL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionOntoL q h x = x :=
  linearProjOfIsCompl_apply_left h.isCompl x

theorem range_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).range = ⊤ :=
  linearProjOfIsCompl_range h.isCompl

theorem projectionOntoL_surjective (h : IsTopCompl p q) : Surjective (p.projectionOntoL q h) :=
  linearProjOfIsCompl_surjective h.isCompl

@[simp]
theorem projectionOntoL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionOntoL q h x = 0 ↔ x ∈ q :=
  linearProjOfIsCompl_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff

@[simp]
theorem projectionOntoL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionOntoL q h x = 0 :=
  projectionOntoL_apply_eq_zero_of_mem_right h x.2

theorem ker_projectionOntoL (h : IsTopCompl p q) :
    (p.projectionOntoL q h).ker = q :=
  linearProjOfIsCompl_ker h.isCompl

theorem isQuotientMap_projectionOntoL (h : IsTopCompl p q) :
    IsQuotientMap (p.projectionOntoL q h) :=
  .of_inverse continuous_subtype_val (p.projectionOntoL q h).continuous
    (projectionOntoL_apply_left h)

end projectionOnto

section projection

variable (p q) in
/-- If `h : IsTopCompl p q`, `h.projection` is the continuous linear projection `M →L[R] M` onto
`p` along `q`. This is the continuous version of `Submodule.IsCompl.projection`.

See also `Submodule.IsTopCompl.projectionOnto` for the same projection as an element of
`M →L[R] p`. -/
noncomputable def projectionL (h : IsTopCompl p q) : M →L[R] M :=
  p.subtypeL ∘L p.projectionOntoL q h

@[simp]
theorem toLinearMap_projectionL (h : IsTopCompl p q) :
    p.projectionL q h = h.isCompl.projection :=
  rfl

theorem projectionL_apply (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = p.projectionOntoL q h x :=
  rfl

@[simp]
theorem coe_projectionOntoL_apply (h : IsTopCompl p q) (x : M) :
    (p.projectionOntoL q h x : M) = p.projectionL q h x :=
  rfl

@[simp]
theorem projectionL_apply_mem (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x ∈ p :=
  SetLike.coe_mem _

@[simp]
theorem projectionL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionL q h x = x :=
  h.isCompl.projection_apply_left x

theorem range_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).range = p :=
  h.isCompl.projection_range

@[simp]
theorem projectionL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionL q h x = 0 ↔ x ∈ q :=
  h.isCompl.projection_apply_eq_zero_iff

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff

@[simp]
theorem projectionL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionL q h x = 0 :=
  projectionL_apply_eq_zero_of_mem_right h x.2

theorem ker_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).ker = q :=
  h.isCompl.projection_ker

@[simp]
theorem isIdempotentElem_projectionL (h : IsTopCompl p q) :
    IsIdempotentElem (p.projectionL q h) := by
  simp [← isIdempotentElem_toLinearMap_iff]

theorem projectionL_add_projectionL_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x + q.projectionL p h.symm x = x :=
  h.isCompl.projection_add_projection_eq_self x

theorem projectionL_add_projectionL_eq_id [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    p.projectionL q h + q.projectionL p h.symm = .id R M :=
  ContinuousLinearMap.ext <| projectionL_add_projectionL_eq_self h

lemma projectionL_eq_self_sub_projectionL [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    q.projectionL p h.symm x = x - p.projectionL q h x := by
  rw [eq_sub_iff_add_eq, projectionL_add_projectionL_eq_self]

lemma projectionL_eq_id_sub_projectionL [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    q.projectionL p h.symm = .id R M - p.projectionL q h :=
  ContinuousLinearMap.ext <| projectionL_eq_self_sub_projectionL h

/-- The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`. -/
@[simp] lemma projection_eq_self_iff [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = x ↔ x ∈ p :=
  h.isCompl.projection_eq_self_iff x

theorem _root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL
    {f : M →L[R] M} (hf : IsIdempotentElem f) : f = f.range.projectionL f.ker hf.isTopCompl :=
  coe_inj.mp <| LinearMap.IsIdempotentElem.eq_isCompl_projection hf.toLinearMap

theorem _root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker
    {f : M →L[R] M} : IsIdempotentElem f ↔
      ∃ h : IsTopCompl f.range f.ker, f = f.range.projectionL f.ker h :=
  ⟨fun h ↦ ⟨_, h.eq_projectionL⟩, fun ⟨hf, h⟩ ↦ h.symm ▸ isIdempotentElem_projectionL hf⟩

end projection

section closed_hausdorff

theorem IsTopCompl.closedComplemented (h : IsTopCompl p q) : ClosedComplemented p :=
  ⟨p.projectionOntoL q h, projectionOntoL_apply_left h⟩

/-- A variant of `Submodule.IsTopCompl.isClosed`. This has the very mild advantage over
`h.symm.isClosed` that it doesn't assume `ContinuousSub M`. -/
theorem IsTopCompl.isClosed' [T1Space p] (h : IsTopCompl p q) : IsClosed (q : Set M) := by
  rw [← ker_projectionOntoL h]
  exact isClosed_ker _

/-- If `p` and `q` are topological complements and `q` is Hausdorff, then `p` is closed. -/
protected theorem IsTopCompl.isClosed [T1Space q] [ContinuousSub M] (h : IsTopCompl p q) :
    IsClosed (p : Set M) :=
  h.symm.isClosed'

protected theorem IsTopCompl.t3Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T3Space p := by
  have : IsClosed ({0} : Set p) := by
    rw [← (isQuotientMap_projectionOntoL h).isClosed_preimage]
    rwa [← ker_projectionOntoL h] at hq
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
