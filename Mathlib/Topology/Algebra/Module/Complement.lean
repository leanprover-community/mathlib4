/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sharvil Kesarwani
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Topological complements of submodules

Let `M` be a topological `R`-module. Two submodules `p, q` of `M` are said to be
*topological complements* (`Submodule.IsTopCompl`) if they are algebraic complements and the
algebraic isomorphism `M ≃ p × q` is a homeomorphism.

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
* `Submodule.projectionOntoL`: if `h : IsTopCompl p q`, `p.projectionOntoL q h` is the
  continuous linear projection `M →L[R] p` along `q`. This is the continuous version of
  `Submodule.projectionOnto`.
* `Submodule.projectionL`: if `h : IsTopCompl p q`, `p.projectionL q h` is the continuous
  linear projection `M →L[R] M` onto `p` along `q`. This is the continuous version of
  `Submodule.IsCompl.projection`.
* `Submodule.ClosedComplemented.complement`: an arbitrary topological complement of a topologically
  complemented submodule.
* `Submodule.prodEquivOfIsTopCompl`: the bundled continuous linear equivalence `p × q ≃L[R] M`
  arising from a topological complement pair.
* `Submodule.quotientEquivOfIsTopCompl`: the bundled continuous linear equivalence `M ⧸ p ≃L[R] q`
  arising from a topological complement pair.
* `ContinuousLinearMap.ofIsTopCompl`: the continuous linear map induced by maps on a topological
  complement pair.

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
  continuous_projection : Continuous (p.projection q isCompl)

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p q : Submodule R M}

section IsTopCompl

theorem IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projection q h) :=
  ⟨IsTopCompl.continuous_projection, fun h' ↦ ⟨h, h'⟩⟩

theorem IsCompl.isTopCompl_iff_projectionOnto (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projectionOnto q h) := by
  rw [h.isTopCompl_iff, IsInducing.subtypeVal.continuous_iff]
  rfl

@[deprecated (since := "2026-05-05")] alias IsCompl.isTopCompl_iff_linearProjOfIsCompl :=
  IsCompl.isTopCompl_iff_projectionOnto

theorem IsTopCompl.continuous_projectionOnto (h : IsTopCompl p q) :
    Continuous (p.projectionOnto q h.isCompl) :=
  h.isCompl.isTopCompl_iff_projectionOnto.mp h

@[deprecated (since := "2026-05-05")] alias IsTopCompl.continuous_linearProjOfIsCompl :=
  IsTopCompl.continuous_projectionOnto

protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection

open LinearMap in
theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl {f : M →L[R] M}
    (hf : IsIdempotentElem f) : IsTopCompl f.range f.ker where
  isCompl := hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_projection ▸ f.continuous

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
  ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]
theorem toLinearMap_projectionOntoL (h : IsTopCompl p q) :
    p.projectionOntoL q h = p.projectionOnto q h.isCompl :=
  rfl

@[simp]
theorem projectionOntoL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionOntoL q h x = x :=
  projectionOnto_apply_left h.isCompl x

theorem range_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).range = ⊤ := by
  simp

theorem projectionOntoL_surjective (h : IsTopCompl p q) : Surjective (p.projectionOntoL q h) :=
  projectionOnto_surjective h.isCompl

@[simp]
theorem projectionOntoL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionOntoL q h x = 0 ↔ x ∈ q :=
  projectionOnto_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff

@[simp]
theorem projectionOntoL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionOntoL q h x = 0 :=
  projectionOntoL_apply_eq_zero_of_mem_right h x.2

theorem ker_projectionOntoL (h : IsTopCompl p q) :
    (p.projectionOntoL q h).ker = q := by
  simp

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
    p.projectionL q h = p.projection q h.isCompl :=
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
  projection_apply_left h.isCompl x

theorem range_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).range = p := by
  simp

@[simp]
theorem projectionL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionL q h x = 0 ↔ x ∈ q :=
  projection_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff

@[simp]
theorem projectionL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionL q h x = 0 :=
  projectionL_apply_eq_zero_of_mem_right h x.2

theorem ker_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).ker = q := by
  simp

@[simp]
theorem isIdempotentElem_projectionL (h : IsTopCompl p q) :
    IsIdempotentElem (p.projectionL q h) := by
  simp [← isIdempotentElem_toLinearMap_iff]

theorem projectionL_add_projectionL_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x + q.projectionL p h.symm x = x :=
  projection_add_projection_eq_self h.isCompl x

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
@[simp] lemma projectionL_eq_self_iff [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = x ↔ x ∈ p :=
  projection_eq_self_iff h.isCompl x

theorem _root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL
    {f : M →L[R] M} (hf : IsIdempotentElem f) : f = f.range.projectionL f.ker hf.isTopCompl :=
  coe_inj.mp <| LinearMap.IsIdempotentElem.eq_projection hf.toLinearMap

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

section ContinuousLinearEquiv

variable [IsTopologicalAddGroup M]

/-- Two submodules `p` and `q` are topological complements if and only if the linear equivalence
`p.prodEquivOfIsCompl q h` is continuous in the inverse direction. -/
theorem IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.prodEquivOfIsCompl q h).symm :=
  ⟨fun hTop ↦ ((p.projectionOntoL q hTop).prod (q.projectionOntoL p hTop.symm)).continuous.congr
    fun x ↦ (prodEquivOfIsCompl_symm_apply h x).symm,
  fun hCont ↦ ⟨h, continuous_subtype_val.comp <| continuous_fst.comp hCont⟩⟩

/-- The algebraic equivalence `p.prodEquivOfIsCompl q h : p × q ≃ₗ[R] M` from a pair of
complementary submodules is always continuous as a map `p × q → M`. -/
theorem continuous_prodEquivOfIsCompl (h : IsCompl p q) : Continuous (p.prodEquivOfIsCompl q h) :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/-- Two submodules `p` and `q` are topological complements if and only if the linear equivalence
`p.prodEquivOfIsCompl q h` is a homeomorphism. -/
theorem IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ IsHomeomorph (p.prodEquivOfIsCompl q h) := by
  rw [(p.prodEquivOfIsCompl q h).isHomeomorph_iff,
    isTopCompl_iff_continuous_symm_prodEquivOfIsCompl, and_iff_right]
  exact continuous_prodEquivOfIsCompl h

variable (p q) in
/-- If two submodules `p` and `q` are topological complements, then the linear equivalence
`p.prodEquivOfIsCompl q h.isCompl` is a homeomorphism, bundled as a continuous linear
equivalence. -/
noncomputable def prodEquivOfIsTopCompl (h : IsTopCompl p q) : (p × q) ≃L[R] M :=
  { p.prodEquivOfIsCompl q h.isCompl with
    continuous_toFun := continuous_prodEquivOfIsCompl h.isCompl
    continuous_invFun := h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp h }

@[simp]
theorem toLinearEquiv_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    (prodEquivOfIsTopCompl p q h : (p × q) ≃ₗ[R] M) = p.prodEquivOfIsCompl q h.isCompl :=
  rfl

@[simp]
theorem prodEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : p × q) :
    prodEquivOfIsTopCompl p q h x = (x.1 : M) + x.2 :=
  rfl

@[simp]
theorem prodEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (x : M) :
    (prodEquivOfIsTopCompl p q h).symm x =
      ((p.projectionOntoL q h x, q.projectionOntoL p h.symm x) : p × q) :=
  prodEquivOfIsCompl_symm_apply h.isCompl x

/-- Two submodules `p` and `q` are topological complements if and only if the linear equivalence
`p.quotientEquivOfIsCompl q h` is continuous. -/
theorem IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.quotientEquivOfIsCompl q h) := by
  have hproj : ⇑(p.quotientEquivOfIsCompl q h) ∘ ⇑p.mkQ = ⇑(q.projectionOnto p h.symm) := by
    funext; simp
  rw [p.isQuotientMap_mkQL.continuous_iff, coe_mkQL, hproj, ← h.symm.isTopCompl_iff_projectionOnto]
  exact ⟨IsTopCompl.symm, IsTopCompl.symm⟩

variable (p q) in
/-- If two submodules `p` and `q` are topological complements, then the linear equivalence
`p.quotientEquivOfIsCompl q h.isCompl` is a homeomorphism, bundled as a continuous linear
equivalence. -/
noncomputable def quotientEquivOfIsTopCompl (h : IsTopCompl p q) : (M ⧸ p) ≃L[R] q :=
  { p.quotientEquivOfIsCompl q h.isCompl with
    continuous_toFun := h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp h
    continuous_invFun := (p.mkQL.comp q.subtypeL).continuous }

@[simp]
theorem toLinearEquiv_quotientEquivOfIsTopCompl (h : IsTopCompl p q) :
    (quotientEquivOfIsTopCompl p q h : (M ⧸ p) ≃ₗ[R] q) = p.quotientEquivOfIsCompl q h.isCompl :=
  rfl

theorem quotientEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : M ⧸ p) :
    quotientEquivOfIsTopCompl p q h x = p.quotientEquivOfIsCompl q h.isCompl x :=
  rfl

@[simp]
theorem quotientEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (y : q) :
    (quotientEquivOfIsTopCompl p q h).symm y = p.mkQ y :=
  rfl

@[simp]
theorem quotientEquivOfIsTopCompl_apply_mk (h : IsTopCompl p q) (x : M) :
    quotientEquivOfIsTopCompl p q h (Quotient.mk x) = q.projectionOnto p h.isCompl.symm x :=
  quotientEquivOfIsCompl_apply_mk h.isCompl x

end ContinuousLinearEquiv

end Submodule

namespace ContinuousLinearMap

variable {R : Type*} [Ring R] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module R E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  {p q : Submodule R E}

/-- Given continuous linear maps `φ : p →L[R] F` and `ψ : q →L[R] F` from topological complement
submodules of `E`, the induced continuous linear map `E →L[R] F`.

This is the continuous version of `LinearMap.ofIsCompl`. -/
noncomputable def ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) : E →L[R] F :=
  φ.coprod ψ ∘L ↑(prodEquivOfIsTopCompl p q h).symm

theorem ofIsTopCompl_eq_add (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    ofIsTopCompl h φ ψ = φ ∘L p.projectionOntoL q h + ψ ∘L q.projectionOntoL p h.symm := by
  ext; simp [ofIsTopCompl]

@[simp]
theorem toLinearMap_ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    (ofIsTopCompl h φ ψ : E →ₗ[R] F) = LinearMap.ofIsCompl h.isCompl φ ψ := by
  rfl

@[simp]
theorem ofIsTopCompl_apply_left (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) (x : p) :
    ofIsTopCompl h φ ψ (x : E) = φ x := by
  simp [ofIsTopCompl]

@[simp]
theorem ofIsTopCompl_apply_right (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) (x : q) :
    ofIsTopCompl h φ ψ (x : E) = ψ x := by
  simp [ofIsTopCompl]

theorem ofIsTopCompl_eq (h : IsTopCompl p q) {φ : p →L[R] F} {ψ : q →L[R] F} {χ : E →L[R] F}
    (hφ : ∀ u : p, φ u = χ u) (hψ : ∀ u : q, ψ u = χ u) : ofIsTopCompl h φ ψ = χ := by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h.isCompl x
  simp [hφ, hψ]

@[simp]
theorem ofIsTopCompl_zero (h : IsTopCompl p q) : (ofIsTopCompl h 0 0 : E →L[R] F) = 0 := by
  ext; simp [ofIsTopCompl]

@[simp]
theorem ofIsTopCompl_add (h : IsTopCompl p q) (φ₁ φ₂ : p →L[R] F) (ψ₁ ψ₂ : q →L[R] F) :
    ofIsTopCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsTopCompl h φ₁ ψ₁ + ofIsTopCompl h φ₂ ψ₂ := by
  ext; simp [ofIsTopCompl, add_add_add_comm]

theorem range_ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    LinearMap.range (ofIsTopCompl h φ ψ : E →ₗ[R] F) = φ.range ⊔ ψ.range := by simp

end ContinuousLinearMap
