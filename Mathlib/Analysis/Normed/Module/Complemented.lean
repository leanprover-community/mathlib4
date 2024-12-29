/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Complemented subspaces of normed vector spaces

A submodule `p` of a topological module `E` over `R` is called *complemented* if there exists
a continuous linear projection `f : E →ₗ[R] p`, `∀ x : p, f x = x`. We prove that for
a closed subspace of a normed space this condition is equivalent to existence of a closed
subspace `q` such that `p ⊓ q = ⊥`, `p ⊔ q = ⊤`. We also prove that a subspace of finite codimension
is always a complemented subspace.

## Tags

complemented subspace, normed vector space
-/


variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

open LinearMap (ker range)

namespace ContinuousLinearMap

section

variable [CompleteSpace 𝕜]

theorem ker_closedComplemented_of_finiteDimensional_range (f : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (range f)] : (ker f).ClosedComplemented := by
  set f' : E →L[𝕜] range f := f.codRestrict _ (LinearMap.mem_range_self (f : E →ₗ[𝕜] F))
  rcases f'.exists_right_inverse_of_surjective (f : E →ₗ[𝕜] F).range_rangeRestrict with ⟨g, hg⟩
  simpa only [f', ker_codRestrict]
    using f'.closedComplemented_ker_of_rightInverse g (ContinuousLinearMap.ext_iff.1 hg)

end

variable [CompleteSpace E] [CompleteSpace (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
nonrec def equivProdOfSurjectiveOfIsCompl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃L[𝕜] F × G :=
  (f.equivProdOfSurjectiveOfIsCompl (g : E →ₗ[𝕜] G) hf hg hfg).toContinuousLinearEquivOfContinuous
    (f.continuous.prod_mk g.continuous)

@[simp]
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.prod g := rfl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_toLinearEquiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv =
      LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg := rfl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end ContinuousLinearMap

namespace Submodule

variable [CompleteSpace E] (p q : Subspace 𝕜 E)

/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E := by
  haveI := hp.completeSpace_coe; haveI := hq.completeSpace_coe
  refine (p.prodEquivOfIsCompl q h).toContinuousLinearEquivOfContinuous ?_
  exact (p.subtypeL.coprod q.subtypeL).continuous

/-- Projection to a closed submodule along a closed complement. -/
def linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L ↑(prodEquivOfClosedCompl p q h hp hq).symm

def idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] E :=
  ↑(prodEquivOfClosedCompl p q h hp hq) ∘L (ContinuousLinearMap.inl 𝕜 p q ∘L
    (linearProjOfClosedCompl p q h hp hq))




/-

-/

variable {p q}

@[simp]
theorem coe_prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquivOfIsCompl q h := rfl

@[simp]
theorem coe_prodEquivOfClosedCompl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (p.prodEquivOfIsCompl q h).symm := rfl

@[simp]
theorem coe_continuous_linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    (p.linearProjOfClosedCompl q h hp hq : E →ₗ[𝕜] p) = p.linearProjOfIsCompl q h := rfl

@[simp]
theorem coe_continuous_linearProjOfClosedCompl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.linearProjOfClosedCompl q h hp hq) = p.linearProjOfIsCompl q h := rfl

theorem ClosedComplemented.of_isCompl_isClosed (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  ⟨p.linearProjOfClosedCompl q h hp hq, Submodule.linearProjOfIsCompl_apply_left h⟩

alias IsCompl.closedComplemented_of_isClosed := ClosedComplemented.of_isCompl_isClosed

theorem closedComplemented_iff_isClosed_exists_isClosed_isCompl :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ q : Submodule 𝕜 E, IsClosed (q : Set E) ∧ IsCompl p q :=
  ⟨fun h => ⟨h.isClosed, h.exists_isClosed_isCompl⟩,
    fun ⟨hp, ⟨_, hq, hpq⟩⟩ => .of_isCompl_isClosed hpq hp hq⟩

theorem ClosedComplemented.of_quotient_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 (E ⧸ p)] (hp : IsClosed (p : Set E)) : p.ClosedComplemented := by
  obtain ⟨q, hq⟩ : ∃ q, IsCompl p q := p.exists_isCompl
  haveI : FiniteDimensional 𝕜 q := (p.quotientEquivOfIsCompl q hq).finiteDimensional
  exact .of_isCompl_isClosed hq hp q.closed_of_finiteDimensional

lemma ker_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : LinearMap.ker (idempotentOfClosedCompl p q h hp hq) = q := by
  rw [idempotentOfClosedCompl]
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    coe_prodEquivOfClosedCompl, coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
    ContinuousLinearMap.inl_apply, coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero,
    ZeroMemClass.coe_eq_zero, linearProjOfIsCompl_apply_eq_zero_iff]

lemma xinv (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) {x : E} : x ∈ p ↔ (idempotentOfClosedCompl p q h hp hq) x = x := by
  constructor
  · intro hx
    simp only [idempotentOfClosedCompl, ContinuousLinearMap.coe_comp',
      ContinuousLinearEquiv.coe_coe, coe_prodEquivOfClosedCompl,
      coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
      (linearProjOfIsCompl_apply_left h ⟨x,hx⟩), ContinuousLinearMap.inl_apply,
      coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  · intro hx
    rw [idempotentOfClosedCompl] at hx
    simp at hx
    rw [← hx]
    exact coe_mem ((linearProjOfIsCompl p q h) x)

lemma yinv (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) {y : E} : y ∈ q ↔ (idempotentOfClosedCompl p q h hp hq) y = 0 := by
  constructor
  · intro h
    rw [idempotentOfClosedCompl]
    simp?
    exact h
  · intro h
    rw [idempotentOfClosedCompl] at h
    simp at h
    exact h

lemma range_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : LinearMap.range (idempotentOfClosedCompl p q h hp hq) = p := by
  ext x
  constructor
  · rw [idempotentOfClosedCompl]
    intro hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact coe_mem ((linearProjOfIsCompl p q h) y)
  · intro hx
    exact LinearMap.mem_range.mp ⟨x,(xinv h hp hq).mp hx⟩


#check sub_eq_zero

lemma ker_id_sub_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    LinearMap.ker ((1 : E →L[𝕜] E) - (idempotentOfClosedCompl p q h hp hq)) = p := by
  ext x
  simp
  constructor
  · rw [idempotentOfClosedCompl]
    intro hx
    simp at hx
    rw [sub_eq_zero] at hx
    rw [hx]
    exact coe_mem ((linearProjOfIsCompl p q h) x)
  · intro hx
    exact sub_eq_zero.mpr ((xinv h hp hq).mp hx).symm


lemma range_id_sub_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    LinearMap.range ((1 : E →L[𝕜] E) - (idempotentOfClosedCompl p q h hp hq)) = q := by
  rw [idempotentOfClosedCompl]
  ext x
  constructor
  · intro hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    sorry
  · intro hx
    simp
    use x
    simp
    exact hx



lemma is_idempotent_ofClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : IsIdempotentElem (idempotentOfClosedCompl p q h hp hq) := by
  rw [IsIdempotentElem]
  ext x

  rw [idempotentOfClosedCompl]

end Submodule
