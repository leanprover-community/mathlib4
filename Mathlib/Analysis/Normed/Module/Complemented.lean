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

open LinearMap (ker range)

namespace IsIdempotentElem

lemma ker_id_sub_eq_range {P : E →ₗ[𝕜] E} (h : IsIdempotentElem P) : ker (1 - P) = range P :=
  (Submodule.toAddSubgroup_inj (ker (1 - P)) (range P)).mp (by
  rw [LinearMap.range_toAddSubgroup, ← AddMonoid.End.ker_id_sub_eq_range (by
    rw [IsIdempotentElem]
    conv_rhs => rw [← h]
    rfl)]
  rfl)

lemma range_id_sub_eq_ker {P : E →ₗ[𝕜] E} (h : IsIdempotentElem P) : range (1 - P) = ker P := by
  rw [← (ker_id_sub_eq_range (IsIdempotentElem.one_sub h)), sub_sub_cancel]

end IsIdempotentElem

lemma continuous_isIdempotent_iff_linear_isIdempotent {P : E →L[𝕜] E} :
    IsIdempotentElem P ↔ IsIdempotentElem (P : E →ₗ[𝕜] E) := by
  constructor
  · intro h
    rw [IsIdempotentElem]
    conv_rhs => rw [← h]
    rfl
  · intro h
    apply (P*P).coe_injective
    rw [← h]
    rfl

@[simp]
lemma continuous_ker_eq_linear_ker {P : E →L[𝕜] E} : ker (P : E →ₗ[𝕜] E) = ker P := rfl

@[simp]
lemma continuous_range_eq_linear_range {P : E →L[𝕜] E} : range (P : E →ₗ[𝕜] E) = range P  := rfl

lemma IsIdempotentElem.ker_id_sub_eq_range_cont {P : E →L[𝕜] E} (h : IsIdempotentElem P) :
    ker (1 - P) = range P := by
  rw [← continuous_ker_eq_linear_ker, ← continuous_range_eq_linear_range,
    ← (continuous_isIdempotent_iff_linear_isIdempotent.mp h).ker_id_sub_eq_range]
  rfl

lemma IsIdempotentElem.range_id_sub_eq_ker_cont {P : E →L[𝕜] E} (h : IsIdempotentElem P) :
    range (1 - P) = ker P := by
  rw [← (ker_id_sub_eq_range_cont (IsIdempotentElem.one_sub h)), sub_sub_cancel]

noncomputable section

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

variable (p q)

/-- Idempotent corresponding to a complemented subspace. -/
def idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] E :=
  p.subtypeL ∘L p.linearProjOfClosedCompl q h hp hq

variable {p q}

-- x ∈ p ↔ P x = x where P := idempotentOfClosedCompl p q h hp hq
lemma mem_iff_invariant_ofClosedCompl  (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) {x : E} :
    x ∈ p ↔ p.idempotentOfClosedCompl q h hp hq x = x := by
  constructor
  · intro hx
    simp only [idempotentOfClosedCompl, ContinuousLinearMap.coe_comp', coe_subtypeL', coe_subtype,
      coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
      (linearProjOfIsCompl_apply_left h ⟨x, hx⟩)]
  · intro hx
    simp [idempotentOfClosedCompl] at hx
    rw [← hx]
    exact coe_mem ((p.linearProjOfIsCompl q h) x)

-- y ∈ q ↔ P y = 0 where P := idempotentOfClosedCompl p q h hp hq
lemma mem_iff_zero_ofClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) {y : E} :
    y ∈ q ↔ p.idempotentOfClosedCompl q h hp hq y = 0 := by
  constructor
  · intro hy
    simp only [idempotentOfClosedCompl, ContinuousLinearMap.coe_comp', coe_subtypeL', coe_subtype,
      coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
      ((linearProjOfIsCompl_apply_eq_zero_iff h).mpr hy), ZeroMemClass.coe_zero]
  · intro h
    rw [idempotentOfClosedCompl] at h
    simp at h
    exact h



-- P is an idempotent where P := idempotentOfClosedCompl p q h hp hq
lemma is_idempotent_ofClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    IsIdempotentElem (p.idempotentOfClosedCompl q h hp hq) := by
  ext z
  have hy1 : z ∈ p ⊔ q := by
    rw [h.sup_eq_top]
    exact AddSubgroup.mem_top z
  obtain ⟨x₁,⟨hx₁,⟨y₁,⟨hy₁,hx₁y₁y⟩⟩⟩⟩ := Submodule.mem_sup.mp hy1
  rw [← hx₁y₁y, map_add, map_add, ((mem_iff_zero_ofClosedCompl h hp hq).mp hy₁),
    ((mem_iff_invariant_ofClosedCompl h hp hq).mp hx₁), add_zero,
    ContinuousLinearMap.coe_mul, Function.comp_apply, Function.comp_apply,
    ((mem_iff_zero_ofClosedCompl h hp hq).mp hy₁),
    ((mem_iff_invariant_ofClosedCompl h hp hq).mp hx₁),
    map_zero, add_zero, (mem_iff_invariant_ofClosedCompl h hp hq).mp hx₁]

-- ker P = q where P := idempotentOfClosedCompl p q h hp hq
lemma ker_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ker (p.idempotentOfClosedCompl q h hp hq) = q := by
  ext x
  simp only [idempotentOfClosedCompl, LinearMap.mem_ker, ContinuousLinearMap.coe_comp',
    coe_subtypeL', coe_subtype, coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
    ZeroMemClass.coe_eq_zero, linearProjOfIsCompl_apply_eq_zero_iff]

-- range P = p where P := idempotentOfClosedCompl p q h hp hq
lemma range_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    range (p.idempotentOfClosedCompl q h hp hq) = p := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by simp [idempotentOfClosedCompl, ← hy],
    fun hx => LinearMap.mem_range.mp ⟨x,(mem_iff_invariant_ofClosedCompl h hp hq).mp hx⟩⟩

-- ker (1 - P) = p where P := idempotentOfClosedCompl p q h hp hq
lemma ker_id_sub_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ker (1 - (p.idempotentOfClosedCompl q h hp hq)) = p := by
  simp_rw [(is_idempotent_ofClosedCompl h hp hq).ker_id_sub_eq_range_cont,
    range_idempotentOfClosedCompl h hp hq]

-- range (1  - P) = q where P := idempotentOfClosedCompl p q h hp hq
lemma range_id_sub_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    range (1  - (p.idempotentOfClosedCompl q h hp hq)) = q := by
  simp_rw [(is_idempotent_ofClosedCompl h hp hq).range_id_sub_eq_ker_cont,
    ker_idempotentOfClosedCompl h hp hq]

end Submodule
