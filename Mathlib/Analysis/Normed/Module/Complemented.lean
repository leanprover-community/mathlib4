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

/-
TODO: Move this to the correct place
-/

noncomputable section

theorem AddMonoidHom.ker_prod_ker_le_ker_coprod {M : Type*} [AddCommGroup M] {M₂ : Type*}
    [AddCommGroup M₂]  {M₃ : Type*} [AddCommGroup M₃] (f : M →+ M₃) (g : M₂ →+ M₃) :
    (ker f).prod (ker g) ≤ ker (f.coprod g) := by
  rintro ⟨y, z⟩
  --simp +contextual only [Subgroup.mem_prod, mem_ker, coprod_apply, add_zero, implies_true]
  intro h
  rw [AddSubgroup.mem_prod, mem_ker, mem_ker] at h
  rw [mem_ker, coprod_apply, h.1, h.2, add_zero]

theorem AddMonoidHom.ker_coprod_of_disjoint_range {M : Type*} [AddCommGroup M] {M₂ : Type*}
    [AddCommGroup M₂] {M₃ : Type*}
    [AddCommGroup M₃] (f : M →+ M₃) (g : M₂ →+ M₃)
    (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g) := by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, AddSubgroup.mem_prod, coprod_apply] at h ⊢
  have : f y ∈ (range f) ⊓ (range g) := by
    simp only [AddSubgroup.mem_inf, mem_range, exists_apply_eq_apply, true_and]
    --simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot, AddSubgroup.mem_bot] at this
  rw [this] at h
  simpa [this] using h

variable {G : Type*} [AddCommGroup G] (p q : AddSubgroup G) --(h : IsCompl p q)

theorem AddSubgroup.sup_eq_range (p q : AddSubgroup G) :
    p ⊔ q = AddMonoidHom.range (p.subtype.coprod q.subtype) := by
  apply AddSubgroup.ext fun x => by simp [AddSubgroup.mem_sup, SetLike.exists]

open AddMonoidHom in
/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def AddSubgroup.prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃+ G := by
  apply AddEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot_iff]
    rw[ (ker_coprod_of_disjoint_range p.subtype q.subtype), ker_subtype, ker_subtype,
      AddSubgroup.bot_sum_bot]
    rw [range_subtype, range_subtype]
    exact h.1
  · rw [← range_eq_top, ← AddSubgroup.sup_eq_range, h.sup_eq_top]

end


variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open LinearMap (ker range)

namespace IsIdempotentElem

open LinearMap in
lemma ker_id_sub_eq_range {P : E →ₗ[𝕜] E} (h : IsIdempotentElem P) : ker (1 - P) = range P :=
  (Submodule.toAddSubgroup_inj (ker (1 - P)) (range P)).mp (_root_.ker_id_sub_eq_range h)

lemma range_id_sub_eq_ker {P : E →ₗ[𝕜] E} (h : IsIdempotentElem P) : range (1 - P) = ker P := by
  rw [← (ker_id_sub_eq_range (IsIdempotentElem.one_sub h)), sub_sub_cancel]

end IsIdempotentElem

lemma IsIdempotentElem.ker_id_sub_eq_range_cont {P : E →L[𝕜] E} (h : IsIdempotentElem P) :
    ker (1 - P) = range P :=
  (Submodule.toAddSubgroup_inj (ker (1 - P)) (range P)).mp (_root_.ker_id_sub_eq_range h)

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
    (f.continuous.prodMk g.continuous)

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

-- P is an idempotent where P := idempotentOfClosedCompl p q h hp hq
lemma is_idempotent_ofClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    IsIdempotentElem (p.idempotentOfClosedCompl q h hp hq) := by
  ext x
  simp only [idempotentOfClosedCompl, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_comp',
    coe_subtypeL', coe_subtype, coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
    linearProjOfIsCompl_apply_left]

-- ker P = q where P := idempotentOfClosedCompl p q h hp hq
lemma ker_idempotentOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ker (p.idempotentOfClosedCompl q h hp hq) = q := by
  ext x
  simp only [idempotentOfClosedCompl, LinearMap.mem_ker, ContinuousLinearMap.coe_comp',
    coe_subtypeL', coe_subtype, coe_continuous_linearProjOfClosedCompl', Function.comp_apply,
    ZeroMemClass.coe_eq_zero, linearProjOfIsCompl_apply_eq_zero_iff]

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
