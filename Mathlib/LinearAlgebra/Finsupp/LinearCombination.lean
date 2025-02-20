/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# `Finsupp.linearCombination`

## Main definitions

* `Finsupp.linearCombination R (v : ι → M)`: sends `l : ι → R` to the linear combination of
  `v i` with coefficients `l i`;
* `Finsupp.linearCombinationOn`: a restricted version of `Finsupp.linearCombination` with domain

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section LinearCombination

variable (R)
variable {α' : Type*} {M' : Type*} [AddCommMonoid M'] [Module R M'] (v : α → M) {v' : α' → M'}

/-- Interprets (l : α →₀ R) as a linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
def linearCombination : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)

@[deprecated (since := "2024-08-29")] noncomputable alias total := linearCombination

variable {v}

theorem linearCombination_apply (l : α →₀ R) : linearCombination R v l = l.sum fun i a => a • v i :=
  rfl

@[deprecated (since := "2024-08-29")] alias total_apply := linearCombination_apply

theorem linearCombination_apply_of_mem_supported {l : α →₀ R} {s : Finset α}
    (hs : l ∈ supported R R (↑s : Set α)) : linearCombination R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [not_mem_support_iff.1 hxg, zero_smul]

@[deprecated (since := "2024-08-29")] alias total_apply_of_mem_supported :=
  linearCombination_apply_of_mem_supported

@[simp]
theorem linearCombination_single (c : R) (a : α) :
    linearCombination R v (single a c) = c • v a := by
  simp [linearCombination_apply, sum_single_index]

@[deprecated (since := "2024-08-29")] alias total_single := linearCombination_single

theorem linearCombination_zero_apply (x : α →₀ R) : (linearCombination R (0 : α → M)) x = 0 := by
  simp [linearCombination_apply]

@[deprecated (since := "2024-08-29")] alias total_zero_apply := linearCombination_zero_apply

variable (α M)

@[simp]
theorem linearCombination_zero : linearCombination R (0 : α → M) = 0 :=
  LinearMap.ext (linearCombination_zero_apply R)

@[simp]
theorem linearCombination_single_index (c : M) (a : α) (f : α →₀ R) [DecidableEq α] :
    linearCombination R (Pi.single a c) f = f a • c := by
  rw [linearCombination_apply, sum_eq_single a, Pi.single_eq_same]
  · exact fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, smul_zero]
  · exact fun _ ↦ by simp only [single_eq_same, zero_smul]

@[deprecated (since := "2024-08-29")] alias total_zero := linearCombination_zero

variable {α M}

theorem linearCombination_linear_comp (f : M →ₗ[R] M') :
    linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v := by
  ext
  simp [linearCombination_apply]

theorem apply_linearCombination (f : M →ₗ[R] M') (v) (l : α →₀ R) :
    f (linearCombination R v l) = linearCombination R (f ∘ v) l :=
  congr($(linearCombination_linear_comp R f) l).symm

@[deprecated (since := "2024-08-29")] alias apply_total := apply_linearCombination

theorem apply_linearCombination_id (f : M →ₗ[R] M') (l : M →₀ R) :
    f (linearCombination R _root_.id l) = linearCombination R f l :=
  apply_linearCombination ..

@[deprecated (since := "2024-08-29")] alias apply_total_id := apply_linearCombination_id

theorem linearCombination_unique [Unique α] (l : α →₀ R) (v : α → M) :
    linearCombination R v l = l default • v default := by
  rw [← linearCombination_single, ← unique_single l]

@[deprecated (since := "2024-08-29")] alias total_unique := linearCombination_unique

theorem linearCombination_surjective (h : Function.Surjective v) :
    Function.Surjective (linearCombination R v) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨Finsupp.single y 1, by simp [hy]⟩

@[deprecated (since := "2024-08-29")] alias total_surjective := linearCombination_surjective

theorem linearCombination_range (h : Function.Surjective v) :
    LinearMap.range (linearCombination R v) = ⊤ :=
  range_eq_top.2 <| linearCombination_surjective R h

@[deprecated (since := "2024-08-29")] alias total_range := linearCombination_range

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`Finsupp.linearCombination R id : (M →₀ R) →ₗ[R] M`. -/
theorem linearCombination_id_surjective (M) [AddCommMonoid M] [Module R M] :
    Function.Surjective (linearCombination R (id : M → M)) :=
  linearCombination_surjective R Function.surjective_id

@[deprecated (since := "2024-08-29")] alias total_id_surjective := linearCombination_id_surjective

theorem range_linearCombination : LinearMap.range (linearCombination R v) = span R (range v) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [linearCombination_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    use Finsupp.single i 1
    simp [hi]

@[deprecated (since := "2024-08-29")] alias range_total := range_linearCombination

theorem lmapDomain_linearCombination (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
    (linearCombination R v').comp (lmapDomain R R f) = g.comp (linearCombination R v) := by
  ext l
  simp [linearCombination_apply, Finsupp.sum_mapDomain_index, add_smul, h]

@[deprecated (since := "2024-08-29")] alias lmapDomain_total := lmapDomain_linearCombination

theorem linearCombination_comp_lmapDomain (f : α → α') :
    (linearCombination R v').comp (Finsupp.lmapDomain R R f) = linearCombination R (v' ∘ f) := by
  ext
  simp

@[deprecated (since := "2024-08-29")] alias total_comp_lmapDomain :=
  linearCombination_comp_lmapDomain

@[simp]
theorem linearCombination_embDomain (f : α ↪ α') (l : α →₀ R) :
    (linearCombination R v') (embDomain f l) = (linearCombination R (v' ∘ f)) l := by
  simp [linearCombination_apply, Finsupp.sum, support_embDomain, embDomain_apply]

@[deprecated (since := "2024-08-29")] alias total_embDomain := linearCombination_embDomain

@[simp]
theorem linearCombination_mapDomain (f : α → α') (l : α →₀ R) :
    (linearCombination R v') (mapDomain f l) = (linearCombination R (v' ∘ f)) l :=
  LinearMap.congr_fun (linearCombination_comp_lmapDomain _ _) l

@[deprecated (since := "2024-08-29")] alias total_mapDomain := linearCombination_mapDomain

@[simp]
theorem linearCombination_equivMapDomain (f : α ≃ α') (l : α →₀ R) :
    (linearCombination R v') (equivMapDomain f l) = (linearCombination R (v' ∘ f)) l := by
  rw [equivMapDomain_eq_mapDomain, linearCombination_mapDomain]

@[deprecated (since := "2024-08-29")] alias total_equivMapDomain := linearCombination_equivMapDomain

/-- A version of `Finsupp.range_linearCombination` which is useful for going in the other
direction -/
theorem span_eq_range_linearCombination (s : Set M) :
    span R s = LinearMap.range (linearCombination R ((↑) : s → M)) := by
  rw [range_linearCombination, Subtype.range_coe_subtype, Set.setOf_mem_eq]

@[deprecated (since := "2024-08-29")] alias span_eq_range_total := span_eq_range_linearCombination

theorem mem_span_iff_linearCombination (s : Set M) (x : M) :
    x ∈ span R s ↔ ∃ l : s →₀ R, linearCombination R (↑) l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_linearCombination _ _) x

@[deprecated (since := "2024-08-29")] alias mem_span_iff_total := mem_span_iff_linearCombination

variable {R}

theorem mem_span_range_iff_exists_finsupp {v : α → M} {x : M} :
    x ∈ span R (range v) ↔ ∃ c : α →₀ R, (c.sum fun i a => a • v i) = x := by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]

variable (R)

theorem span_image_eq_map_linearCombination (s : Set α) :
    span R (v '' s) = Submodule.map (linearCombination R v) (supported R R s) := by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : ∀ i, z i • v i ∈ span R (v '' s) := by
      intro c
      haveI := Classical.decPred fun x => x ∈ s
      by_cases h : c ∈ s
      · exact smul_mem _ _ (subset_span (Set.mem_image_of_mem _ h))
      · simp [(Finsupp.mem_supported' R _).1 hz _ h]
    rw [mem_comap, linearCombination_apply]
    refine sum_mem ?_
    simp [this]

@[deprecated (since := "2024-08-29")] alias span_image_eq_map_total :=
  span_image_eq_map_linearCombination

theorem mem_span_image_iff_linearCombination {s : Set α} {x : M} :
    x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, linearCombination R v l = x := by
  rw [span_image_eq_map_linearCombination]
  simp

@[deprecated (since := "2024-08-29")] alias mem_span_image_iff_total :=
  mem_span_image_iff_linearCombination

theorem linearCombination_option (v : Option α → M) (f : Option α →₀ R) :
    linearCombination R v f =
      f none • v none + linearCombination R (v ∘ Option.some) f.some := by
  rw [linearCombination_apply, sum_option_index_smul, linearCombination_apply]; simp

@[deprecated (since := "2024-08-29")] alias total_option := linearCombination_option

theorem linearCombination_linearCombination {α β : Type*} (A : α → M) (B : β → α →₀ R)
    (f : β →₀ R) : linearCombination R A (linearCombination R B f) =
      linearCombination R (fun b => linearCombination R A (B b)) f := by
  classical
  simp only [linearCombination_apply]
  apply induction_linear f
  · simp only [sum_zero_index]
  · intro f₁ f₂ h₁ h₂
    simp [sum_add_index, h₁, h₂, add_smul]
  · simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]

@[deprecated (since := "2024-08-29")] alias total_total := linearCombination_linearCombination

theorem linearCombination_smul [Module R S] [Module S M] [IsScalarTower R S M] {w : α' → S} :
    linearCombination R (fun i : α × α' ↦ w i.2 • v i.1) = (linearCombination S v).restrictScalars R
      ∘ₗ mapRange.linearMap (linearCombination R w) ∘ₗ (finsuppProdLEquiv R).toLinearMap := by
  ext; simp [finsuppProdLEquiv, finsuppProdEquiv, Finsupp.curry]

@[simp]
theorem linearCombination_fin_zero (f : Fin 0 → M) : linearCombination R f = 0 := by
  ext i
  apply finZeroElim i

@[deprecated (since := "2024-08-29")] alias total_fin_zero := linearCombination_fin_zero

variable (α) (M) (v)

/-- `Finsupp.linearCombinationOn M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : Set α` of indices.
-/
def linearCombinationOn (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((linearCombination _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_linearCombination _).2 ⟨l, hl, rfl⟩

@[deprecated (since := "2024-08-29")] noncomputable alias totalOn := linearCombinationOn

variable {α} {M} {v}

theorem linearCombinationOn_range (s : Set α) :
    LinearMap.range (linearCombinationOn α M R v s) = ⊤ := by
  rw [linearCombinationOn, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top, LinearMap.range_comp,
    range_subtype]
  exact (span_image_eq_map_linearCombination _ _).le

@[deprecated (since := "2024-08-29")] alias totalOn_range := linearCombinationOn_range

theorem linearCombination_restrict (s : Set α) :
    linearCombination R (s.restrict v) = Submodule.subtype _ ∘ₗ
      linearCombinationOn α M R v s ∘ₗ (supportedEquivFinsupp s).symm.toLinearMap := by
  classical ext; simp [linearCombinationOn]

theorem linearCombination_comp (f : α' → α) :
    linearCombination R (v ∘ f) = (linearCombination R v).comp (lmapDomain R R f) := by
  ext
  simp [linearCombination_apply]

@[deprecated (since := "2024-08-29")] alias total_comp := linearCombination_comp

theorem linearCombination_comapDomain (f : α → α') (l : α' →₀ R)
    (hf : Set.InjOn f (f ⁻¹' ↑l.support)) : linearCombination R v (Finsupp.comapDomain f l hf) =
      (l.support.preimage f hf).sum fun i => l (f i) • v i := by
  rw [linearCombination_apply]; rfl

@[deprecated (since := "2024-08-29")] alias total_comapDomain := linearCombination_comapDomain

theorem linearCombination_onFinset {s : Finset α} {f : α → R} (g : α → M)
    (hf : ∀ a, f a ≠ 0 → a ∈ s) :
    linearCombination R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x := by
  classical
  simp only [linearCombination_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose! h
  simp [h]

@[deprecated (since := "2024-08-29")] alias total_onFinset := linearCombination_onFinset

end LinearCombination

end Finsupp

section Fintype

variable {α M : Type*} (R : Type*) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
variable (v : α → M)

/-- `Fintype.linearCombination R S v f` is the linear combination of vectors in `v` with weights
in `f`. This variant of `Finsupp.linearCombination` is defined on fintype indexed vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
protected def Fintype.linearCombination : (α → M) →ₗ[S] (α → R) →ₗ[R] M where
  toFun v :=
    { toFun := fun f => ∑ i, f i • v i
      map_add' := fun f g => by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
      map_smul' := fun r f => by simp_rw [Finset.smul_sum, smul_smul]; rfl }
  map_add' u v := by ext; simp [Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Finset.smul_sum, smul_comm]

@[deprecated (since := "2024-08-29")] alias Fintype.total := Fintype.linearCombination

variable {S}

theorem Fintype.linearCombination_apply (f) : Fintype.linearCombination R S v f = ∑ i, f i • v i :=
  rfl

@[deprecated (since := "2024-08-29")] alias Fintype.total_apply := Fintype.linearCombination_apply

@[simp]
theorem Fintype.linearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.linearCombination R S v (Pi.single i r) = r • v i := by
  simp_rw [Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

@[deprecated (since := "2024-08-29")] alias Fintype.total_apply_single :=
  Fintype.linearCombination_apply_single

variable (S)

theorem Finsupp.linearCombination_eq_fintype_linearCombination_apply (x : α → R) :
    linearCombination R v ((Finsupp.linearEquivFunOnFinite R R α).symm x) =
      Fintype.linearCombination R S v x := by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.not_mem_support_iff.mp hx]
    exact zero_smul _ _

@[deprecated (since := "2024-08-29")] alias Finsupp.total_eq_fintype_total_apply :=
  Finsupp.linearCombination_eq_fintype_linearCombination_apply

theorem Finsupp.linearCombination_eq_fintype_linearCombination :
    (linearCombination R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap =
      Fintype.linearCombination R S v :=
  LinearMap.ext <| linearCombination_eq_fintype_linearCombination_apply R S v

@[deprecated (since := "2024-08-29")] alias Finsupp.total_eq_fintype_total :=
  Finsupp.linearCombination_eq_fintype_linearCombination

variable {S}

@[simp]
theorem Fintype.range_linearCombination :
    LinearMap.range (Fintype.linearCombination R S v) = Submodule.span R (Set.range v) := by
  rw [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, Finsupp.range_linearCombination]

@[deprecated (since := "2024-08-29")] alias Fintype.range_total := Fintype.range_linearCombination

section SpanRange

variable {v} {x : M}

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem mem_span_range_iff_exists_fun :
    x ∈ span R (range v) ↔ ∃ c : α → R, ∑ i, c i • v i = x := by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
  exact exists_congr fun c => Eq.congr_left <| Finsupp.sum_fintype _ _ fun i => zero_smul _ _

/-- A family `v : α → V` is generating `V` iff every element `(x : V)`
can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem top_le_span_range_iff_forall_exists_fun :
    ⊤ ≤ span R (range v) ↔ ∀ x, ∃ c : α → R, ∑ i, c i • v i = x := by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩

end SpanRange

end Fintype

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- Pick some representation of `x : span R w` as a linear combination in `w`,
  ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose
-/
irreducible_def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose

@[simp]
theorem Span.finsupp_linearCombination_repr {w : Set M} (x : span R w) :
    Finsupp.linearCombination R ((↑) : w → M) (Span.repr R w x) = x := by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose_spec

@[deprecated (since := "2024-08-29")] alias Span.finsupp_total_repr :=
  Span.finsupp_linearCombination_repr
end

theorem LinearMap.map_finsupp_linearCombination (f : M →ₗ[R] N) {ι : Type*} {g : ι → M}
    (l : ι →₀ R) : f (linearCombination R g l) = linearCombination R (f ∘ g) l :=
  apply_linearCombination _ _ _ _

@[deprecated (since := "2024-08-29")] alias LinearMap.map_finsupp_total :=
  LinearMap.map_finsupp_linearCombination

theorem mem_span_finset {s : Finset M} {x : M} :
    x ∈ span R (↑s : Set M) ↔ ∃ f : M → R, ∑ i ∈ s, f i • i = x :=
  ⟨fun hx =>
    let ⟨v, hvs, hvx⟩ :=
      (Finsupp.mem_span_image_iff_linearCombination _).1
        (show x ∈ span R (_root_.id '' (↑s : Set M)) by rwa [Set.image_id])
    ⟨v, hvx ▸ (linearCombination_apply_of_mem_supported _ hvs).symm⟩,
    fun ⟨_, hf⟩ => hf ▸ sum_mem fun _ hi => smul_mem _ _ <| subset_span hi⟩

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `Finsupp.sum`. -/
theorem mem_span_set {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔
      ∃ c : M →₀ R, (c.support : Set M) ⊆ s ∧ (c.sum fun mi r => r • mi) = m := by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_linearCombination R (v := _root_.id (α := M))

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses a sum indexed by `Fin n` for some `n`. -/
lemma mem_span_set' {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔ ∃ (n : ℕ) (f : Fin n → R) (g : Fin n → s),
      ∑ i, f i • (g i : M) = m := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i ↦ c (A.symm i), fun i ↦ ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv A.symm _ (fun j ↦ c j • (j : M)) (fun i ↦ rfl)
  · rintro ⟨n, f, g, rfl⟩
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (g i).2))

/-- The span of a subset `s` is the union over all `n` of the set of linear combinations of at most
`n` terms belonging to `s`. -/
lemma span_eq_iUnion_nat (s : Set M) :
    (Submodule.span R s : Set M) = ⋃ (n : ℕ),
      (fun (f : Fin n → (R × M)) ↦ ∑ i, (f i).1 • (f i).2) '' ({f | ∀ i, (f i).2 ∈ s}) := by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_setOf_eq, mem_span_set']
  refine exists_congr (fun n ↦ ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i ↦ (f i, g i), fun i ↦ (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i ↦ (f i).1, fun i ↦ ⟨(f i).2, (hf i)⟩, rfl⟩
