/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Bingyu Xia
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Data.Finsupp.Weight

/-!
# Functions tending to the cofinite filter

This file introduces the typeclass `Filter.TendstoCofinite`, which represents functions
`f : α → β` that tend to the cofinite filter along the cofinite filter. Functions of this class
are precisely the valid index transformations for renaming variables in multivariate power series.

## Main definitions

* `Filter.TendstoCofinite`: A typeclass for functions `f` satisfying
  `Filter.Tendsto f cofinite cofinite`. By `Filter.tendstoCofinite_iff_finite_preimage_singleton`,
  this is equivalent to `f` having finite fibers.
* `Filter.TendstoCofinite.mapDomain`: Given a function `v : α → M` into an `AddCommMonoid`,
  this is the pushforward function `β → M` defined by summing the values of `v` over the
  finite fibers of `f`.

## Main results

* `Filter.tendstoCofinite_iff_finite_preimage_singleton`: Characterizes `TendstoCofinite`
  as exactly those functions with finite fibers.
* Basic instances of `TendstoCofinite`.
* `Finsupp.mapDomain_tendstoCofinite`: Pushing forward finitely supported functions along
  a `TendstoCofinite` function preserves the `TendstoCofinite` property.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable {α β ι R M : Type*} (f : α → β) (g : β → ι) [AddCommMonoid M]

open Set Filter

namespace Filter

/-- The class of functions `f` such that `Tendsto f cofinite cofinite`, it is equivalent to
`f` having finite fibers, see `Filter.tendstoCofinite_iff_finite_preimage_singleton`. -/
@[mk_iff] class TendstoCofinite (f : α → β) : Prop where
  tendsto_cofinite (f) : Tendsto f cofinite cofinite

lemma TendstoCofinite.finite_preimage [TendstoCofinite f] {s : Set β} (hs : s.Finite) :
    Set.Finite (f ⁻¹' s) := by
  simpa [compl_eq_univ_diff] using TendstoCofinite.tendsto_cofinite f
    (show univ \ s ∈ cofinite by simpa [compl_eq_univ_diff])

lemma TendstoCofinite.finite_preimage_singleton [TendstoCofinite f] (b : β) :
    Set.Finite (f ⁻¹' {b}) := by simpa using TendstoCofinite.finite_preimage f (by simp)

theorem tendstoCofinite_iff_finite_preimage_singleton : TendstoCofinite f ↔
    ∀ b : β, Set.Finite (f ⁻¹' {b}) := ⟨fun _ ↦ TendstoCofinite.finite_preimage_singleton f,
  fun h ↦ ⟨Tendsto.cofinite_of_finite_preimage_singleton h⟩⟩

variable {f} in
lemma tendstoCofinite_of_injective (h : f.Injective) : TendstoCofinite f := ⟨h.tendsto_cofinite⟩

@[instance]
lemma tendstoCofinite_of_finite [Finite α] : TendstoCofinite f :=
  (tendstoCofinite_iff_finite_preimage_singleton f).mpr fun b ↦ Set.toFinite (f ⁻¹' {b})

namespace TendstoCofinite

@[instance]
lemma comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f) :=
  (tendstoCofinite_iff_finite_preimage_singleton _).mpr (fun r ↦ by
    simpa using TendstoCofinite.finite_preimage f (TendstoCofinite.finite_preimage g (by simp)))

@[instance]
lemma id : TendstoCofinite (id : α → α) := by simp [tendstoCofinite_iff_finite_preimage_singleton]

@[instance]
lemma embedding (e : α ↪ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

@[instance]
lemma equiv (e : α ≃ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

variable [TendstoCofinite f]

/-- Given `f : α → β` with `Filter.TendstoCofinite f` and `v : α → M`,
`Filter.TendstoCofinite.mapDomain f v : β → M` is the function whose value at `b : β` is
the sum of `v x` over all `x` such that `f x = b`. -/
noncomputable def mapDomain (v : α → M) : β → M :=
  fun i ↦ (finite_preimage_singleton f i).toFinset.sum v

@[simp]
lemma mapDomain_add (u v : α → M) : mapDomain f (u + v) = mapDomain f u + mapDomain f v := by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]
lemma mapDomain_smul [DistribSMul R M] (r : R) (v : α → M) :
    mapDomain f (r • v) = r • (mapDomain f v) := by ext; simp [mapDomain, Finset.smul_sum]

theorem mapDomain_eq_zero (v : α → M) {i : β} (h' : i ∉ Set.range f) : mapDomain f v i = 0 := by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

end TendstoCofinite

end Filter

@[instance]
theorem Finsupp.mapDomain_tendstoCofinite [TendstoCofinite f] :
    TendstoCofinite (mapDomain (M := ℕ) f) := by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x ↦ ?_
  let s := Finset.sup x.support (fun t ↦ (TendstoCofinite.finite_preimage_singleton f t).toFinset)
  let e : s ↪ α := Function.Embedding.subtype (fun u ↦ u ∈ s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <| finite_of_degree_le (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_setOf_eq]
  refine fun y hy ↦ ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain_eq_of_subsingletonAddUnits]
    exact degree_comapDomain_le_of_canonicallyOrderedAdd ..
  · suffices y.support ⊆ s by simpa [e]
    simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
      fun i hi ↦ ⟨i, by simp [hi]⟩
