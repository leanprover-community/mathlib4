/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
# The club filter and the non-stationary ideal

Let `α` be a well-order of uncountable cofinality. We are interested in two constructions:

- The `clubFilter` is a filter on `α`, consisting of all sets which contain a club. It is closed
  under intersections of cardinal `cof α`.
- The `nonstationaryIdeal` is an ideal on `α`, consisting of non-stationary sets. It is closed under
  unions of cardinal `cof α`.



## Implementation details

It'd be most natural to define `nonstationaryIdeal` using `Order.Ideal`, but Mathlib currently has
no way of taking a quotient by it. We instead define it as a (ring) `Ideal` on the type alias
`AsBoolRing (Set α)`. This lets us define `StationarySet` as a ring quotient.
-/

#exit
@[expose] public section

variable {α : Type*} {s : Set α} [LinearOrder α] [WellFoundedLT α]

open Cardinal Order Set

/-! ### Filter and ideal -/

/-- The filter consisting of all sets which contain a club set. -/
@[simps]
def clubFilter (hα : cof α ≠ ℵ₀) : Filter α where
  sets := {s | ∃ t ⊆ s, IsClub t}
  univ_sets := ⟨_, subset_rfl, .univ⟩
  sets_of_superset {s t} hs hst := by
    obtain ⟨u, hus, hu⟩ := hs
    exact ⟨u, hus.trans hst, hu⟩
  inter_sets {s t} hs ht := by
    obtain ⟨u, hus, hu⟩ := hs
    obtain ⟨v, hvt, hv⟩ := ht
    exact ⟨_, Set.inter_subset_inter hus hvt, hu.inter hα hv⟩

@[simp]
theorem mem_clubFilter {hα : cof α ≠ ℵ₀} : s ∈ clubFilter hα ↔ ∃ t ⊆ s, IsClub t :=
  .rfl

theorem cardinalInterFilter_clubFilter {hα : cof α ≠ ℵ₀} :
    CardinalInterFilter (clubFilter hα) (cof α) where
  cardinal_sInter_mem s hsα hs := by
    simp_rw [mem_clubFilter] at hs
    choose t hts ht using hs
    refine ⟨⋂ x : s, t _ x.2, ?_, ?_⟩
    · rw [Set.sInter_eq_iInter]
      exact Set.iInter_mono (by simpa)
    · apply IsClub.iInter hα <;> simpa

theorem countableInterFilter_clubFilter {hα : cof α ≠ ℵ₀} :
    CountableInterFilter (clubFilter hα) where
  countable_sInter_mem s hsα hs := by
    simp_rw [mem_clubFilter] at hs
    choose t hts ht using hs
    refine ⟨⋂ x : s, t _ x.2, ?_, ?_⟩
    · rw [Set.sInter_eq_iInter]
      exact Set.iInter_mono (by simpa)
    · have := hsα.to_subtype
      apply IsClub.iInter_of_countable hα
      simpa

@[simps]
def nonstationaryIdeal (hα : cof α ≠ ℵ₀) : Ideal (AsBoolRing (Set α)) where
  carrier := {s | ¬ IsStationary (ofBoolRing s)}
  zero_mem' := by simp
  add_mem' {s t} hs ht := by
    dsimp at *
    rw [Set.symmDiff_def, isStationary_union_iff hα, not_or]
    constructor
    · contrapose! hs
      exact hs.mono diff_subset
    · contrapose! ht
      exact ht.mono diff_subset
  smul_mem' s t hs := by
    dsimp at *
    contrapose! hs
    exact hs.mono inter_subset_right

@[simp]
theorem mem_nonstationaryIdeal_iff {s : AsBoolRing (Set α)} {hα : cof α ≠ ℵ₀} :
    s ∈ nonstationaryIdeal hα ↔ ¬ IsStationary (ofBoolRing s) :=
  .rfl

/-! ### Boolean algebra of stationary sets -/

variable [h₀ : Fact (cof α ≠ ℵ₀)]
include h₀

variable (α) in
def StationarySet : Type _ :=
  AsBoolRing (Set α) ⧸ nonstationaryIdeal h₀.out

namespace StationarySet

instance : BooleanAlgebra (StationarySet α) :=
  let : BooleanRing (StationarySet α) :=
    inferInstanceAs (BooleanRing (AsBoolRing (Set α) ⧸ nonstationaryIdeal h₀.out))
  BooleanRing.toBooleanAlgebra

def mk (s : Set α) : StationarySet α :=
  Ideal.Quotient.mk _ (toBoolRing s)

theorem mk_eq_mk {s t : Set α} : mk s = mk t ↔ ¬ IsStationary (symmDiff s t) :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem ..

@[simp] theorem mk_empty : mk (∅ : Set α) = ⊥ := rfl
@[simp] theorem mk_univ : mk (univ : Set α) = ⊤ := rfl
@[simp] theorem mk_inter (s t : Set α) : mk (s ∩ t) = mk s ⊓ mk t := rfl

@[simp]
theorem mk_compl (s : Set α) : mk sᶜ = (mk s)ᶜ := by
  unfold mk
  rw [toBoolRing_compl]
  rfl

@[simp]
theorem mk_union (s t : Set α) : mk (s ∪ t) = mk s ⊔ mk t := by
  change mk (s ⊔ t) = _
  unfold mk
  rw [toBoolRing_sup]
  rfl

@[simp]
theorem mk_sdiff (s t : Set α) : mk (s \ t) = mk s \ mk t := by
  unfold mk
  rw [toBoolRing_sdiff]
  rfl

@[simp]
theorem mk_symmDiff (s t : Set α) : mk (symmDiff s t) = symmDiff (mk s) (mk t) := by
  simp [symmDiff]

@[simp]
theorem mk_eq_bot {s : Set α} : mk s = ⊥ ↔ ¬ IsStationary s := by
  rw [← mk_empty, mk_eq_mk]
  simp [symmDiff]

alias ⟨_, mk_of_not_isStationary⟩ := mk_eq_bot

end StationarySet
