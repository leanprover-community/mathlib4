/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions on exactly one point

This file contains definitions and basic results on defining/updating/removing `Finsupp`s
using one point of the domain.

## Main declarations

* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.
-/

@[expose] public section

assert_not_exists CompleteLattice

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `single` -/

section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind

@[grind =]
theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]

theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]

theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b := by
  classical
  ext
  simp [single_apply, Set.indicator, @eq_comm _ a]

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b := by
  classical exact Pi.single_eq_same (M := fun _ ↦ M) a b

@[simp]
theorem single_eq_of_ne (h : a' ≠ a) : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne h _

@[simp]
theorem single_eq_of_ne' (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _

theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (0 : _) a b := by
  classical rw [single_eq_set_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]

theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b

@[simp, grind =]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  DFunLike.coe_injective <| by
    classical simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)

theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  grind

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical
  grind

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  classical
  grind

theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `Finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`Finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_set_indicator]

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : x = a <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx))) hx)

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  classical
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      grind
  · grind

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

lemma apply_surjective (a : α) : Surjective fun f : α →₀ M ↦ f a :=
  RightInverse.surjective fun _ ↦ single_eq_same

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _

theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [DFunLike.ext_iff, single_eq_set_indicator]

theorem single_ne_zero : single a b ≠ 0 ↔ b ≠ 0 :=
  single_eq_zero.not

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical simp only [single_apply, eq_comm]

instance instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [Finsupp.unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same,
    single_eq_same]

lemma apply_single' [Zero N] [Zero P] (e : N → P) (he : e 0 = 0) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b := by
  classical
  grind

theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero _ h.1⟩

theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩

theorem card_support_eq_one {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) := by
  simp only [card_eq_one, support_eq_singleton]

theorem card_support_eq_one' {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, ∃ b ≠ 0, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

@[simp]
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single, Equiv.symm_apply_apply]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    grind

@[grind =]
theorem update_apply [DecidableEq α] : (f.update a b) i = if i = a then b else f i := by
  delta update Function.update
  grind

@[simp, norm_cast]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  grind

@[simp]
theorem update_self : f.update a (f a) = f := by
  classical
  grind

@[simp]
theorem zero_update : update 0 a b = single a b := rfl

theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  grind

@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.erase a := by
  grind

variable {b}

theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) :
    support (f.update a b) = insert a f.support := by
  grind

theorem support_update_subset [DecidableEq α] :
    support (f.update a b) ⊆ insert a f.support := by
  grind

theorem update_comm (f : α →₀ M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ := by
  classical
  grind

@[simp] theorem update_idem (f : α →₀ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c := by
  classical
  grind

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    classical
    grind

@[grind =]
theorem erase_apply [DecidableEq α] {a a' : α} {f : α →₀ M} :
    f.erase a a' = if a' = a then 0 else f a' := by
  rw [erase, coe_mk]
  simp only [ite_eq_ite]

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} :
    (f.erase a).support = f.support.erase a := by
  classical
  grind

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 := by classical grind

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by classical grind

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by classical grind

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  classical grind

@[simp]
theorem erase_of_notMem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  classical grind

@[deprecated (since := "2025-05-23")] alias erase_of_not_mem_support := erase_of_notMem_support

theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  simp

theorem erase_eq_update_zero (f : α →₀ M) (a : α) : f.erase a = update f a 0 := by classical grind

-- The name matches `Finset.erase_insert_of_ne`
theorem erase_update_of_ne (f : α →₀ M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by classical grind

-- not `simp` as `erase_of_notMem_support` can prove this
theorem erase_idem (f : α →₀ M) (a : α) :
    erase a (erase a f) = erase a f := by classical grind

@[simp] theorem update_erase_eq_update (f : α →₀ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by classical grind

@[simp] theorem erase_update_eq_erase (f : α →₀ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by classical grind

end Erase

/-! ### Declarations about `mapRange` -/

section MapRange

variable [Zero M] [Zero N] [Zero P]

@[simp]
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) :=
  by classical grind

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

theorem single_of_embDomain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single_ne_zero _ hb]
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply_self f l, h]
      grind
    · exact hc₂

@[simp]
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  classical
    ext b
    by_cases h : b ∈ Set.range f <;> grind

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

@[simp]
theorem zipWith_single_single (f : M → N → P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  classical
  grind

end ZipWith
end Finsupp
