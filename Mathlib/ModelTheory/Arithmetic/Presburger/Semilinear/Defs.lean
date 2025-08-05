/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a finitely
generated affine `ℕ`-submodule, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linear independent `ℕ`-submodule generators (periods).

## Main Definitions

- `Set.Linear`: a set is linear if is a finitely generated `ℕ`-submodule added by a single element
  (a finitely generated affine `ℕ`-submodule).
- `Set.Semilinear`: a set is semilinear if it is a finite union of linear sets.
- `Set.ProperLinear`: a linear set is proper if its `ℕ`-submodule generators (periods) are linear
  independent.
- `Set.ProperSemilinear`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `Set.Semilinear` is closed under union, projection, set addition and additive closure.
- `Set.Semilinear.proper_semilinear`: every semilinear set is a finite union of proper linear sets.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v w w₁ w₂

namespace Set

variable {α : Type u} {β : Type v} [AddCommMonoid α] [AddCommMonoid β]
  {ι : Type w} {ι₁ : Type w₁} {ι₂ : Type w₂} {a : α} {s s₁ s₂ : Set α}

open Pointwise Submodule

/-- A set is linear if is a finitely generated `ℕ`-submodule added by a single element (a finitely
  generated affine `ℕ`-submodule). -/
def Linear (s : Set α) :=
  ∃ (a : α) (t : Finset α), s = a +ᵥ (span ℕ (t : Set α) : Set α)

theorem Linear.singleton (a) : ({a} : Set α).Linear :=
  ⟨a, ∅, by simp⟩

theorem Linear.span_finset (s : Finset α) : (span ℕ (s : Set α) : Set α).Linear :=
  ⟨0, s, by rw [zero_vadd]⟩

theorem Linear.univ [h : Module.Finite ℕ α] : (univ : Set α).Linear := by
  obtain ⟨s, hs⟩ := h.fg_top
  refine ⟨0, s, ?_⟩
  rw [zero_vadd, hs, top_coe]

theorem Linear.vadd (hs : s.Linear) : (a +ᵥ s).Linear := by
  rcases hs with ⟨b, t, rfl⟩
  rw [vadd_vadd]
  exact ⟨a + b, t, rfl⟩

theorem Linear.add (hs₁ : s₁.Linear) (hs₂ : s₂.Linear) : (s₁ + s₂).Linear := by
  classical
  rcases hs₁ with ⟨a, t₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, rfl⟩
  rw [vadd_add_vadd, ← coe_sup, ← span_union, ← Finset.coe_union]
  exact ⟨a + b, t₁ ∪ t₂, rfl⟩

theorem Linear.image (hs : s.Linear) (f : α →ₗ[ℕ] β) : (f '' s).Linear := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  refine ⟨f a, t.image f, ?_⟩
  simp [image_vadd_distrib, span_image]

/-- A set is semilinear if it is a finite union of linear sets. -/
def Semilinear (s : Set α) :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, t.Linear) ∧ s = ⋃₀ S

theorem Linear.semilinear (h : s.Linear) : s.Semilinear :=
  ⟨{s}, by simp [h], by simp⟩

theorem Semilinear.empty : (∅ : Set α).Semilinear :=
  ⟨∅, by simp, by simp⟩

theorem Semilinear.singleton (a) : ({a} : Set α).Semilinear :=
  (Linear.singleton a).semilinear

theorem Semilinear.span_finset (s : Finset α) : (span ℕ (s : Set α) : Set α).Semilinear :=
  (Linear.span_finset s).semilinear

theorem Semilinear.univ [Module.Finite ℕ α] : (Set.univ : Set α).Semilinear :=
  Linear.univ.semilinear

/-- Semilinear sets are closed under union. -/
theorem Semilinear.union (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ ∪ s₂).Semilinear := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [← sUnion_union, ← Finset.coe_union]
  refine ⟨S₁ ∪ S₂, ?_, rfl⟩
  intro s hs
  simp only [Finset.mem_union] at hs
  exact hs.elim (hS₁ s) (hS₂ s)

theorem Semilinear.sUnion {S : Finset (Set α)} (hS : ∀ s ∈ S, s.Semilinear) :
    (⋃₀ (S : Set (Set α))).Semilinear := by
  classical
  induction S using Finset.induction with
  | empty => simpa using empty
  | insert s S _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using union hS.1 (ih hS.2)

theorem Semilinear.iUnion [Fintype ι] {s : ι → Set α}
    (hs : ∀ i, (s i).Semilinear) : (⋃ i, s i).Semilinear := by
  classical
  rw [← sUnion_range, ← image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  apply sUnion
  simpa

theorem Semilinear.biUnion {s : Finset ι} {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).Semilinear) : (⋃ i ∈ s, t i).Semilinear := by
  classical
  simp_rw [← Finset.mem_coe, ← sUnion_image, ← Finset.coe_image]
  apply sUnion
  simpa

theorem Finite.semilinear (hs : s.Finite) : s.Semilinear := by
  rw [← biUnion_of_singleton s, ← hs.coe_toFinset]
  simp_rw [Finset.mem_coe]
  apply Semilinear.biUnion
  simp [Semilinear.singleton]

theorem Semilinear.vadd (hs : s.Semilinear) : (a +ᵥ s).Semilinear := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  refine ⟨S.image (a +ᵥ ·), ?_, ?_⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro s hs
    exact (hS s hs).vadd
  · simp [vadd_set_sUnion, sUnion_eq_iUnion (s := a +ᵥ _), mem_vadd_set]

/-- Semilinear sets are closed under set addition. -/
theorem Semilinear.add (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) :
    (s₁ + s₂).Semilinear := by
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  simp_rw [sUnion_add, add_sUnion, Finset.mem_coe]
  exact biUnion fun s₁ hs₁ => biUnion fun s₂ hs₂ => ((hS₁ s₁ hs₁).add (hS₂ s₂ hs₂)).semilinear

theorem Semilinear.image (hs : s.Semilinear) (f : α →ₗ[ℕ] β) : (f '' s).Semilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, image_iUnion]
  exact biUnion fun s hs => ((hS s hs).image f).semilinear

theorem Semilinear.image_iff (f : α ≃ₗ[ℕ] β) : (f '' s).Semilinear ↔ s.Semilinear := by
  constructor <;> intro h
  · convert h.image f.symm.toLinearMap
    simp [image_image]
  · exact h.image f.toLinearMap

/-- Semilinear sets are closed under projection. -/
theorem Semilinear.proj {s : Set (ι₁ ⊕ ι₂ → α)} (hs : s.Semilinear) :
    {x | ∃ y, Sum.elim x y ∈ s}.Semilinear := by
  convert hs.image (LinearMap.funLeft ℕ α Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    refine ⟨Sum.elim x y, hy, ?_⟩
    rfl
  · simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
    rintro y hy rfl
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/-- An variant of `Semilinear.proj` for backward reasoning. -/
theorem Semilinear.proj' {p : (ι₁ → α) → (ι₂ → α) → Prop} :
    {x | p (x ∘ Sum.inl) (x ∘ Sum.inr)}.Semilinear → {x | ∃ y, p x y}.Semilinear :=
  proj

lemma Linear.span (hs : s.Linear) : (span ℕ s : Set α).Semilinear := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  convert_to ({0} ∪ (a +ᵥ (span ℕ ({a} ∪ t) : Set α))).Semilinear
  · ext x
    simp only [SetLike.mem_coe, mem_union, mem_singleton_iff]
    constructor
    · intro hx
      induction hx using span_induction with simp only [mem_vadd_set, SetLike.mem_coe] at *
      | mem x hx =>
        rcases hx with ⟨x, hx, rfl⟩
        refine Or.inr ⟨x, ?_, rfl⟩
        simp only [span_union]
        exact mem_sup_right hx
      | zero => exact Or.inl True.intro
      | add x y _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨x, hx, rfl⟩
        · simpa only [zero_add]
        · rcases ih₂ with rfl | ⟨y, hy, rfl⟩
          · exact Or.inr ⟨x, hx, by simp⟩
          · refine Or.inr ⟨a + (x + y), add_mem (mem_span_of_mem (by simp)) (add_mem hx hy), ?_⟩
            simp only [vadd_eq_add, ← add_assoc]
            rw [add_right_comm a a x]
      | smul n x _ ih =>
        rcases ih with rfl | ⟨x, hx, rfl⟩
        · simp
        · rcases n with (_ | n)
          · simp
          · refine Or.inr ⟨n • a + (n + 1) • x,
              add_mem (smul_mem _ _ (mem_span_of_mem (by simp))) (smul_mem _ _ hx), ?_⟩
            simp only [vadd_eq_add, ← add_assoc, succ_nsmul, smul_add]
            rw [add_comm a]
    · rintro (hx | hx)
      · simp [hx]
      · simp only [mem_vadd_set, SetLike.mem_coe, span_union, mem_sup, mem_span_singleton] at hx
        rcases hx with ⟨_, ⟨_, ⟨n, rfl⟩, z, hz, rfl⟩, rfl⟩
        rw [vadd_eq_add, add_left_comm, ← vadd_eq_add a]
        refine add_mem (smul_mem _ _ (mem_span_of_mem ?_)) (mem_span_of_mem (vadd_mem_vadd_set hz))
        nth_rw 2 [← add_zero a]
        rw [← vadd_eq_add]
        exact vadd_mem_vadd_set (zero_mem _)
  rw [← Finset.coe_singleton a, ← Finset.coe_union]
  exact (Semilinear.singleton 0).union (semilinear ⟨a, {a} ∪ t, rfl⟩)

/-- Semilinear sets are closed under `span ℕ` (additive closure). -/
theorem Semilinear.span (hs : s.Semilinear) : (span ℕ s : Set α).Semilinear := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  induction S using Finset.induction with
  | empty => simpa using singleton 0
  | insert s S _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa [span_union, coe_sup] using hS.1.span.add (ih hS.2)

/-- A linear set is proper if its `ℕ`-submodule generators (periods) are linear independent. -/
def ProperLinear (s : Set α) :=
  ∃ (a : α) (t : Finset α),
    LinearIndepOn ℕ id (t : Set α) ∧ s = a +ᵥ (span ℕ (t : Set α) : Set α)

theorem ProperLinear.linear (hs : s.ProperLinear) : s.Linear := by
  rcases hs with ⟨a, t, _, rfl⟩
  exact ⟨a, t, rfl⟩

/-- A semilinear set is proper if it is a finite union of proper linear sets. -/
def ProperSemilinear (s : Set α) :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, t.ProperLinear) ∧ s = ⋃₀ S

theorem ProperSemilinear.semilinear (hs : s.ProperSemilinear) : s.Semilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  refine ⟨S, ?_, rfl⟩
  intro s hs
  exact (hS s hs).linear

theorem ProperLinear.proper_semilinear (hs : s.ProperLinear) : s.ProperSemilinear :=
  ⟨{s}, by simp [hs], by simp⟩

theorem ProperSemilinear.empty : (∅ : Set α).ProperSemilinear :=
  ⟨∅, by simp, by simp⟩

theorem ProperSemilinear.union (hs₁ : s₁.ProperSemilinear) (hs₂ : s₂.ProperSemilinear) :
    (s₁ ∪ s₂).ProperSemilinear := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [← sUnion_union, ← Finset.coe_union]
  refine ⟨S₁ ∪ S₂, ?_, rfl⟩
  intro s hs
  simp only [Finset.mem_union] at hs
  exact hs.elim (hS₁ s) (hS₂ s)

theorem ProperSemilinear.sUnion {S : Finset (Set α)}
    (hS : ∀ s ∈ S, s.ProperSemilinear) : (⋃₀ (S : Set (Set α))).ProperSemilinear := by
  classical
  induction S using Finset.induction with
  | empty => simpa using empty
  | insert s S _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using union hS.1 (ih hS.2)

theorem ProperSemilinear.iUnion [Fintype ι] {s : ι → Set α}
    (hs : ∀ i, (s i).ProperSemilinear) : (⋃ i, s i).ProperSemilinear := by
  classical
  rw [← sUnion_range, ← image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  apply sUnion
  simpa

theorem ProperSemilinear.biUnion {s : Finset ι} {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).ProperSemilinear) : (⋃ i ∈ s, t i).ProperSemilinear := by
  classical
  simp_rw [← Finset.mem_coe, ← sUnion_image, ← Finset.coe_image]
  apply sUnion
  simpa

lemma Linear.proper_semilinear [IsCancelAdd α] (hs : s.Linear) : s.ProperSemilinear := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn ℕ id (t : Set α)
  · exact ProperLinear.proper_semilinear ⟨a, t, hindep, rfl⟩
  · rw [not_linearIndepOn_finset_iffₒ] at hindep
    rcases hindep with ⟨t', ht', f, g, heq, i, hi, hfi⟩
    simp only [Function.id_def] at heq
    convert_to
      (⋃ j ∈ t', ⋃ k ∈ Finset.range (f j),
        (a + k • j) +ᵥ (Submodule.span ℕ (t.erase j : Set α) : Set α)).ProperSemilinear
    · ext x
      simp only [mem_vadd_set, SetLike.mem_coe]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_span_finset] at hx
        rcases hx with ⟨h, hh, rfl⟩
        clear hh
        induction hn : h i using Nat.strong_induction_on generalizing h with | _ n ih
        subst hn
        by_cases hh : ∀ j ∈ t', f j ≤ h j
        · convert ih (h i - f i) (tsub_lt_self (hfi.trans_le (hh i hi)) hfi)
            (fun j => if hj : j ∈ t' then h j - f j else h j + g j) (by simp [hi]) using 1
          nth_rw 1 [← Finset.union_sdiff_of_subset ht']
          simp_rw [vadd_eq_add, add_left_cancel_iff, Finset.sum_union Finset.sdiff_disjoint.symm,
            dite_eq_ite, ite_smul, Finset.sum_ite, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.2 ht', Finset.filter_notMem_eq_sdiff, add_smul,
            Finset.sum_add_distrib, ← heq, ← add_assoc, add_right_comm, ← Finset.sum_add_distrib,
            ← add_smul]
          refine congr_arg (· + _) (Finset.sum_congr rfl fun j hj => ?_)
          rw [tsub_add_cancel_of_le (hh j hj)]
        · simp only [not_forall, not_le] at hh
          rcases hh with ⟨j, hj, hhj⟩
          simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
          refine ⟨j, hj, h j, hhj, ∑ x ∈ t.erase j, h x • x,
            sum_mem fun x hx => (smul_mem _ _ (mem_span_of_mem hx)), ?_⟩
          rw [← Finset.sum_erase_add _ _ (ht' hj), ← add_assoc, add_right_comm]
      · simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
        rintro ⟨j, hj, k, hk, y, hy, rfl⟩
        refine ⟨k • j + y,
          add_mem (smul_mem _ _ (mem_span_of_mem (ht' hj))) ((span_mono (t.erase_subset j)) hy), ?_⟩
        rw [add_assoc]
    · exact ProperSemilinear.biUnion fun j hj =>
        ProperSemilinear.biUnion fun k hk =>
          ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/-- The **proper decomposition** of semilinear sets: every semilinear set is a finite union of
  proper linear sets. -/
theorem Semilinear.proper_semilinear [IsCancelAdd α] (hs : s.Semilinear) : s.ProperSemilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe]
  exact ProperSemilinear.biUnion fun s hs => (hS s hs).proper_semilinear

end Set
