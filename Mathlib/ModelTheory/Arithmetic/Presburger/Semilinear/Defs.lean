/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a coset of a
finitely generated additive submonoid, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linear independent submonoid generators (periods).

## Main Definitions

- `Set.Linear`: a set is linear if is a coset of a finitely generated additive submonoid.
- `Set.Semilinear`: a set is semilinear if it is a finite union of linear sets.
- `Set.ProperLinear`: a linear set is proper if its submonoid generators (periods) are linear
  independent.
- `Set.ProperSemilinear`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `Set.Semilinear` is closed under union, projection, set addition and additive closure.
- `Set.Semilinear.proper_semilinear`: every semilinear set is a finite union of proper linear sets.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v

namespace Set

variable {α : Type u} {β : Type v} [AddCommMonoid α] [AddCommMonoid β]
  {F : Type*} [FunLike F α β] [AddMonoidHomClass F α β]
  {ι κ : Type*} {a : α} {s s₁ s₂ : Set α}

open Pointwise AddSubmonoid

/-- A set is linear if is a coset of a finitely generated additive submonoid. -/
def Linear (s : Set α) :=
  ∃ (a : α) (t : Finset α), s = a +ᵥ (closure (t : Set α) : Set α)

theorem Linear.singleton (a) : ({a} : Set α).Linear :=
  ⟨a, ∅, by simp⟩

theorem Linear.closure_finset (s : Finset α) : (closure (s : Set α) : Set α).Linear :=
  ⟨0, s, by rw [zero_vadd]⟩

theorem Linear.iff_eq_vadd_addSubmonoid_fg :
    s.Linear ↔ ∃ (a : α) (P : AddSubmonoid α), P.FG ∧ s = a +ᵥ (P : Set α) :=
  exists_congr fun a => ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩

theorem Linear.of_addSubmonoid_fg {P : AddSubmonoid α} (hP : P.FG) : (P : Set α).Linear := by
  rw [iff_eq_vadd_addSubmonoid_fg]
  exact ⟨0, P, hP, by rw [zero_vadd]⟩

theorem Linear.univ [AddMonoid.FG α] : (univ : Set α).Linear :=
  of_addSubmonoid_fg AddMonoid.FG.fg_top

theorem Linear.vadd (hs : s.Linear) : (a +ᵥ s).Linear := by
  rcases hs with ⟨b, t, rfl⟩
  rw [vadd_vadd]
  exact ⟨a + b, t, rfl⟩

theorem Linear.add (hs₁ : s₁.Linear) (hs₂ : s₂.Linear) : (s₁ + s₂).Linear := by
  classical
  rcases hs₁ with ⟨a, t₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, rfl⟩
  rw [vadd_add_vadd, ← coe_sup, ← closure_union, ← Finset.coe_union]
  exact ⟨a + b, t₁ ∪ t₂, rfl⟩

theorem Linear.image (hs : s.Linear) (f : F) : (f '' s).Linear := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  refine ⟨f a, t.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

/-- A set is semilinear if it is a finite union of linear sets. -/
def Semilinear (s : Set α) :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, t.Linear) ∧ s = ⋃₀ S

theorem Linear.semilinear (h : s.Linear) : s.Semilinear :=
  ⟨{s}, by simp [h], by simp⟩

theorem Semilinear.empty : (∅ : Set α).Semilinear :=
  ⟨∅, by simp, by simp⟩

theorem Semilinear.singleton (a) : ({a} : Set α).Semilinear :=
  (Linear.singleton a).semilinear

theorem Semilinear.closure_finset (s : Finset α) : (closure (s : Set α) : Set α).Semilinear :=
  (Linear.closure_finset s).semilinear

theorem Semilinear.of_addSubmonoid_fg {P : AddSubmonoid α} (hP : P.FG) : (P : Set α).Semilinear :=
  (Linear.of_addSubmonoid_fg hP).semilinear

theorem Semilinear.univ [AddMonoid.FG α] : (univ : Set α).Semilinear :=
  Linear.univ.semilinear

/-- Semilinear sets are closed under union. -/
theorem Semilinear.union (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ ∪ s₂).Semilinear := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [← sUnion_union, ← Finset.coe_union]
  refine ⟨S₁ ∪ S₂, ?_, rfl⟩
  intro s hs
  rw [Finset.mem_union] at hs
  exact hs.elim (hS₁ s) (hS₂ s)

theorem Semilinear.sUnion {S : Finset (Set α)} (hS : ∀ s ∈ S, s.Semilinear) :
    (⋃₀ (S : Set (Set α))).Semilinear := by
  classical
  induction S using Finset.induction with
  | empty => simpa using empty
  | insert s S _ ih =>
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using hS.1.union (ih hS.2)

theorem Semilinear.iUnion [Finite ι] {s : ι → Set α}
    (hs : ∀ i, (s i).Semilinear) : (⋃ i, s i).Semilinear := by
  classical
  haveI := Fintype.ofFinite ι
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
  simp_rw [vadd_set_sUnion, Finset.mem_coe]
  exact biUnion fun s hs => (hS s hs).vadd.semilinear

/-- Semilinear sets are closed under set addition. -/
theorem Semilinear.add (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) :
    (s₁ + s₂).Semilinear := by
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  simp_rw [sUnion_add, add_sUnion, Finset.mem_coe]
  exact biUnion fun s₁ hs₁ => biUnion fun s₂ hs₂ => ((hS₁ s₁ hs₁).add (hS₂ s₂ hs₂)).semilinear

theorem Semilinear.image (hs : s.Semilinear) (f : F) : (f '' s).Semilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, image_iUnion]
  exact biUnion fun s hs => ((hS s hs).image f).semilinear

theorem Semilinear.image_iff {F : Type*} [EquivLike F α β] [AddEquivClass F α β] (f : F) :
    (f '' s).Semilinear ↔ s.Semilinear := by
  constructor <;> intro h
  · convert h.image (f : α ≃+ β).symm
    simp [image_image]
  · exact h.image f

/-- Semilinear sets are closed under projection. -/
theorem Semilinear.proj {s : Set (ι ⊕ κ → α)} (hs : s.Semilinear) :
    { x | ∃ y, Sum.elim x y ∈ s }.Semilinear := by
  convert hs.image (LinearMap.funLeft ℕ α Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/-- An variant of `Semilinear.proj` for backward reasoning. -/
theorem Semilinear.proj' {p : (ι → α) → (κ → α) → Prop} :
    { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) }.Semilinear → { x | ∃ y, p x y }.Semilinear :=
  proj

lemma Linear.closure (hs : s.Linear) : (closure s : Set α).Semilinear := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  convert (Semilinear.singleton 0).union (semilinear ⟨a, {a} ∪ t, rfl⟩)
  ext x
  simp only [SetLike.mem_coe, Finset.coe_union, Finset.coe_singleton, singleton_union,
    mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with ⟨x, hx, rfl⟩
      exact Or.inr ⟨x, closure_mono (subset_insert _ _) hx, rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨x, hx, rfl⟩
      · simpa only [zero_add]
      · rcases ih₂ with rfl | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨x, hx, by simp⟩
        · refine Or.inr ⟨_, add_mem (mem_closure_of_mem (mem_insert _ _)) (add_mem hx hy), ?_⟩
          simp_rw [← add_assoc, add_right_comm a a x]
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · simp
    · simp_rw [insert_eq, closure_union, mem_sup, mem_closure_singleton] at hx
      rcases hx with ⟨_, ⟨n, rfl⟩, ⟨x, hx, rfl⟩⟩
      rw [add_left_comm]
      refine add_mem (nsmul_mem (mem_closure_of_mem ?_) _)
        (mem_closure_of_mem (vadd_mem_vadd_set hx))
      nth_rw 2 [← add_zero a]
      exact vadd_mem_vadd_set (zero_mem _)

/-- Semilinear sets are closed under additive closure. -/
theorem Semilinear.closure (hs : s.Semilinear) : (closure s : Set α).Semilinear := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  induction S using Finset.induction with
  | empty => simpa using singleton 0
  | insert s S _ ih =>
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa [closure_union, coe_sup] using hS.1.closure.add (ih hS.2)

/-- A linear set is proper if its submonoid generators (periods) are linear independent. -/
def ProperLinear (s : Set α) :=
  ∃ (a : α) (t : Finset α), LinearIndepOn ℕ id (t : Set α) ∧ s = a +ᵥ (closure (t : Set α) : Set α)

theorem ProperLinear.linear (hs : s.ProperLinear) : s.Linear := by
  rcases hs with ⟨a, t, _, rfl⟩
  exact ⟨a, t, rfl⟩

/-- A semilinear set is proper if it is a finite union of proper linear sets. -/
def ProperSemilinear (s : Set α) :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, t.ProperLinear) ∧ s = ⋃₀ S

theorem ProperSemilinear.semilinear (hs : s.ProperSemilinear) : s.Semilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  exact ⟨S, fun s hs => (hS s hs).linear, rfl⟩

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
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using hS.1.union (ih hS.2)

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
  · rw [not_linearIndepOn_finset_iffₒₛ] at hindep
    rcases hindep with ⟨t', ht', f, heq, i, hi, hfi⟩
    simp only [Function.id_def] at heq
    convert_to
      (⋃ j ∈ t', ⋃ k ∈ Finset.range (f j),
        (a + k • j) +ᵥ (AddSubmonoid.closure (t.erase j : Set α) : Set α)).ProperSemilinear
    · ext x
      simp only [mem_vadd_set, SetLike.mem_coe]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_closure_finset] at hy
        rcases hy with ⟨g, -, rfl⟩
        induction hn : g i using Nat.strong_induction_on generalizing g with | _ n ih'
        subst hn
        by_cases hfg : ∀ j ∈ t', f j ≤ g j
        · convert ih' (g i - f i) (Nat.sub_lt_self hfi (hfg i hi))
            (fun j => if j ∈ t' then g j - f j else g j + f j) (by simp [hi]) using 1
          conv_lhs => rw [← Finset.union_sdiff_of_subset ht']
          simp_rw [vadd_eq_add, add_left_cancel_iff, Finset.sum_union Finset.sdiff_disjoint.symm,
            ite_smul, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht',
            Finset.filter_notMem_eq_sdiff, add_smul, Finset.sum_add_distrib, ← heq, ← add_assoc,
            add_right_comm, ← Finset.sum_add_distrib]
          congr! 2 with j hj
          rw [← add_smul, tsub_add_cancel_of_le (hfg j hj)]
        · push_neg at hfg
          rcases hfg with ⟨j, hj, hgj⟩
          simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
          refine ⟨j, hj, g j, hgj, ∑ k ∈ t.erase j, g k • k,
            sum_mem fun x hx => (nsmul_mem (mem_closure_of_mem hx) _), ?_⟩
          rw [← Finset.sum_erase_add _ _ (ht' hj), ← add_assoc, add_right_comm]
      · simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
        rintro ⟨j, hj, k, hk, y, hy, rfl⟩
        refine ⟨k • j + y,
          add_mem (nsmul_mem (mem_closure_of_mem (ht' hj)) _)
            ((closure_mono (t.erase_subset j)) hy), ?_⟩
        rw [add_assoc]
    · exact .biUnion fun j hj => .biUnion fun k hk =>
        ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/-- The **proper decomposition** of semilinear sets: every semilinear set is a finite union of
proper linear sets. -/
theorem Semilinear.proper_semilinear [IsCancelAdd α] (hs : s.Semilinear) : s.ProperSemilinear := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe]
  exact ProperSemilinear.biUnion fun s hs => (hS s hs).proper_semilinear

end Set
