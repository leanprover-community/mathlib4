/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Order.Group.Nat

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a coset of a
finitely generated additive submonoid, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linearly independent submonoid generators (periods).

## Main Definitions

- `IsLinearSet`: a set is linear if it is a coset of a finitely generated additive submonoid.
- `IsSemilinearSet`: a set is semilinear if it is a finite union of linear sets.
- `IsProperLinearSet`: a linear set is proper if its submonoid generators (periods) are linearly
  independent.
- `IsProperSemilinearSet`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `IsSemilinearSet` is closed under union, projection, set addition and additive closure.
- `IsSemilinearSet.isProperSemilinearSet`: every semilinear set is a finite union of proper linear
  sets.
- `Nat.isSemilinearSet_iff_ultimately_periodic`: A set of `ℕ` is semilinear if and only if it is
  ultimately periodic, i.e. periodic after some number `k`.

## Naming convention

`IsSemilinearSet.proj` projects a semilinear set of `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index. It is a special case of `IsSemilinearSet.image`, and is useful in proving semilinearity
of sets in form `{ x | ∃ y, p x y }`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

@[expose] public section

variable {M N ι κ F : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [FunLike F M N] [AddMonoidHomClass F M N] {a : M} {s s₁ s₂ : Set M}

open Set Pointwise AddSubmonoid

/-- A set is linear if it is a coset of a finitely generated additive submonoid. -/
def IsLinearSet (s : Set M) : Prop :=
  ∃ (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

/-- An equivalent expression of `IsLinearSet` in terms of `Finset` instead of `Set.Finite`. -/
theorem isLinearSet_iff :
    IsLinearSet s ↔ ∃ (a : M) (t : Finset M), s = a +ᵥ (closure (t : Set M) : Set M) := by
  simp [IsLinearSet, Finset.exists]

@[simp]
theorem IsLinearSet.singleton (a : M) : IsLinearSet {a} :=
  ⟨a, ∅, by simp⟩

theorem IsLinearSet.closure_finset (s : Finset M) : IsLinearSet (closure (s : Set M) : Set M) :=
  ⟨0, s, by simp⟩

theorem IsLinearSet.closure_of_finite (hs : s.Finite) :
    IsLinearSet (closure s : Set M) :=
  ⟨0, s, hs, by simp⟩

theorem isLinearSet_iff_exists_fg_eq_vadd :
    IsLinearSet s ↔ ∃ (a : M) (P : AddSubmonoid M), P.FG ∧ s = a +ᵥ (P : Set M) := by
  simp_rw [isLinearSet_iff, AddSubmonoid.fg_def]
  grind

theorem IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : IsLinearSet (P : Set M) := by
  rw [isLinearSet_iff_exists_fg_eq_vadd]
  exact ⟨0, P, hP, by simp⟩

@[simp]
protected theorem IsLinearSet.univ [AddMonoid.FG M] : IsLinearSet (univ : Set M) :=
  of_fg AddMonoid.fg_top

theorem IsLinearSet.vadd (a : M) (hs : IsLinearSet s) : IsLinearSet (a +ᵥ s) := by
  rcases hs with ⟨b, t, ht, rfl⟩
  exact ⟨a + b, t, ht, by rw [vadd_vadd]⟩

theorem IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨a, t₁, ht₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, ht₂, rfl⟩
  exact ⟨a + b, t₁ ∪ t₂, ht₁.union ht₂, by simp [vadd_add_vadd, closure_union, coe_sup]⟩

theorem IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLinearSet (f '' s) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨f a, f '' t, ht.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

/-- A set is semilinear if it is a finite union of linear sets. -/
def IsSemilinearSet (s : Set M) : Prop :=
  ∃ (S : Set (Set M)), S.Finite ∧ (∀ t ∈ S, IsLinearSet t) ∧ s = ⋃₀ S

/-- An equivalent expression of `IsSemilinearSet` in terms of `Finset` instead of `Set.Finite`. -/
theorem isSemilinearSet_iff :
    IsSemilinearSet s ↔ ∃ (S : Finset (Set M)), (∀ t ∈ S, IsLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset

theorem IsLinearSet.isSemilinearSet (h : IsLinearSet s) : IsSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
theorem IsSemilinearSet.empty : IsSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩

@[simp]
theorem IsSemilinearSet.singleton (a : M) : IsSemilinearSet {a} :=
  (IsLinearSet.singleton a).isSemilinearSet

theorem IsSemilinearSet.closure_finset (s : Finset M) :
    IsSemilinearSet (closure (s : Set M) : Set M) :=
  (IsLinearSet.closure_finset s).isSemilinearSet

theorem IsSemilinearSet.closure_of_finite (hs : s.Finite) :
    IsSemilinearSet (closure s : Set M) :=
  (IsLinearSet.closure_of_finite hs).isSemilinearSet

theorem IsSemilinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) :
    IsSemilinearSet (P : Set M) :=
  (IsLinearSet.of_fg hP).isSemilinearSet

@[simp]
protected theorem IsSemilinearSet.univ [AddMonoid.FG M] : IsSemilinearSet (univ : Set M) :=
  IsLinearSet.univ.isSemilinearSet

/-- Semilinear sets are closed under union. -/
theorem IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∪ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ ∪ S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

theorem IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

theorem IsSemilinearSet.iUnion [Finite ι] {s : ι → Set M} (hs : ∀ i, IsSemilinearSet (s i)) :
    IsSemilinearSet (⋃ i, s i) := by
  rw [← sUnion_range]
  apply sUnion (finite_range s)
  simpa

theorem IsSemilinearSet.biUnion {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

theorem IsSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) :=
  biUnion s.finite_toSet ht

theorem IsSemilinearSet.of_finite (hs : s.Finite) : IsSemilinearSet s := by
  rw [← biUnion_of_singleton s]
  apply biUnion hs
  simp

theorem IsSemilinearSet.vadd (a : M) (hs : IsSemilinearSet s) : IsSemilinearSet (a +ᵥ s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  rw [vadd_set_sUnion]
  exact biUnion hS fun s hs => ((hS' s hs).vadd a).isSemilinearSet

/-- Semilinear sets are closed under set addition. -/
theorem IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  simp_rw [sUnion_add, add_sUnion]
  exact biUnion hS₁ fun s₁ hs₁ => biUnion hS₂ fun s₂ hs₂ =>
    ((hS₁' s₁ hs₁).add (hS₂' s₂ hs₂)).isSemilinearSet

/-- The image of a semilinear set under a homomorphism is semilinear. -/
theorem IsSemilinearSet.image (hs : IsSemilinearSet s) (f : F) : IsSemilinearSet (f '' s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, image_iUnion]
  exact biUnion hS fun s hs => ((hS' s hs).image f).isSemilinearSet

theorem isSemilinearSet_image_iff {F : Type*} [EquivLike F M N] [AddEquivClass F M N] (f : F) :
    IsSemilinearSet (f '' s) ↔ IsSemilinearSet s := by
  constructor <;> intro h
  · convert! h.image (f : M ≃+ N).symm
    simp [image_image]
  · exact h.image f

/-- Semilinear sets are closed under projection (from `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index). It is a special case of `IsSemilinearSet.image`. -/
theorem IsSemilinearSet.proj {s : Set (ι ⊕ κ → M)} (hs : IsSemilinearSet s) :
    IsSemilinearSet { x | ∃ y, Sum.elim x y ∈ s } := by
  convert! hs.image (LinearMap.funLeft ℕ M Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/-- A variant of `IsSemilinearSet.proj` for backward reasoning. -/
theorem IsSemilinearSet.proj' {p : (ι → M) → (κ → M) → Prop} :
    IsSemilinearSet { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) } → IsSemilinearSet { x | ∃ y, p x y } :=
  proj

protected lemma IsLinearSet.closure (hs : IsLinearSet s) : IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  convert! (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, { a } ∪ t, by simp [ht], rfl⟩)
  ext x
  simp only [SetLike.mem_coe, singleton_union, mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with ⟨x, hx, rfl⟩
      exact Or.inr ⟨x, closure_mono (subset_insert _ _) hx, rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨x, hx, rfl⟩
      · simpa
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
protected theorem IsSemilinearSet.closure (hs : IsSemilinearSet s) :
    IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa [closure_union, coe_sup] using hS'.1.closure.add (ih hS'.2)

/-- A linear set is proper if its submonoid generators (periods) are linearly independent. -/
def IsProperLinearSet (s : Set M) : Prop :=
  ∃ (a : M) (t : Set M), t.Finite ∧ LinearIndepOn ℕ id t ∧ s = a +ᵥ (closure t : Set M)

/-- An equivalent expression of `IsProperLinearSet` in terms of `Finset` instead of `Set.Finite`. -/
theorem isProperLinearSet_iff :
    IsProperLinearSet s ↔ ∃ (a : M) (t : Finset M),
      LinearIndepOn ℕ id (t : Set M) ∧ s = a +ᵥ (closure (t : Set M) : Set M) :=
  exists_congr fun a =>
    ⟨fun ⟨t, ht, hs⟩ => ⟨ht.toFinset, by simpa⟩, fun ⟨t, hs⟩ => ⟨t, t.finite_toSet, hs⟩⟩

theorem IsProperLinearSet.isLinearSet (hs : IsProperLinearSet s) : IsLinearSet s := by
  rcases hs with ⟨a, t, ht, _, rfl⟩
  exact ⟨a, t, ht, rfl⟩

@[simp]
theorem IsProperLinearSet.singleton (a : M) : IsProperLinearSet {a} :=
  ⟨a, ∅, by simp⟩

/-- A semilinear set is proper if it is a finite union of proper linear sets. -/
def IsProperSemilinearSet (s : Set M) : Prop :=
  ∃ (S : Set (Set M)), S.Finite ∧ (∀ t ∈ S, IsProperLinearSet t) ∧ s = ⋃₀ S

/-- An equivalent expression of `IsProperSemilinearSet` in terms of `Finset` instead of
`Set.Finite`. -/
theorem isProperSemilinearSet_iff :
    IsProperSemilinearSet s ↔ ∃ (S : Finset (Set M)), (∀ t ∈ S, IsProperLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset

theorem IsProperSemilinearSet.isSemilinearSet (hs : IsProperSemilinearSet s) :
    IsSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  exact ⟨S, hS, fun s hs => (hS' s hs).isLinearSet, rfl⟩

theorem IsProperLinearSet.isProperSemilinearSet (hs : IsProperLinearSet s) :
    IsProperSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
theorem IsProperSemilinearSet.empty : IsProperSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩

theorem IsProperSemilinearSet.union (hs₁ : IsProperSemilinearSet s₁)
    (hs₂ : IsProperSemilinearSet s₂) : IsProperSemilinearSet (s₁ ∪ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ ∪ S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

theorem IsProperSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsProperSemilinearSet s) : IsProperSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

theorem IsProperSemilinearSet.biUnion {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i ∈ s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

theorem IsProperSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i ∈ s, t i) :=
  biUnion s.finite_toSet ht

lemma IsLinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsLinearSet s) :
    IsProperSemilinearSet s := by
  classical
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn ℕ id (t : Set M)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, by simpa⟩
  rw [not_linearIndepOn_finset_iffₒₛ] at hindep
  rcases hindep with ⟨t', ht', f, heq, i, hi, hfi⟩
  simp only [Function.id_def] at heq
  convert_to IsProperSemilinearSet (⋃ j ∈ t', ⋃ k ∈ Finset.range (f j),
    (a + k • j) +ᵥ (closure (t.erase j : Set M) : Set M))
  · ext x
    simp only [mem_vadd_set, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closure_finset] at hy
      rcases hy with ⟨g, -, rfl⟩
      induction hn : g i using Nat.strong_induction_on generalizing g with | _ n ih'
      subst hn
      by_cases! hfg : ∀ j ∈ t', f j ≤ g j
      · convert!
        ih' (g i - f i) (Nat.sub_lt_self hfi (hfg i hi))
          (fun j => if j ∈ t' then g j - f j else g j + f j) (by simp [hi]) using 1
        conv_lhs => rw [← Finset.union_sdiff_of_subset ht']
        simp_rw [vadd_eq_add, add_left_cancel_iff, Finset.sum_union Finset.sdiff_disjoint.symm,
          ite_smul, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht',
          Finset.filter_notMem_eq_sdiff, add_smul, Finset.sum_add_distrib, ← heq, ← add_assoc,
          add_right_comm, ← Finset.sum_add_distrib]
        congr! 2 with j hj
        rw [← add_smul, tsub_add_cancel_of_le (hfg j hj)]
      · rcases hfg with ⟨j, hj, hgj⟩
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
  · exact .biUnion_finset fun j hj => .biUnion_finset fun k hk =>
      ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/-- The **proper decomposition** of semilinear sets: every semilinear set is a finite union of
proper linear sets. -/
theorem IsSemilinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsSemilinearSet s) :
    IsProperSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion]
  exact IsProperSemilinearSet.biUnion hS fun s hs => (hS' s hs).isProperSemilinearSet



/-- A set of `ℕ` is semilinear if and only if it is ultimately periodic, i.e. periodic after some
number `k`. -/
theorem Nat.isSemilinearSet_iff_ultimately_periodic {s : Set ℕ} :
    IsSemilinearSet s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s := by
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : ∀ t ∈ S, ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ t ↔ x + p ∈ t := by
      intro t ht
      apply hS at ht
      rw [isProperLinearSet_iff] at ht
      rcases ht with ⟨a, t, ht, rfl⟩
      have hcard : t.card ≤ 1 := by simpa [CommSemiring.rank_self] using ht.cardinal_le_rank
      simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
      rcases hcard with ⟨b, (rfl | rfl)⟩
      · refine ⟨a + 1, 1, zero_lt_one, fun x hx => ?_⟩
        simp [(by grind : x ≠ a), (by grind : x + 1 ≠ a)]
      · have hb : b ≠ 0 := by simpa [ne_comm] using ht.zero_notMem_image
        rw [Nat.ne_zero_iff_zero_lt] at hb
        refine ⟨a, b, hb, fun x hx => ?_⟩
        simp only [Finset.coe_singleton, mem_vadd_set, SetLike.mem_coe,
          AddSubmonoid.mem_closure_singleton, smul_eq_mul, vadd_eq_add, exists_exists_eq_and]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x + 1, by grind⟩
        · rintro ⟨y, heq⟩
          cases y with
          | zero => exact ⟨0, by grind⟩
          | succ y => exact ⟨y, by grind⟩
    choose! k p hS hS' using hS
    refine ⟨S.sup k, S.lcm p, ?_, fun x hx => ?_⟩
    · grind [Finset.lcm_eq_zero_iff]
    · simp only [mem_sUnion, SetLike.mem_coe]
      refine exists_congr fun t => and_congr_right fun ht => ?_
      have hpt : p t ∣ S.lcm p := Finset.dvd_lcm ht
      rw [dvd_iff_exists_eq_mul_left] at hpt
      rcases hpt with ⟨m, hpt⟩
      rw [hpt]
      clear hpt
      induction m with grind [Finset.sup_le_iff]
  · intro ⟨k, p, hp, hs⟩
    have h₁ : {x ∈ s | x < k}.Finite := (Set.finite_lt_nat k).subset (sep_subset_setOf _ _)
    have h₂ : {x ∈ s | k ≤ x ∧ x < k + p}.Finite :=
      (Set.finite_Ico k (k + p)).subset (sep_subset_setOf _ _)
    convert! (IsSemilinearSet.of_finite h₁).union (.add (.of_finite h₂) (.closure_finset { p }))
    ext x
    simp only [sep_and, Finset.coe_singleton, mem_union, mem_setOf_eq, mem_add, mem_inter_iff,
      SetLike.mem_coe, AddSubmonoid.mem_closure_singleton, smul_eq_mul, exists_exists_eq_and]
    constructor
    · intro hx
      by_cases hx' : x < k
      · exact Or.inl ⟨hx, hx'⟩
      · rw [not_lt] at hx'
        refine Or.inr ⟨k + (x - k) % p, ⟨⟨?_1, ?_2⟩, ?_1, ?_3⟩, (x - k) / p, ?_4⟩
        · rw [← add_tsub_cancel_of_le hx', ← Nat.mod_add_div' (x - k) p, ← add_assoc] at hx
          generalize (x - k) / p = m at hx
          induction m with grind
        · grind
        · exact Nat.add_lt_add_left (Nat.mod_lt _ hp) _
        · rw [add_assoc, Nat.mod_add_div', add_tsub_cancel_of_le hx']
    · rintro (⟨hx, hx'⟩ | ⟨x, ⟨⟨hx, hx'⟩, _⟩, m, rfl⟩)
      · exact hx
      · induction m with grind
