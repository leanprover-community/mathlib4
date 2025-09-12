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
which are linear sets with linearly independent submonoid generators (periods).

## Main Definitions

- `IsLinearSet`: a set is linear if is a coset of a finitely generated additive submonoid.
- `IsSemilinearSet`: a set is semilinear if it is a finite union of linear sets.
- `IsProperLinearSet`: a linear set is proper if its submonoid generators (periods) are linearly
  independent.
- `IsProperSemilinearSet`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `IsSemilinearSet` is closed under union, projection, set addition and additive closure.
- `IsSemilinearSet.isProperSemilinearSet`: every semilinear set is a finite union of proper linear
  sets.

## Naming convention

`IsSemilinearSet.proj` projects a semilinear set of `ι ⊕ κ → α` to `ι → α` by taking `Sum.inl` on
the index. It is a special case of `IsSemilinearSet.image`, and is useful in proving semilinearity
of sets in form `{ x | ∃ y, p x y }`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v

variable {α : Type u} {β : Type v} [AddCommMonoid α] [AddCommMonoid β]
  {F : Type*} [FunLike F α β] [AddMonoidHomClass F α β]
  {ι κ : Type*} {a : α} {s s₁ s₂ : Set α}

open Set Pointwise AddSubmonoid

/-- A set is linear if is a coset of a finitely generated additive submonoid. -/
def IsLinearSet (s : Set α) : Prop :=
  ∃ (a : α) (t : Finset α), s = a +ᵥ (closure (t : Set α) : Set α)

@[simp]
theorem IsLinearSet.singleton (a) : IsLinearSet ({a} : Set α) :=
  ⟨a, ∅, by simp⟩

theorem IsLinearSet.closure_finset (s : Finset α) : IsLinearSet (closure (s : Set α) : Set α) :=
  ⟨0, s, by rw [zero_vadd]⟩

theorem isLinearSet_iff_eq_vadd_addSubmonoid_fg :
    IsLinearSet s ↔ ∃ (a : α) (P : AddSubmonoid α), P.FG ∧ s = a +ᵥ (P : Set α) :=
  exists_congr fun a => ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩

theorem isLinearSet_of_addSubmonoid_fg {P : AddSubmonoid α} (hP : P.FG) :
    IsLinearSet (P : Set α) := by
  rw [isLinearSet_iff_eq_vadd_addSubmonoid_fg]
  exact ⟨0, P, hP, by rw [zero_vadd]⟩

@[simp]
protected theorem IsLinearSet.univ [AddMonoid.FG α] : IsLinearSet (univ : Set α) :=
  isLinearSet_of_addSubmonoid_fg AddMonoid.FG.fg_top

theorem IsLinearSet.vadd (a : α) (hs : IsLinearSet s) : IsLinearSet (a +ᵥ s) := by
  rcases hs with ⟨b, t, rfl⟩
  rw [vadd_vadd]
  exact ⟨a + b, t, rfl⟩

theorem IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSet (s₁ + s₂) := by
  classical
  rcases hs₁ with ⟨a, t₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, rfl⟩
  rw [vadd_add_vadd, ← coe_sup, ← closure_union, ← Finset.coe_union]
  exact ⟨a + b, t₁ ∪ t₂, rfl⟩

theorem IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLinearSet (f '' s) := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  refine ⟨f a, t.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

/-- A set is semilinear if it is a finite union of linear sets. -/
def IsSemilinearSet (s : Set α) : Prop :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, IsLinearSet t) ∧ s = ⋃₀ S

theorem IsLinearSet.isSemilinearSet (h : IsLinearSet s) : IsSemilinearSet s :=
  ⟨{s}, by simp [h], by simp⟩

@[simp]
theorem IsSemilinearSet.empty : IsSemilinearSet (∅ : Set α) :=
  ⟨∅, by simp, by simp⟩

@[simp]
theorem IsSemilinearSet.singleton (a) : IsSemilinearSet ({a} : Set α) :=
  (IsLinearSet.singleton a).isSemilinearSet

theorem IsSemilinearSet.closure_finset (s : Finset α) :
    IsSemilinearSet (closure (s : Set α) : Set α) :=
  (IsLinearSet.closure_finset s).isSemilinearSet

theorem isSemilinearSet_of_addSubmonoid_fg {P : AddSubmonoid α} (hP : P.FG) :
    IsSemilinearSet (P : Set α) :=
  (isLinearSet_of_addSubmonoid_fg hP).isSemilinearSet

@[simp]
protected theorem IsSemilinearSet.univ [AddMonoid.FG α] : IsSemilinearSet (univ : Set α) :=
  IsLinearSet.univ.isSemilinearSet

/-- Semilinear sets are closed under union. -/
theorem IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∪ s₂) := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [← sUnion_union, ← Finset.coe_union]
  refine ⟨S₁ ∪ S₂, ?_, rfl⟩
  intro s hs
  rw [Finset.mem_union] at hs
  exact hs.elim (hS₁ s) (hS₂ s)

theorem IsSemilinearSet.sUnion {S : Finset (Set α)} (hS : ∀ s ∈ S, IsSemilinearSet s) :
    IsSemilinearSet (⋃₀ (S : Set (Set α))) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S _ ih =>
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using hS.1.union (ih hS.2)

theorem IsSemilinearSet.iUnion [Finite ι] {s : ι → Set α} (hs : ∀ i, IsSemilinearSet (s i)) :
    IsSemilinearSet (⋃ i, s i) := by
  classical
  haveI := Fintype.ofFinite ι
  rw [← sUnion_range, ← image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  apply sUnion
  simpa

theorem IsSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set α}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) := by
  classical
  simp_rw [← Finset.mem_coe, ← sUnion_image, ← Finset.coe_image]
  apply sUnion
  simpa

theorem IsSemilinearSet.biUnion {s : Set ι} {t : ι → Set α} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) := by
  rw [← hs.coe_toFinset]
  apply biUnion_finset
  simpa

theorem IsSemilinearSet.of_finite (hs : s.Finite) : IsSemilinearSet s := by
  rw [← biUnion_of_singleton s, ← hs.coe_toFinset]
  simp_rw [Finset.mem_coe]
  apply biUnion_finset
  simp

theorem IsSemilinearSet.vadd (a : α) (hs : IsSemilinearSet s) : IsSemilinearSet (a +ᵥ s) := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [vadd_set_sUnion, Finset.mem_coe]
  exact biUnion_finset fun s hs => ((hS s hs).vadd a).isSemilinearSet

/-- Semilinear sets are closed under set addition. -/
theorem IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  simp_rw [sUnion_add, add_sUnion, Finset.mem_coe]
  exact biUnion_finset fun s₁ hs₁ => biUnion_finset fun s₂ hs₂ =>
    ((hS₁ s₁ hs₁).add (hS₂ s₂ hs₂)).isSemilinearSet

theorem IsSemilinearSet.image (hs : IsSemilinearSet s) (f : F) : IsSemilinearSet (f '' s) := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, image_iUnion]
  exact biUnion_finset fun s hs => ((hS s hs).image f).isSemilinearSet

theorem isSemilinearSet_image_iff {F : Type*} [EquivLike F α β] [AddEquivClass F α β] (f : F) :
    IsSemilinearSet (f '' s) ↔ IsSemilinearSet s := by
  constructor <;> intro h
  · convert h.image (f : α ≃+ β).symm
    simp [image_image]
  · exact h.image f

/-- Semilinear sets are closed under projection (from `ι ⊕ κ → α` to `ι → α` by taking `Sum.inl` on
the index). It is a special case of `IsSemilinearSet.image`. -/
theorem IsSemilinearSet.proj {s : Set (ι ⊕ κ → α)} (hs : IsSemilinearSet s) :
    IsSemilinearSet { x | ∃ y, Sum.elim x y ∈ s } := by
  convert hs.image (LinearMap.funLeft ℕ α Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/-- A variant of `Semilinear.proj` for backward reasoning. -/
theorem IsSemilinearSet.proj' {p : (ι → α) → (κ → α) → Prop} :
    IsSemilinearSet { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) } → IsSemilinearSet { x | ∃ y, p x y } :=
  proj

protected lemma IsLinearSet.closure (hs : IsLinearSet s) : IsSemilinearSet (closure s : Set α) := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  convert (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, {a} ∪ t, rfl⟩)
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
protected theorem IsSemilinearSet.closure (hs : IsSemilinearSet s) :
    IsSemilinearSet (closure s : Set α) := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  induction S using Finset.induction with
  | empty => simp
  | insert s S _ ih =>
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa [closure_union, coe_sup] using hS.1.closure.add (ih hS.2)

/-- A linear set is proper if its submonoid generators (periods) are linearly independent. -/
def IsProperLinearSet (s : Set α) : Prop :=
  ∃ (a : α) (t : Finset α), LinearIndepOn ℕ id (t : Set α) ∧ s = a +ᵥ (closure (t : Set α) : Set α)

theorem IsProperLinearSet.isLinearSet (hs : IsProperLinearSet s) : IsLinearSet s := by
  rcases hs with ⟨a, t, _, rfl⟩
  exact ⟨a, t, rfl⟩

/-- A semilinear set is proper if it is a finite union of proper linear sets. -/
def IsProperSemilinearSet (s : Set α) : Prop :=
  ∃ (S : Finset (Set α)), (∀ t ∈ S, IsProperLinearSet t) ∧ s = ⋃₀ S

theorem IsProperSemilinearSet.isSemilinearSet (hs : IsProperSemilinearSet s) :
    IsSemilinearSet s := by
  rcases hs with ⟨S, hS, rfl⟩
  exact ⟨S, fun s hs => (hS s hs).isLinearSet, rfl⟩

theorem IsProperLinearSet.isProperSemilinearSet (hs : IsProperLinearSet s) :
    IsProperSemilinearSet s :=
  ⟨{s}, by simp [hs], by simp⟩

@[simp]
theorem IsProperSemilinearSet.empty : IsProperSemilinearSet (∅ : Set α) :=
  ⟨∅, by simp, by simp⟩

theorem IsProperSemilinearSet.union (hs₁ : IsProperSemilinearSet s₁)
    (hs₂ : IsProperSemilinearSet s₂) : IsProperSemilinearSet (s₁ ∪ s₂) := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [← sUnion_union, ← Finset.coe_union]
  refine ⟨S₁ ∪ S₂, ?_, rfl⟩
  intro s hs
  simp only [Finset.mem_union] at hs
  exact hs.elim (hS₁ s) (hS₂ s)

theorem IsProperSemilinearSet.sUnion {S : Finset (Set α)} (hS : ∀ s ∈ S, IsProperSemilinearSet s) :
    IsProperSemilinearSet (⋃₀ (S : Set (Set α))) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S _ ih =>
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using hS.1.union (ih hS.2)

theorem IsProperSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set α}
    (ht : ∀ i ∈ s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i ∈ s, t i) := by
  classical
  simp_rw [← Finset.mem_coe, ← sUnion_image, ← Finset.coe_image]
  apply sUnion
  simpa

lemma IsLinearSet.isProperSemilinearSet [IsCancelAdd α] (hs : IsLinearSet s) :
    IsProperSemilinearSet s := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn ℕ id (t : Set α)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, hindep, rfl⟩
  · rw [not_linearIndepOn_finset_iffₒₛ] at hindep
    rcases hindep with ⟨t', ht', f, heq, i, hi, hfi⟩
    simp only [Function.id_def] at heq
    convert_to IsProperSemilinearSet (⋃ j ∈ t', ⋃ k ∈ Finset.range (f j),
      (a + k • j) +ᵥ (closure (t.erase j : Set α) : Set α))
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
    · exact .biUnion_finset fun j hj => .biUnion_finset fun k hk =>
        ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/-- The **proper decomposition** of semilinear sets: every semilinear set is a finite union of
proper linear sets. -/
theorem IsSemilinearSet.isProperSemilinearSet [IsCancelAdd α] (hs : IsSemilinearSet s) :
    IsProperSemilinearSet s := by
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe]
  exact IsProperSemilinearSet.biUnion_finset fun s hs => (hS s hs).isProperSemilinearSet
