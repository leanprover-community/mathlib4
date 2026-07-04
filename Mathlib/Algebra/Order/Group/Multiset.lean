/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Multiset.Fold

/-!
# Multisets form an ordered monoid

This file contains the ordered monoid instance on multisets, and lemmas related to it.

See note [foundational algebra order theory].
-/

@[expose] public section

open List Nat

variable {α β : Type*}

namespace Multiset

/-! ### Additive monoid -/

instance instAddLeftMono : AddLeftMono (Multiset α) where elim _s _t _u := Multiset.add_le_add_left

instance instAddLeftReflectLE : AddLeftReflectLE (Multiset α) where
  le_of_add_le_add_left := Multiset.le_of_add_le_add_left

instance instAddCancelCommMonoid : AddCancelCommMonoid (Multiset α) where
  add_comm := Multiset.add_comm
  add_assoc := Multiset.add_assoc
  zero_add := Multiset.zero_add
  add_zero := Multiset.add_zero
  add_left_cancel _ _ _ := Multiset.add_right_inj.1
  nsmul := nsmulRec

lemma mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s := by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul, mem_add] at h
    exact h.elim ih id

@[simp]
lemma mem_nsmul {a : α} {s : Multiset α} {n : ℕ} : a ∈ n • s ↔ n ≠ 0 ∧ a ∈ s := by
  refine ⟨fun ha ↦ ⟨?_, mem_of_mem_nsmul ha⟩, fun h ↦ ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul, mem_add]
  exact Or.inr h.2

lemma mem_nsmul_of_ne_zero {a : α} {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s := by
  simp [*]

theorem smul_subset_self (s : Multiset α) (n : ℕ) : n • s ⊆ s :=
  subset_iff.mpr fun _ ↦ mem_of_mem_nsmul

theorem subset_smul_self_of_ne_zero (s : Multiset α) {n : ℕ} (hn : n ≠ 0) : s ⊆ n • s :=
  subset_iff.mpr fun _ ↦ mem_nsmul_of_ne_zero hn |>.mpr

lemma nsmul_cons {s : Multiset α} (n : ℕ) (a : α) :
    n • (a ::ₘ s) = n • ({a} : Multiset α) + n • s := by
  rw [← singleton_add, nsmul_add]

/-! ### Cardinality -/

/-- `Multiset.card` bundled as a group hom. -/
@[simps]
def cardHom : Multiset α →+ ℕ where
  toFun := card
  map_zero' := card_zero
  map_add' := card_add

@[simp]
lemma card_nsmul (s : Multiset α) (n : ℕ) : card (n • s) = n * card s := cardHom.map_nsmul ..

/-! ### `Multiset.replicate` -/

/-- `Multiset.replicate` as an `AddMonoidHom`. -/
@[simps]
def replicateAddMonoidHom (a : α) : ℕ →+ Multiset α where
  toFun n := replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a

lemma nsmul_replicate {a : α} (n m : ℕ) : n • replicate m a = replicate (n * m) a :=
  ((replicateAddMonoidHom a).map_nsmul _ _).symm

lemma nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a := by
  rw [← replicate_one, nsmul_replicate, mul_one]

/-! ### `Multiset.map` -/

/-- `Multiset.map` as an `AddMonoidHom`. -/
@[simps]
def mapAddMonoidHom (f : α → β) : Multiset α →+ Multiset β where
  toFun := map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
lemma coe_mapAddMonoidHom (f : α → β) : (mapAddMonoidHom f : Multiset α → Multiset β) = map f := rfl

lemma map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • map f s :=
  (mapAddMonoidHom f).map_nsmul _ _

/-! ### Subtraction -/

section
variable [DecidableEq α]

instance : OrderedSub (Multiset α) where tsub_le_iff_right _n _m _k := Multiset.sub_le_iff_le_add

instance : ExistsAddOfLE (Multiset α) where
  exists_add_of_le h := leInductionOn h fun s ↦
      let ⟨l, p⟩ := s.exists_perm_append; ⟨l, Quot.sound p⟩

end

/-! ### `Multiset.filter` -/

section
variable (p : α → Prop) [DecidablePred p]

lemma filter_nsmul (s : Multiset α) (n : ℕ) : filter p (n • s) = n • filter p s := by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons, filter_add, ih, filter_cons, nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (mem_of_mem_nsmul hb)]

/-! ### countP -/

@[simp]
lemma countP_nsmul (s) (n : ℕ) : countP p (n • s) = n * countP p s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

/-- `countP p`, the number of elements of a multiset satisfying `p`, promoted to an
`AddMonoidHom`. -/
def countPAddMonoidHom : Multiset α →+ ℕ where
  toFun := countP p
  map_zero' := countP_zero _
  map_add' := countP_add _

@[simp] lemma coe_countPAddMonoidHom : (countPAddMonoidHom p : Multiset α → ℕ) = countP p := rfl

end

@[simp] lemma dedup_nsmul [DecidableEq α] {s : Multiset α} {n : ℕ} (hn : n ≠ 0) :
    (n • s).dedup = s.dedup := by ext a; by_cases h : a ∈ s <;> simp [h, hn]

lemma Nodup.le_nsmul_iff_le {s t : Multiset α} {n : ℕ} (h : s.Nodup) (hn : n ≠ 0) :
    s ≤ n • t ↔ s ≤ t := by
  classical simp [← h.le_dedup_iff_le, hn]

/-! ### Multiplicity of an element -/

section
variable [DecidableEq α] {s : Multiset α}

/-- `count a`, the multiplicity of `a` in a multiset, promoted to an `AddMonoidHom`. -/
def countAddMonoidHom (a : α) : Multiset α →+ ℕ :=
  countPAddMonoidHom (a = ·)

@[simp]
lemma coe_countAddMonoidHom (a : α) : (countAddMonoidHom a : Multiset α → ℕ) = count a := rfl

@[simp]
lemma count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

end

theorem le_card_smul_iff_subset {s t : Multiset α} : s ≤ s.card • t ↔ s ⊆ t := by
  classical
  refine ⟨fun hle ↦ Subset.trans (subset_of_le hle) (t.smul_subset_self s.card), ?_⟩
  refine fun hsub ↦ le_iff_count.mpr fun a ↦ ?_
  by_cases! has : a ∉ s
  · simp [count_eq_zero_of_notMem has]
  grw [count_le_card, count_nsmul, ← one_le_count_iff_mem.mpr <| mem_of_subset hsub has, mul_one]

-- TODO: This should be `addMonoidHom_ext`
@[ext]
lemma addHom_ext [AddZeroClass β] ⦃f g : Multiset α →+ β⦄ (h : ∀ x, f {x} = g {x}) : f = g := by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]

theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s :=
  ⟨s.card, le_card_smul_iff_subset.mpr s.subset_dedup⟩

end Multiset
