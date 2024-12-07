/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Order.PartialSups

/-!
# Consecutive differences of sets

This file defines the way to make a sequence of elements into a sequence of disjoint elements with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The sequence `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`, ....
* `partialSups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `iSup_disjointed`: `disjointed f` has the same supremum as `f`. Limiting case of
  `partialSups_disjointed`.

We also provide set notation variants of some lemmas.

## TODO

Find a useful statement of `disjointedRec_succ`.

One could generalize `disjointed` to any locally finite bot preorder domain, in place of `ℕ`.
Related to the TODO in the module docstring of `Mathlib.Order.PartialSups`.
-/


variable {α : Type*}

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

/-- If `f : ℕ → α` is a sequence of elements, then `disjointed f` is the sequence formed by
subtracting each element from the nexts. This is the unique disjoint sequence whose partial sups
are the same as the original sequence. -/
def disjointed (f : ℕ → α) : ℕ → α
  | 0 => f 0
  | n + 1 => f (n + 1) \ partialSups f n

@[simp]
theorem disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 :=
  rfl

theorem disjointed_succ (f : ℕ → α) (n : ℕ) : disjointed f (n + 1) = f (n + 1) \ partialSups f n :=
  rfl

theorem disjointed_le_id : disjointed ≤ (id : (ℕ → α) → ℕ → α) := by
  rintro f n
  cases n
  · rfl
  · exact sdiff_le

theorem disjointed_le (f : ℕ → α) : disjointed f ≤ f :=
  disjointed_le_id f

theorem disjoint_disjointed (f : ℕ → α) : Pairwise (Disjoint on disjointed f) := by
  refine (Symmetric.pairwise_on Disjoint.symm _).2 fun m n h => ?_
  cases n
  · exact (Nat.not_lt_zero _ h).elim
  exact
    disjoint_sdiff_self_right.mono_left
      ((disjointed_le f m).trans (le_partialSups_of_le f (Nat.lt_add_one_iff.1 h)))

-- Porting note: `disjointedRec` had a change in universe level.
/-- An induction principle for `disjointed`. To define/prove something on `disjointed f n`, it's
enough to define/prove it for `f n` and being able to extend through diffs. -/
def disjointedRec {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n)
  | 0 => id
  | n + 1 => fun h => by
    suffices H : ∀ k, p (f (n + 1) \ partialSups f k) from H n
    rintro k
    induction' k with k ih
    · exact hdiff h
    rw [partialSups_succ, ← sdiff_sdiff_left]
    exact hdiff ih

@[simp]
theorem disjointedRec_zero {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i))
    (h₀ : p (f 0)) : disjointedRec hdiff h₀ = h₀ :=
  rfl

-- TODO: Find a useful statement of `disjointedRec_succ`.
protected lemma Monotone.disjointed_succ {f : ℕ → α} (hf : Monotone f) (n : ℕ) :
    disjointed f (n + 1) = f (n + 1) \ f n := by rw [disjointed_succ, hf.partialSups_eq]

protected lemma Monotone.disjointed_succ_sup {f : ℕ → α} (hf : Monotone f) (n : ℕ) :
    disjointed f (n + 1) ⊔ f n = f (n + 1) := by
  rw [hf.disjointed_succ, sdiff_sup_cancel]; exact hf n.le_succ

@[simp]
theorem partialSups_disjointed (f : ℕ → α) : partialSups (disjointed f) = partialSups f := by
  ext n
  induction' n with k ih
  · rw [partialSups_zero, partialSups_zero, disjointed_zero]
  · rw [partialSups_succ, partialSups_succ, disjointed_succ, ih, sup_sdiff_self_right]

/-- `disjointed f` is the unique sequence that is pairwise disjoint and has the same partial sups
as `f`. -/
theorem disjointed_unique {f d : ℕ → α} (hdisj : Pairwise (Disjoint on d))
    (hsups : partialSups d = partialSups f) : d = disjointed f := by
  ext n
  cases' n with n
  · rw [← partialSups_zero d, hsups, partialSups_zero, disjointed_zero]
  suffices h : d n.succ = partialSups d n.succ \ partialSups d n by
    rw [h, hsups, partialSups_succ, disjointed_succ, sup_sdiff, sdiff_self, bot_sup_eq]
  rw [partialSups_succ, sup_sdiff, sdiff_self, bot_sup_eq, eq_comm, sdiff_eq_self_iff_disjoint]
  suffices h : ∀ m ≤ n, Disjoint (partialSups d m) (d n.succ) from h n le_rfl
  rintro m hm
  induction' m with m ih
  · exact hdisj (Nat.succ_ne_zero _).symm
  rw [partialSups_succ, disjoint_iff, inf_sup_right, sup_eq_bot_iff, ← disjoint_iff, ← disjoint_iff]
  exact ⟨ih (Nat.le_of_succ_le hm), hdisj (Nat.lt_succ_of_le hm).ne⟩

end GeneralizedBooleanAlgebra

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α]

theorem iSup_disjointed (f : ℕ → α) : ⨆ n, disjointed f n = ⨆ n, f n :=
  iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)

theorem disjointed_eq_inf_compl (f : ℕ → α) (n : ℕ) : disjointed f n = f n ⊓ ⨅ i < n, (f i)ᶜ := by
  cases n
  · rw [disjointed_zero, eq_comm, inf_eq_left]
    simp_rw [le_iInf_iff]
    exact fun i hi => (i.not_lt_zero hi).elim
  simp_rw [disjointed_succ, partialSups_eq_biSup, sdiff_eq, compl_iSup]
  congr
  ext i
  rw [Nat.lt_succ_iff]

end CompleteBooleanAlgebra

/-! ### Set notation variants of lemmas -/


theorem disjointed_subset (f : ℕ → Set α) (n : ℕ) : disjointed f n ⊆ f n :=
  disjointed_le f n

theorem iUnion_disjointed {f : ℕ → Set α} : ⋃ n, disjointed f n = ⋃ n, f n :=
  iSup_disjointed f

theorem disjointed_eq_inter_compl (f : ℕ → Set α) (n : ℕ) :
    disjointed f n = f n ∩ ⋂ i < n, (f i)ᶜ :=
  disjointed_eq_inf_compl f n

theorem preimage_find_eq_disjointed (s : ℕ → Set α) (H : ∀ x, ∃ n, x ∈ s n)
    [∀ x n, Decidable (x ∈ s n)] (n : ℕ) : (fun x => Nat.find (H x)) ⁻¹' {n} = disjointed s n := by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]
