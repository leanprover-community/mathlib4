/-
Copyright (c) 2024 Joachim Breitner, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice

/-!
# Sum of suprema in `ENat`
-/

public section

assert_not_exists Field

namespace ENat

variable {a b c d : ℕ∞} {r p q : ℕ}

section OperationsAndInfty

variable {α : Type*}

@[simp, norm_cast]
theorem coe_finset_sum {s : Finset α} {f : α → ℕ} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : ℕ∞) :=
  map_sum (Nat.castRingHom _) f s

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℕ} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℕ∞) :=
  map_prod (Nat.castRingHom _) f s

@[simp]
theorem toNat_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ∞} :
    (∏ i ∈ s, f i).toNat = ∏ i ∈ s, (f i).toNat :=
  map_prod toNatHom _ _

theorem iInf_sum {ι α : Type*} {f : ι → α → ℕ∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a ∈ s, f i a = ∑ a ∈ s, ⨅ i, f i a := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

end OperationsAndInfty

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α → ℕ∞}

/-- A product of finite numbers is still finite. -/
lemma prod_ne_top (h : ∀ a ∈ s, f a ≠ ⊤) : ∏ a ∈ s, f a ≠ ⊤ := WithTop.prod_ne_top h

/-- A product of finite numbers is still finite. -/
lemma prod_lt_top (h : ∀ a ∈ s, f a < ⊤) : ∏ a ∈ s, f a < ⊤ := WithTop.prod_lt_top h

/-- A sum is infinite iff one of the summands is infinite. -/
@[simp] lemma sum_eq_top : ∑ x ∈ s, f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := WithTop.sum_eq_top

/-- A sum is finite iff all summands are finite. -/
lemma sum_ne_top : ∑ a ∈ s, f a ≠ ⊤ ↔ ∀ a ∈ s, f a ≠ ⊤ := WithTop.sum_ne_top

/-- A sum is finite iff all summands are finite. -/
@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤ := WithTop.sum_lt_top

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℕ∞} (h : ∑ x ∈ s, f x ≠ ⊤) {a : α}
    (ha : a ∈ s) : f a < ⊤ :=
  sum_lt_top.1 h.lt_top a ha

/-- Seeing `ℕ∞` as `ℕ` does not change their sum, unless one of the `ℕ∞` is
infinity -/
theorem toNat_sum {s : Finset α} {f : α → ℕ∞} (hf : ∀ a ∈ s, f a ≠ ⊤) :
    ENat.toNat (∑ a ∈ s, f a) = ∑ a ∈ s, ENat.toNat (f a) := by
  rw [← coe_inj, coe_toNat, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_toNat (hf x hx)).symm
  · exact sum_ne_top.2 hf

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℕ∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENat.add_lt_add Hlt.1 (ih Hlt.2)

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℕ∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply sum_lt_sum_of_nonempty hs Hle

end Sum

lemma sum_iSup {α ι : Type*} {s : Finset α} {f : α → ι → ℕ∞}
    (hf : ∀ i j, ∃ k, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ s, ⨆ i, f a i = ⨆ i, ∑ a ∈ s, f a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j ↦ (hf i j).imp fun k hk ↦ ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

lemma sum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
    {f : α → ι → ℕ∞} (hf : ∀ a, Monotone (f a)) : (∑ a ∈ s, iSup (f a)) = ⨆ n, ∑ a ∈ s, f a n :=
  sum_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a ↦ ⟨hf a hi, hf a hj⟩

end ENat
