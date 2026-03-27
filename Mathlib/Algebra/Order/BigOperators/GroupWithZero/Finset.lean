/-
Copyright (c) 2025 Michael Stoll, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in groups with zero involving order

This file contains the results concerning the interaction of finset big operators with groups with
zero, where order is involved.
-/

@[expose] public section

variable {ι R : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero R]

section PosMulMono
section Preorder
variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0

/-- If all `f i`, `i ∈ s`, are nonneg and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod` for
the case of an ordered commutative multiplicative monoid. -/
@[gcongr]
lemma prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

theorem one_le_prod₀ (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  prod_const_one.symm.trans_le (prod_le_prod₀ (fun _ _ ↦ zero_le_one) h)

theorem one_le_prod'₀ (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  one_le_prod₀ fun i _ ↦ h i

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one` for the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_one₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  convert ← prod_le_prod₀ h0 h1
  exact Finset.prod_const_one

@[gcongr]
theorem prod_le_prod_of_subset_of_one_le₀ (h : s ⊆ t)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i
        = (∏ i ∈ s, f i) * 1 := (mul_one _).symm
      _ ≤ (∏ i ∈ s, f i) * ∏ i ∈ t \ s, f i :=
          mul_le_mul_of_nonneg_left (one_le_prod₀ (by simpa only [mem_sdiff, and_imp]))
            (prod_nonneg h0)
      _ = (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := mul_comm ..
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]

theorem prod_le_prod_of_subset_of_le_one₀ (h : s ⊆ t)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  classical calc
      ∏ i ∈ t, f i
        = ∏ i ∈ t \ s ∪ s, f i := by rw [sdiff_union_of_subset h]
      _ = (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := prod_union sdiff_disjoint
      _ = (∏ i ∈ s, f i) * ∏ i ∈ t \ s, f i := mul_comm ..
      _ ≤ (∏ i ∈ s, f i) * 1 :=
          mul_le_mul_of_nonneg_left
            (prod_le_one₀ (fun i hi ↦ h0 i (sdiff_subset hi)) (by simpa only [mem_sdiff, and_imp]))
            (prod_nonneg (fun i hi ↦ h0 i (h hi)))
      _ = ∏ i ∈ s, f i := mul_one _

theorem prod_mono_set_of_one_le₀ (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le₀ hst
    (fun x _ ↦ zero_le_one.trans (hf x)) fun x _ _ ↦ hf x

theorem prod_anti_set_of_le_one₀ (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Antitone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_le_one₀ hst (fun x _ ↦ h0 x) fun x _ _ ↦ h1 x

theorem prod_le_univ_prod_of_one_le₀ [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le₀ (subset_univ s)
    (fun x _ ↦ zero_le_one.trans (w x)) fun a _ _ ↦ w a

theorem single_le_prod₀ (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) :
    f a ≤ ∏ x ∈ s, f x := by
  rw [← prod_singleton f a]
  apply prod_le_prod_of_subset_of_one_le₀ (singleton_subset_iff.2 h) _ fun i hi _ ↦ hf i hi
  intro i hi
  rw [mem_singleton] at hi
  exact hi ▸ zero_le_one.trans (hf a h)

lemma mul_le_prod₀ {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s)
    (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k := by
  rw [← prod_singleton (a := j) (f := f), ← prod_cons (by simpa : i ∉ {j})]
  refine prod_le_prod_of_subset_of_one_le₀ (by simp [cons_subset, *]) ?_ fun k hk _ ↦ hf k hk
  intro k hk
  refine zero_le_one.trans (hf k ?_)
  rw [mem_cons, mem_singleton] at hk
  rcases hk with rfl | rfl <;> assumption

theorem prod_le_pow_card₀ (s : Finset ι) (f : ι → R) (n : R)
    (h0 : ∀ x ∈ s, 0 ≤ f x) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s :=
  (prod_le_prod₀ h0 h).trans_eq (prod_const n)

theorem pow_card_le_prod₀ (s : Finset ι) (f : ι → R) (n : R)
    (hn : 0 ≤ n) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ #s ≤ s.prod f :=
  (prod_const n).symm.trans_le (prod_le_prod₀ (fun _ _ ↦ hn) h)

theorem prod_fiberwise_le_prod_of_one_le_prod_fiber₀ {β : Type*} [DecidableEq β]
    {t : Finset β} {g : ι → β}
    (h0 : ∀ x ∈ s, 0 ≤ f x)
    (h : ∀ y ∉ t, (1 : R) ≤ ∏ x ∈ s with g x = y, f x) :
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤ ∏ x ∈ s, f x :=
  calc
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤
        ∏ y ∈ t ∪ s.image g, ∏ x ∈ s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le₀ subset_union_left
        (fun _ _ ↦ prod_nonneg fun x hx ↦ h0 x (mem_of_mem_filter x hx))
        fun _ _ hy ↦ h _ hy
    _ = ∏ x ∈ s, f x :=
      prod_fiberwise_of_maps_to
        (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _

theorem prod_le_prod_fiberwise_of_prod_fiber_le_one₀ {β : Type*} [DecidableEq β]
    {t : Finset β} {g : ι → β}
    (h0 : ∀ x ∈ s, 0 ≤ f x)
    (h : ∀ y ∉ t, ∏ x ∈ s with g x = y, f x ≤ 1) :
    ∏ x ∈ s, f x ≤ ∏ y ∈ t, ∏ x ∈ s with g x = y, f x :=
  calc
    ∏ x ∈ s, f x
      = ∏ y ∈ t ∪ s.image g, ∏ x ∈ s with g x = y, f x :=
        (prod_fiberwise_of_maps_to
          (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _).symm
    _ ≤ ∏ y ∈ t, ∏ x ∈ s with g x = y, f x :=
        prod_le_prod_of_subset_of_le_one₀ subset_union_left
          (fun _ _ ↦ prod_nonneg fun x hx ↦ h0 x (mem_of_mem_filter x hx))
          fun _ _ hy ↦ h _ hy

lemma prod_image_le_of_one_le₀ {β : Type*} [DecidableEq β]
    {g : ι → β} {f : β → R} (hf : ∀ u ∈ s.image g, 1 ≤ f u) :
    ∏ u ∈ s.image g, f u ≤ ∏ u ∈ s, f (g u) := by
  rw [prod_comp f g]
  refine prod_le_prod₀
    (fun a hag ↦ zero_le_one.trans (hf a hag)) fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow₀ (hf a hag)
  rw [← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

lemma le_prod_max_one {N : Type*} [CommMonoidWithZero N] [LinearOrder N] [ZeroLEOneClass N]
    [PosMulMono N] {i : ι} (hi : i ∈ s) (f : ι → N) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ ↦ le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ prod_le_prod₀ (fun _ _ ↦ by grind [zero_le_one]) fun _ _ ↦ by grind

end Preorder

section PartialOrder
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R] {f : ι → R} {s : Finset ι}

theorem prod_eq_one_iff_of_one_le₀ (hf : ∀ i ∈ s, 1 ≤ f i) :
    (∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ hf _ ∘ mem_insert_of_mem
    rw [prod_insert ha, forall_mem_insert]
    refine ⟨fun heq ↦ ?_, fun ⟨ha1, h⟩ ↦ by rw [ha1, one_mul, (ih hs).mpr h]⟩
    have ha1 : f a = 1 := by
      have hle := hf _ (mem_insert_self _ _)
      apply le_antisymm _ hle
      rw [← heq]
      nth_rw 1 [← mul_one (f a)]
      exact mul_le_mul_of_nonneg_left (one_le_prod₀ hs) (zero_le_one.trans hle)
    exact ⟨ha1, (ih hs).mp (by rwa [ha1, one_mul] at heq)⟩

lemma one_lt_prod_iff_of_one_le₀ (hf : ∀ x ∈ s, 1 ≤ f x) :
    1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x := by
  have hprod : 1 ≤ ∏ x ∈ s, f x := one_le_prod₀ hf
  rw [hprod.lt_iff_ne', Ne, prod_eq_one_iff_of_one_le₀ hf, not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

theorem prod_eq_one_iff_of_le_one₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ 1) :
    (∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun _ ↦ h0 _ ∘ mem_insert_of_mem
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun _ ↦ hf _ ∘ mem_insert_of_mem
    rw [prod_insert ha, forall_mem_insert]
    refine ⟨fun heq ↦ ?_, fun ⟨ha1, h⟩ ↦ by rw [ha1, one_mul, (ih hs0 hs1).mpr h]⟩
    have ha1 : f a = 1 := by
      apply le_antisymm (hf _ (mem_insert_self _ _))
      rw [← heq]
      nth_rw 2 [← mul_one (f a)]
      exact mul_le_mul_of_nonneg_left (prod_le_one₀ hs0 hs1) (h0 _ (mem_insert_self _ _))
    exact ⟨ha1, (ih hs0 hs1).mp (by rwa [ha1, one_mul] at heq)⟩

lemma prod_lt_one_iff_of_le_one₀ (h0 : ∀ x ∈ s, 0 ≤ f x) (hf : ∀ x ∈ s, f x ≤ 1) :
    ∏ x ∈ s, f x < 1 ↔ ∃ x ∈ s, f x < 1 := by
  have hprod : ∏ x ∈ s, f x ≤ 1 := prod_le_one₀ h0 hf
  rw [hprod.lt_iff_ne, Ne, prod_eq_one_iff_of_le_one₀ h0 hf, not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne]

end PartialOrder
end PosMulMono

section PosMulStrictMono
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R]
  {f g : ι → R} {s t : Finset ι}

lemma prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0

lemma prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (notMem_erase _ _), prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod₀ (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

lemma prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono
end CommMonoidWithZero
end Finset

namespace Fintype
variable [Fintype ι]

section CommMonoidWithZero
variable [CommMonoidWithZero R]

section Preorder
variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R}

theorem prod_le_prod₀ (h0 : 0 ≤ f) (hfg : f ≤ g) : ∏ i, f i ≤ ∏ i, g i :=
  Finset.prod_le_prod₀ (fun x _ ↦ h0 x) fun x _ ↦ hfg x

lemma one_le_prod₀ (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod₀ fun _ _ ↦ hf _

lemma prod_le_one₀ (h0 : 0 ≤ f) (hf : f ≤ 1) : ∏ i, f i ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ ↦ h0 _) fun _ _ ↦ hf _

end Preorder

section PartialOrder
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R] {f : ι → R}

lemma prod_eq_one_iff_of_one_le₀ (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_one_le₀ fun i _ ↦ hf i).trans <| by simp [funext_iff]

lemma prod_eq_one_iff_of_le_one₀ (h0 : 0 ≤ f) (hf : f ≤ 1) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_le_one₀ (fun i _ ↦ h0 i) fun i _ ↦ hf i).trans <| by
    simp [funext_iff]

end PartialOrder
end CommMonoidWithZero
end Fintype
