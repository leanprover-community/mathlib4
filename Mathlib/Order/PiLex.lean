/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Order.Lex
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common

/-!
# Lexicographic order on Pi types

This file defines the lexicographic and colexicographic orders for Pi types.

* In the lexicographic order, `a` is less than `b` if `a i = b i` for all `i` up to some point
  `k`, and `a k < b k`.
* In the colexicographic order, `a` is less than `b` if `a i = b i` for all `i` above some point
  `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order.

## See also

Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Order.Sigma`: Lexicographic order on `Σₗ i, α i`.
* `Order.PSigma`: Lexicographic order on `Σₗ' i, α i`.
* `Order.Prod.Lex.Basic`: Lexicographic order on `α × β`.
-/

@[expose] public section

assert_not_exists Monoid

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
and each `β i` is ordered by `s`.

The `<` relation on `Lex (∀ i, β i)` is `Pi.Lex (· < ·) (· < ·)`, while the `<` relation on
`Colex (∀ i, β i)` is `Pi.Lex (· > ·) (· < ·)`. -/
protected def Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
basic API, just in case -/
/-- The notation `Πₗ i, α i` refers to a pi type equipped with the lexicographic order. -/
-- The type ascription on `p` lets the delaborator generator elaborate the expansion.
notation3 "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, (p : (_ : (_ : Type _)) → Type _) i)) =>
  r

theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

theorem lex_lt_of_lt [∀ i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

theorem lex_iff_of_unique [Unique ι] [∀ i, LT (β i)] {r} [Std.Irrefl r] {x y : ∀ i, β i} :
    Pi.Lex r (· < ·) x y ↔ x default < y default := by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

theorem trichotomous_lex [∀ i, Std.Trichotomous (α := β i) s] [wf : WellFounded r] :
    Std.Trichotomous (Pi.Lex r @s) :=
  { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i ≠ b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (fun h => wf.not_lt_min _ (by grind) hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
      exact hba ⟨i, (hri · · |>.symm), Not.imp_symm this <| wf.min_mem {i | a i ≠ b i} h⟩ }

instance [LT ι] [∀ a, LT (β a)] : LT (Lex (∀ i, β i)) where
  lt x y := Pi.Lex (· < ·) (· < ·) x.ofLex y.ofLex

instance [LT ι] [∀ a, LT (β a)] : LT (Colex (∀ i, β i)) where
  lt x y := Pi.Lex (· > ·) (· < ·) x.ofColex y.ofColex

@[deprecated "syntactic equality" (since := "2026-11-10")] alias toLex_apply := rfl
@[deprecated "syntactic equality" (since := "2026-11-10")] alias ofLex_apply := rfl
@[deprecated "syntactic equality" (since := "2026-11-10")] alias toColex_apply := rfl
@[deprecated "syntactic equality" (since := "2026-11-10")] alias ofColex_apply := rfl

theorem Lex.lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Lex (∀ i, β i)} :
    x < y ↔ x.ofLex default < y.ofLex default :=
  lex_iff_of_unique

theorem Colex.lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Colex (∀ i, β i)} :
    x < y ↔ x.ofColex default < y.ofColex default :=
  lex_iff_of_unique

instance Lex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Lex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a.ofLex k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    obtain H | rfl | H := lt_trichotomy N₁ N₂
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

instance Colex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Colex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a.ofColex k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    obtain H | rfl | H := lt_trichotomy N₁ N₂
    exacts [⟨N₂, fun j hj => (lt_N₁ _ (H.trans hj)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| H.trans hj), lt_N₂ _ H ▸ a_lt_b⟩]

instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Lex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Colex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

/-- `Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`. -/
noncomputable instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO _ (· < ·)
    { trichotomous := fun x y h₁ h₂ ↦ Lex.ext ((trichotomous_lex ..).1 x.ofLex y.ofLex h₁ h₂) }
    (Classical.decRel _)

/-- `Colex (∀ i, α i)` is a linear order if the original order has well-founded `>`. -/
noncomputable instance Colex.linearOrder [LinearOrder ι] [WellFoundedGT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Colex (∀ i, β i)) :=
  @linearOrderOfSTO _ (· < ·)
    { trichotomous := fun _ _ h₁ h₂ ↦ Colex.ext ((trichotomous_lex ..).1 _ _ h₁ h₂) }
    (Classical.decRel _)

theorem lex_le_iff_of_unique [Unique ι] [LinearOrder ι] [∀ i, PartialOrder (β i)]
    {x y : Lex (∀ i, β i)} : x ≤ y ↔ x.ofLex default ≤ y.ofLex default := by
  simp_rw [le_iff_lt_or_eq, Pi.Lex.lt_iff_of_unique, ← ofLex_inj, funext_iff, Unique.forall_iff]

theorem colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [∀ i, PartialOrder (β i)]
    {x y : Colex (∀ i, β i)} : x ≤ y ↔ x.ofColex default ≤ y.ofColex default := by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff]

section PartialOrder
variable [LinearOrder ι] {x : ∀ i, β i} {i : ι} {a : β i} [∀ i, PartialOrder (β i)]

open Function

section Lex
variable [WellFoundedLT ι]

open _root_.Lex

theorem toLex_monotone : Monotone (@toLex (∀ i, β i)) := fun a b h ↦
  or_iff_not_imp_left.2 fun hne ↦
    let ⟨i, hi, hl⟩ := WellFounded.has_min inferInstance (r := (· < ·)) {i | a i ≠ b i}
      (Function.ne_iff.1 (by simpa using hne))
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩

theorem toLex_strictMono : StrictMono (@toLex (∀ i, β i)) := fun a b h =>
  let ⟨i, hi, hl⟩ := WellFounded.has_min inferInstance (r := (· < ·)) { i | a i ≠ b i }
    (Function.ne_iff.1 h.ne)
  ⟨i, fun j hj => by
    contrapose! hl
    exact ⟨j, hl, hj⟩, (h.le i).lt_of_ne hi⟩

@[simp]
theorem lt_toLex_update_self_iff : toLex x < toLex (update x i a) ↔ x i < a := by
  refine ⟨?_, fun h => toLex_strictMono <| lt_update_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]
theorem toLex_update_lt_self_iff : toLex (update x i a) < toLex x ↔ a < x i := by
  refine ⟨?_, fun h => toLex_strictMono <| update_lt_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]
theorem le_toLex_update_self_iff : toLex x ≤ toLex (update x i a) ↔ x i ≤ a := by
  simp_rw [le_iff_lt_or_eq, lt_toLex_update_self_iff, toLex_inj, eq_update_self_iff]

@[simp]
theorem toLex_update_le_self_iff : toLex (update x i a) ≤ toLex x ↔ a ≤ x i := by
  simp_rw [le_iff_lt_or_eq, toLex_update_lt_self_iff, toLex_inj, update_eq_self_iff]

end Lex

section Colex
variable [WellFoundedGT ι]

open _root_.Colex

theorem toColex_monotone : Monotone (@toColex (∀ i, β i)) := fun a b h ↦
  or_iff_not_imp_left.2 fun hne ↦
    let ⟨i, hi, hl⟩ := WellFounded.has_min inferInstance (r := (· > ·)) {i | a i ≠ b i}
      (Function.ne_iff.1 (by simpa using hne))
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem toColex_strictMono : StrictMono (@toColex (∀ i, β i)) :=
  toLex_strictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem lt_toColex_update_self_iff : toColex x < toColex (update x i a) ↔ x i < a :=
  lt_toLex_update_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem toColex_update_lt_self_iff : toColex (update x i a) < toColex x ↔ a < x i :=
  toLex_update_lt_self_iff (ι := ιᵒᵈ)

@[simp]
theorem le_toColex_update_self_iff : toColex x ≤ toColex (update x i a) ↔ x i ≤ a := by
  simp_rw [le_iff_lt_or_eq, lt_toColex_update_self_iff, toColex_inj, eq_update_self_iff]

@[simp]
theorem toColex_update_le_self_iff : toColex (update x i a) ≤ toColex x ↔ a ≤ x i := by
  simp_rw [le_iff_lt_or_eq, toColex_update_lt_self_iff, toColex_inj, update_eq_self_iff]

end Colex

end PartialOrder

section LinearOrder
variable [LinearOrder ι] {x y : ∀ i, β i} {i : ι} [∀ i, LinearOrder (β i)]

open _root_.Lex in
theorem apply_le_of_toLex (hxy : toLex x ≤ toLex y) (h : ∀ j < i, x j = y j) : x i ≤ y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

open _root_.Colex in
theorem apply_le_of_toColex (hxy : toColex x ≤ toColex y) (h : ∀ j > i, x j = y j) : x i ≤ y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

end LinearOrder

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Lex (∀ a, β a)) where
  bot := ⟨⊥⟩
  bot_le _ := toLex_monotone bot_le

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Colex (∀ a, β a)) where
  bot := ⟨⊥⟩
  bot_le _ := toColex_monotone bot_le

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Lex (∀ a, β a)) where
  top := ⟨⊤⟩
  le_top _ := toLex_monotone le_top

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Colex (∀ a, β a)) where
  top := ⟨⊤⟩
  le_top _ := toColex_monotone le_top

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Lex (∀ a, β a)) where

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Colex (∀ a, β a)) where

instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Lex (∀ i, β i)) where
  dense := by
    rintro ⟨_⟩ ⟨a₂⟩ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨⟨Function.update a₂ _ a⟩, ⟨i, fun j hj ↦ ?_, ?_⟩, i, fun j hj ↦ ?_, ?_⟩
      · rw [h j hj]
        simp [Function.update_of_ne hj.ne a]
      · simp [ha₁]
      · simp [Function.update_of_ne hj.ne a]
      · simp [ha₂]

instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Colex (∀ i, β i)) where
  dense := by
    rintro ⟨a₁⟩ ⟨a₂⟩ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨⟨Function.update a₂ _ a⟩, ⟨i, fun j hj ↦ ?_, ?_⟩, i, fun j hj ↦ ?_, ?_⟩
      · rw [h j hj]
        simp [Function.update_of_ne hj.ne' a]
      · simp [ha₁]
      · simp [Function.update_of_ne hj.ne' a]
      · simp [ha₂]

theorem Lex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Lex (∀ i, β i)) where
  exists_gt a := by
    obtain ⟨b, hb⟩ := exists_gt (a.ofLex i)
    classical exact ⟨⟨Function.update a.ofLex i b⟩, i, fun j hj ↦
      (Function.update_of_ne hj.ne b a.ofLex).symm, by simp [*]⟩

theorem Colex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Colex (∀ i, β i)) where
  exists_gt a := by
    obtain ⟨b, hb⟩ := exists_gt (a.ofColex i)
    classical exact ⟨⟨Function.update a.ofColex i b⟩, i, fun j hj ↦
      (Function.update_of_ne hj.ne' b a.ofColex).symm, by simp [*]⟩

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Lex (∀ i, β i)) where
  exists_gt a :=
    let ⟨_, hb⟩ := exists_gt a.ofLex
    ⟨_, toLex_strictMono hb⟩

instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Colex (∀ i, β i)) where
  exists_gt a :=
    let ⟨_, hb⟩ := exists_gt a.ofColex
    ⟨_, toColex_strictMono hb⟩

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Lex (∀ i, β i)) where
  exists_lt a :=
    let ⟨_, hb⟩ := exists_lt a.ofLex
    ⟨_, toLex_strictMono hb⟩

instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Colex (∀ i, β i)) where
  exists_lt a :=
    let ⟨_, hb⟩ := exists_lt a.ofColex
    ⟨_, toColex_strictMono hb⟩

/-- If we swap two strictly decreasing values in a function, then the result is lexicographically
smaller than the original function. -/
theorem lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f j < f i) : Lex.toLex (f ∘ Equiv.swap i j) < Lex.toLex f :=
  ⟨i, fun _ hik => congr(f $(Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne)), by
    simpa only [Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

/-- If we swap two strictly increasing values in a function, then the result is colexicographically
smaller than the original function. -/
theorem colex_asc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f i < f j) : Colex.toColex (f ∘ Equiv.swap i j) < Colex.toColex f := by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

end Pi
