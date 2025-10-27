/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Common

/-!
# Lexicographic order on Pi types

This file defines the lexicographic and colexicographic orders for Pi types.

* In the lexicographic order, `a` is less than `b` if `a i = b i` for all `i` up to some point
  `k`, and `a k < b k`.
* In the colexicographic order, `a` is less than `b` if `a i = b i` for all `i` above some point
  `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.
-/

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
notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, p i)) => r

theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min _ h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

theorem lex_lt_of_lt [∀ i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

theorem lex_iff_of_unique [Unique ι] [∀ i, LT (β i)] {r} [IsIrrefl ι r] {x y : ∀ i, β i} :
    Pi.Lex r (· < ·) x y ↔ x default < y default := by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

theorem isTrichotomous_lex [∀ i, IsTrichotomous (β i) s] (wf : WellFounded r) :
    IsTrichotomous (∀ i, β i) (Pi.Lex r @s) :=
  { trichotomous := fun a b => by
      rcases eq_or_ne a b with hab | hab
      · exact Or.inr (Or.inl hab)
      · rw [Function.ne_iff] at hab
        let i := wf.min _ hab
        have hri : ∀ j, r j i → a j = b j := by
          intro j
          rw [← not_imp_not]
          exact fun h' => wf.not_lt_min _ _ h'
        have hne : a i ≠ b i := wf.min_mem _ hab
        rcases trichotomous_of s (a i) (b i) with hi | hi
        exacts [Or.inl ⟨i, hri, hi⟩,
          Or.inr <| Or.inr <| ⟨i, fun j hj => (hri j hj).symm, hi.resolve_left hne⟩] }

instance [LT ι] [∀ a, LT (β a)] : LT (Lex (∀ i, β i)) :=
  ⟨Pi.Lex (· < ·) (· < ·)⟩

instance [LT ι] [∀ a, LT (β a)] : LT (Colex (∀ i, β i)) :=
  ⟨Pi.Lex (· > ·) (· < ·)⟩

-- If `Lex` and `Colex` are ever made into one-field structures, the `CoeFun` instance will actually
-- fire. This will make `x i` syntactically equal to `ofLex x i` for `x : Πₗ i, α i`, thus making
-- the following theorems redundant.

@[simp] theorem toLex_apply (x : ∀ i, β i) (i : ι) : toLex x i = x i := rfl
@[simp] theorem ofLex_apply (x : Lex (∀ i, β i)) (i : ι) : ofLex x i = x i := rfl

@[simp] theorem toColex_apply (x : ∀ i, β i) (i : ι) : toColex x i = x i := rfl
@[simp] theorem ofColex_apply (x : Colex (∀ i, β i)) (i : ι) : ofColex x i = x i := rfl

theorem lex_lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Lex (∀ i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

theorem colex_lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Colex (∀ i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

instance Lex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Lex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

instance Colex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Colex (∀ i, β i)) (· < ·) :=
  Lex.isStrictOrder (ι := ιᵒᵈ)

instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Lex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Colex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

/-- `Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`. -/
noncomputable instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (isTrichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)

/-- `Colex (∀ i, α i)` is a linear order if the original order has well-founded `>`. -/
noncomputable instance Colex.linearOrder [LinearOrder ι] [WellFoundedGT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Colex (∀ i, β i)) :=
  Lex.linearOrder (ι := ιᵒᵈ)

theorem lex_le_iff_of_unique [Unique ι] [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]
    {x y : Lex (∀ i, β i)} : x ≤ y ↔ x default ≤ y default := by
  simp_rw [← not_lt, not_iff_not, lex_lt_iff_of_unique]

theorem colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [WellFoundedGT ι] [∀ i, LinearOrder (β i)]
    {x y : Colex (∀ i, β i)} : x ≤ y ↔ x default ≤ y default := by
  simp_rw [← not_lt, not_iff_not, colex_lt_iff_of_unique]

section Lex

variable [LinearOrder ι] [WellFoundedLT ι] [∀ i, PartialOrder (β i)] {x : ∀ i, β i} {i : ι}
  {a : β i}

open Function

theorem toLex_monotone : Monotone (@toLex (∀ i, β i)) := fun a b h =>
  or_iff_not_imp_left.2 fun hne =>
    let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i ≠ b i }
      (Function.ne_iff.1 hne)
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩

theorem toLex_strictMono : StrictMono (@toLex (∀ i, β i)) := fun a b h =>
  let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i ≠ b i }
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

variable [LinearOrder ι] [WellFoundedGT ι] [∀ i, PartialOrder (β i)] {x : ∀ i, β i} {i : ι}
  {a : β i}

open Function

theorem toColex_monotone : Monotone (@toColex (∀ i, β i)) :=
  toLex_monotone (ι := ιᵒᵈ)

theorem toColex_strictMono : StrictMono (@toColex (∀ i, β i)) :=
  toLex_strictMono (ι := ιᵒᵈ)

@[simp]
theorem lt_toColex_update_self_iff : toColex x < toColex (update x i a) ↔ x i < a :=
  lt_toLex_update_self_iff (ι := ιᵒᵈ)

@[simp]
theorem toColex_update_lt_self_iff : toColex (update x i a) < toColex x ↔ a < x i :=
  toLex_update_lt_self_iff (ι := ιᵒᵈ)

@[simp]
theorem le_toColex_update_self_iff : toColex x ≤ toColex (update x i a) ↔ x i ≤ a :=
  le_toLex_update_self_iff (ι := ιᵒᵈ)

@[simp]
theorem toColex_update_le_self_iff : toColex (update x i a) ≤ toColex x ↔ a ≤ x i :=
  toLex_update_le_self_iff (ι := ιᵒᵈ)

end Colex

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Lex (∀ a, β a)) where
  bot := toLex ⊥
  bot_le _ := toLex_monotone bot_le

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Colex (∀ a, β a)) where
  bot := toColex ⊥
  bot_le _ := toColex_monotone bot_le

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Lex (∀ a, β a)) where
  top := toLex ⊤
  le_top _ := toLex_monotone le_top

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Colex (∀ a, β a)) where
  top := toColex ⊤
  le_top _ := toColex_monotone le_top

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Lex (∀ a, β a)) where

instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Colex (∀ a, β a)) where

instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Lex (∀ i, β i)) :=
  ⟨by
    rintro _ a₂ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨Function.update a₂ _ a, ⟨i, fun j hj => ?_, ?_⟩, i, fun j hj => ?_, ?_⟩
      · rw [h j hj]
        dsimp only at hj
        rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]
      · rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]⟩

instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Colex (∀ i, β i)) :=
  inferInstanceAs (DenselyOrdered (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))

theorem Lex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

theorem Colex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Colex (∀ i, β i)) :=
  Lex.noMaxOrder' (ι := ιᵒᵈ) i

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Colex (∀ i, β i)) :=
  inferInstanceAs (NoMaxOrder (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Colex (∀ i, β i)) :=
  inferInstanceAs (NoMinOrder (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))

/-- If we swap two strictly decreasing values in a function, then the result is lexicographically
smaller than the original function. -/
theorem lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f :=
  ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

/-- If we swap two strictly increasing values in a function, then the result is colexicographically
smaller than the original function. -/
theorem colex_asc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f i < f j) : toColex (f ∘ Equiv.swap i j) < toColex f := by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

end Pi
