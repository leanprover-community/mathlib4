/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Common

/-!
# Lexicographic order on Pi types

This file defines the lexicographic order for Pi types. `a` is less than `b` if `a i = b i` for all
`i` up to some point `k`, and `a k < b k`.

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
  and each `β i` is ordered by `s`. -/
protected def Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
basic API, just in case -/
/-- The notation `Πₗ i, α i` refers to a pi type equipped with the lexicographic order. -/
notation3 (prettyPrint := false) "Πₗ "(...)", "r:(scoped p => Lex (∀ i, p i)) => r

@[simp]
theorem toLex_apply (x : ∀ i, β i) (i : ι) : toLex x i = x i :=
  rfl

@[simp]
theorem ofLex_apply (x : Lex (∀ i, β i)) (i : ι) : ofLex x i = x i :=
  rfl

theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min _ h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

theorem lex_lt_of_lt [∀ i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : Pi.Lex r (@fun _ => (· < ·)) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

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
  ⟨Pi.Lex (· < ·) @fun _ => (· < ·)⟩

instance Lex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Lex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Lex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

/-- `Πₗ i, α i` is a linear order if the original order is well-founded. -/
noncomputable instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, LinearOrder (β a)] :
    LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (isTrichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)

section PartialOrder

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

end PartialOrder

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Lex (∀ a, β a)) where
  bot := toLex ⊥
  bot_le _ := toLex_monotone bot_le

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Lex (∀ a, β a)) where
  top := toLex ⊤
  le_top _ := toLex_monotone le_top

instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Lex (∀ a, β a)) :=
  { }

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

theorem Lex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

/-- If we swap two strictly decreasing values in a function, then the result is lexicographically
smaller than the original function. -/
theorem lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f :=
  ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

end Pi
