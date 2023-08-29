/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite

#align_import combinatorics.hall.finite from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# Hall's Marriage Theorem for finite index types

This module proves the basic form of Hall's theorem.
In contrast to the theorem described in `Combinatorics.Hall.Basic`, this
version requires that the indexed family `t : ι → Finset α` have `ι` be finite.
The `Combinatorics.Hall.Basic` module applies a compactness argument to this version
to remove the `Finite` constraint on `ι`.

The modules are split like this since the generalized statement
depends on the topology and category theory libraries, but the finite
case in this module has few dependencies.

A description of this formalization is in [Gusakov2021].

## Main statements

* `Finset.all_card_le_biUnion_card_iff_existsInjective'` is Hall's theorem with
  a finite index set.  This is elsewhere generalized to
  `Finset.all_card_le_biUnion_card_iff_existsInjective`.

## Tags

Hall's Marriage Theorem, indexed families
-/


open Finset

universe u v

namespace HallMarriageTheorem

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → s.card < (s.biUnion t).card)
    (s' : Finset { x' : ι | x' ≠ x }) : s'.card ≤ (s'.biUnion fun x' => (t x').erase a).card := by
  haveI := Classical.decEq ι
  -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => erase (t ↑x') a)
  specialize ha (s'.image fun z => z.1)
  -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => erase (t ↑x') a)
  rw [Nonempty.image_iff, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => erase (t ↑x') a)
  by_cases he : s'.Nonempty
  -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => erase (t ↑x') a)
  · have ha' : s'.card < (s'.biUnion fun x => t x).card := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, exists_prop, SetCoe.exists, exists_and_right,
        exists_eq_right, Subtype.coe_mk]
    rw [← erase_biUnion]
    -- ⊢ card s' ≤ card (erase (Finset.biUnion s' fun x' => t ↑x') a)
    by_cases hb : a ∈ s'.biUnion fun x => t x
    -- ⊢ card s' ≤ card (erase (Finset.biUnion s' fun x' => t ↑x') a)
    · rw [card_erase_of_mem hb]
      -- ⊢ card s' ≤ card (Finset.biUnion s' fun x_1 => t ↑x_1) - 1
      exact Nat.le_pred_of_lt ha'
      -- 🎉 no goals
    · rw [erase_eq_of_not_mem hb]
      -- ⊢ card s' ≤ card (Finset.biUnion s' fun x_1 => t ↑x_1)
      exact Nat.le_of_lt ha'
      -- 🎉 no goals
  · rw [nonempty_iff_ne_empty, not_not] at he
    -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => erase (t ↑x') a)
    subst s'
    -- ⊢ card ∅ ≤ card (Finset.biUnion ∅ fun x' => erase (t ↑x') a)
    simp
    -- 🎉 no goals
#align hall_marriage_theorem.hall_cond_of_erase HallMarriageTheorem.hall_cond_of_erase

/-- First case of the inductive step: assuming that
`∀ (s : Finset ι), s.Nonempty → s ≠ univ → s.card < (s.biUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card)
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', s'.card ≤ (s'.biUnion t').card) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → s.card < (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  haveI := Classical.decEq ι
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Choose an arbitrary element `x : ι` and `y : t x`.
  let x := Classical.arbitrary ι
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ (Finset.biUnion {x} t).card := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]

  choose y hy using tx_ne
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Restrict to everything except `x` and `y`.
  let ι' := { x' : ι | x' ≠ x }
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  let t' : ι' → Finset α := fun x' => (t x').erase y
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]

  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Extend the resulting function.
  refine' ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, _, _⟩
  -- ⊢ Function.Injective fun z => if h : z = x then y else f' { val := z, property …
  · rintro z₁ z₂
    -- ⊢ (fun z => if h : z = x then y else f' { val := z, property := h }) z₁ = (fun …
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;> simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
    -- ⊢ (fun z => if h : z = x then y else f' { val := z, property := h }) z₁ = (fun …
                             -- ⊢ (fun z => if h : z = x then y else f' { val := z, property := h }) z₁ = (fun …
                             -- ⊢ (fun z => if h : z = x then y else f' { val := z, property := h }) z₁ = (fun …
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  · intro z
    -- ⊢ (fun z => if h : z = x then y else f' { val := z, property := h }) z ∈ t z
    simp only [ne_eq, Set.mem_setOf_eq]
    -- ⊢ (if h : z = Classical.arbitrary ι then y else f' { val := z, property := h } …
    split_ifs with hz
    -- ⊢ y ∈ t z
    · rwa [hz]
      -- 🎉 no goals
    · specialize hfr ⟨z, hz⟩
      -- ⊢ f' { val := z, property := hz } ∈ t z
      rw [mem_erase] at hfr
      -- ⊢ f' { val := z, property := hz } ∈ t z
      exact hfr.2
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hall_marriage_theorem.hall_hard_inductive_step_A HallMarriageTheorem.hall_hard_inductive_step_A

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) (s' : Finset (s : Set ι)) :
    s'.card ≤ (s'.biUnion fun a' => t a').card := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp
#align hall_marriage_theorem.hall_cond_of_restrict HallMarriageTheorem.hall_cond_of_restrict

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : s.card = (s.biUnion t).card) (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card)
    (s' : Finset (sᶜ : Set ι)) : s'.card ≤ (s'.biUnion fun x' => t x' \ s.biUnion t).card := by
  haveI := Classical.decEq ι
  -- ⊢ card s' ≤ card (Finset.biUnion s' fun x' => t ↑x' \ Finset.biUnion s t)
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, exists_prop, SetCoe.exists, exists_and_right,
      exists_eq_right, Subtype.coe_mk]
    intro x hx hc _
    exact absurd hx hc
  have : s'.card = (s ∪ s'.image fun z => z.1).card - s.card := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective]
  rw [this, hus]
  -- ⊢ card (s ∪ image (fun z => ↑z) s') - card (Finset.biUnion s t) ≤ card (Finset …
  refine' (tsub_le_tsub_right (ht _) _).trans _
  -- ⊢ card (Finset.biUnion (s ∪ image (fun z => ↑z) s') t) - card (Finset.biUnion  …
  rw [← card_sdiff]
  -- ⊢ card (Finset.biUnion (s ∪ image (fun z => ↑z) s') t \ Finset.biUnion s t) ≤  …
  · refine' (card_le_of_subset _).trans le_rfl
    -- ⊢ Finset.biUnion (s ∪ image (fun z => ↑z) s') t \ Finset.biUnion s t ⊆ Finset. …
    intro t
    -- ⊢ t ∈ Finset.biUnion (s ∪ image (fun z => ↑z) s') t✝ \ Finset.biUnion s t✝ → t …
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union, exists_and_right,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    -- ⊢ ∃ a, a ∈ s' ∧ t ∈ t✝ ↑a ∧ ∀ (x : ι), ¬(x ∈ s ∧ t ∈ t✝ x)
    · exact False.elim <| (hs x) <| And.intro hx rat
      -- 🎉 no goals
    · use x', hx', rat, hs
      -- 🎉 no goals
  · apply biUnion_subset_biUnion_of_subset_left
    -- ⊢ s ⊆ s ∪ image (fun z => ↑z) s'
    apply subset_union_left
    -- 🎉 no goals
#align hall_marriage_theorem.hall_cond_of_compl HallMarriageTheorem.hall_cond_of_compl

/-- Second case of the inductive step: assuming that
`∃ (s : Finset ι), s ≠ univ → s.card = (s.biUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card)
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', s'.card ≤ (s'.biUnion t').card) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : s.card = (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI := Classical.decEq ι
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Restrict to `s`
  rw [Nat.add_one] at hn
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = s.card := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Restrict to `sᶜ` in the domain and `(s.biUnion t)ᶜ` in the codomain.
  set ι'' := (s : Set ι)ᶜ
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  -- Put them together
  have f'_mem_biUnion : ∀ (x') (hx' : x' ∈ s), f' ⟨x', hx'⟩ ∈ s.biUnion t := by
    intro x' hx'
    rw [mem_biUnion]
    exact ⟨x', hx', hsf' _⟩
  have f''_not_mem_biUnion : ∀ (x'') (hx'' : ¬x'' ∈ s), ¬f'' ⟨x'', hx''⟩ ∈ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : ¬x'' ∈ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    intro x x' hx' hx'' h
    apply f''_not_mem_biUnion x' hx''
    rw [← h]
    apply f'_mem_biUnion x
  refine' ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩
  -- ⊢ Function.Injective fun x => if h : x ∈ s then f' { val := x, property := h } …
  · refine' hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
    -- 🎉 no goals
  · intro x
    -- ⊢ (fun x => if h : x ∈ s then f' { val := x, property := h } else f'' { val := …
    simp only [of_eq_true]
    -- ⊢ (if h : x ∈ s then f' { val := x, property := h } else f'' { val := x, prope …
    split_ifs with h
    -- ⊢ f' { val := x, property := h } ∈ t x
    · exact hsf' ⟨x, h⟩
      -- 🎉 no goals
    · exact sdiff_subset _ _ (hsf'' ⟨x, h⟩)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hall_marriage_theorem.hall_hard_inductive_step_B HallMarriageTheorem.hall_hard_inductive_step_B

end Fintype

variable [Finite ι]

/-- Here we combine the two inductive steps into a full strong induction proof,
completing the proof the harder direction of **Hall's Marriage Theorem**.
-/
theorem hall_hard_inductive (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  induction' hn : Fintype.card ι using Nat.strong_induction_on with n ih generalizing ι
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  rcases n with (_ | _)
  -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
  · rw [Fintype.card_eq_zero_iff] at hn
    -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
    -- 🎉 no goals
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ _ →
        (∀ s' : Finset ι', s'.card ≤ (s'.biUnion t').card) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → s.card < (s.biUnion t).card
    -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
    · refine' hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
      -- 🎉 no goals
    · push_neg at h
      -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
      rcases h with ⟨s, sne, snu, sle⟩
      -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)
#align hall_marriage_theorem.hall_hard_inductive HallMarriageTheorem.hall_hard_inductive

end HallMarriageTheorem

/-- This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → Finset α` with `ι` finite.
It states that there is a set of distinct representatives if and only
if every union of `k` of the sets has at least `k` elements.

See `Finset.all_card_le_biUnion_card_iff_exists_injective` for a version
where the `Finite ι` constraint is removed.
-/
theorem Finset.all_card_le_biUnion_card_iff_existsInjective' {ι α : Type*} [Finite ι]
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  -- ⊢ (∀ (s : Finset ι), card s ≤ card (Finset.biUnion s t)) → ∃ f, Function.Injec …
  · exact HallMarriageTheorem.hall_hard_inductive
    -- 🎉 no goals
  · rintro ⟨f, hf₁, hf₂⟩ s
    -- ⊢ card s ≤ card (Finset.biUnion s t)
    rw [← card_image_of_injective s hf₁]
    -- ⊢ card (image f s) ≤ card (Finset.biUnion s t)
    apply card_le_of_subset
    -- ⊢ image f s ⊆ Finset.biUnion s t
    intro
    -- ⊢ a✝ ∈ image f s → a✝ ∈ Finset.biUnion s t
    rw [mem_image, mem_biUnion]
    -- ⊢ (∃ a, a ∈ s ∧ f a = a✝) → ∃ a, a ∈ s ∧ a✝ ∈ t a
    rintro ⟨x, hx, rfl⟩
    -- ⊢ ∃ a, a ∈ s ∧ f x ∈ t a
    exact ⟨x, hx, hf₂ x⟩
    -- 🎉 no goals
#align finset.all_card_le_bUnion_card_iff_exists_injective' Finset.all_card_le_biUnion_card_iff_existsInjective'
