/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Maximum and minimum of finite sets
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {α β ι : Type*}

namespace Finset

/-! ### max and min of finite sets -/

section MaxMin

variable [LinearOrder α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `WithBot α`. If you want to get an element of `α`, see
`s.max'`. -/
@[to_dual
/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `WithTop α`. If you want to get an element of `α`, see
`s.min'`. -/]
protected def max (s : Finset α) : WithBot α :=
  sup s (↑)

@[to_dual]
theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑) :=
  rfl

@[to_dual]
theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑) :=
  rfl

@[to_dual (attr := simp)]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl

@[to_dual (attr := simp, grind =)]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max :=
  fold_insert_idem

@[to_dual (attr := simp)]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_empty_eq]
  exact max_insert

@[to_dual]
lemma max_pair (a b : α) :
    Finset.max {a, b} = max (↑a) (↑b) := by
  simp

@[to_dual]
theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b :=
  let ⟨b, h, _⟩ := WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) _ rfl; ⟨b, h⟩

@[to_dual]
theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨_, h⟩ := h
  max_of_mem h

@[to_dual]
theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h ↦ s.eq_empty_or_nonempty.elim id fun H ↦ by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h ↦ h.symm ▸ max_empty⟩

@[to_dual]
theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s := by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | _ a s _ h =>
    intro a ha
    simp only [max_insert] at ha
    cases max_eq_iff.mp ha <;> simp_all

@[to_dual min_le]
theorem le_max {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as

@[to_dual notMem_of_coe_lt_min]
theorem notMem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_ge

@[to_dual min_le_of_eq]
theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (le_max h₁).trans h₂.le

@[to_dual notMem_of_lt_min]
theorem notMem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
  Finset.notMem_of_max_lt_coe <| h₂.trans_lt <| WithBot.coe_lt_coe.mpr h₁

@[to_dual]
theorem max_union {s t : Finset α} : (s ∪ t).max = s.max ⊔ t.max := sup_union

@[to_dual (attr := gcongr)]
theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st

@[to_dual le_min]
protected theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a ∈ s, (a : WithBot α) ≤ M) :
    s.max ≤ M :=
  Finset.sup_le st

@[to_dual (attr := simp) le_min_iff]
protected lemma max_le_iff {m : WithBot α} {s : Finset α} : s.max ≤ m ↔ ∀ a ∈ s, a ≤ m :=
  Finset.sup_le_iff

@[to_dual (attr := simp)]
protected lemma max_eq_top [OrderTop α] {s : Finset α} : s.max = ⊤ ↔ ⊤ ∈ s :=
  Finset.sup_eq_top_iff.trans <| by simp

/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
@[to_dual
/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `WithTop α`. -/]
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id

variable (s : Finset α) (H : s.Nonempty) {x : α}

@[to_dual]
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

@[to_dual min'_le]
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

@[to_dual le_min']
theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _

@[to_dual]
theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[to_dual (attr := simp) le_min'_iff]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB

@[to_dual (attr := simp) lt_min'_iff]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩

@[to_dual]
theorem max'_eq_sup' : s.max' H = s.sup' H id := rfl

/-- `{a}.max' _` is `a`. -/
@[to_dual (attr := simp) /-- `{a}.min' _` is `a`. -/]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']

@[to_dual]
lemma max'_eq_iff (a : α) : s.max' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → b ≤ a :=
  ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩), fun h ↦ le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

theorem min'_le_max' (hs : s.Nonempty) : s.min' hs ≤ s.max' hs := min'_le _ _ (max'_mem _ _)

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3

/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.1 <| by lia) < s.max' (Finset.card_pos.1 <| by lia) := by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab

@[to_dual]
theorem max'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ ∪ s₂).max' (h₁.mono subset_union_left) = s₁.max' h₁ ⊔ s₂.max' h₂ := sup'_union h₁ h₂ id

@[to_dual]
theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _

@[to_dual]
theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _

@[to_dual]
theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

@[to_dual]
theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

@[to_dual]
theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))

@[to_dual (attr := simp)] theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max a (s.max' H) :=
  (isGreatest_max' _ _).unique <| by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _

@[to_dual]
lemma max'_pair (a b : α) :
    max' {a, b} (insert_nonempty _ _) = max a b := by
  simp

@[to_dual min'_lt_of_mem_erase_min']
theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) :
    a < s.max' H :=
  lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| notMem_erase _ _

/-- To rewrite from right to left, use `Monotone.map_finset_max'`. -/
@[to_dual (attr := simp) /-- To rewrite from right to left, use `Monotone.map_finset_min'`. -/]
theorem max'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' h.of_image) := by
  simp only [max', sup'_image]
  exact .symm <| apply_sup'_eq_sup'_comp _ _ fun _ _ ↦ hf.map_max

/-- A version of `Finset.max'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/
@[to_dual
/-- A version of `Finset.min'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/]
lemma _root_.Monotone.map_finset_max' [LinearOrder β] {f : α → β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.max' h) = (s.image f).max' (h.image f) :=
  .symm <| max'_image hf ..

@[to_dual]
theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id

@[to_dual]
theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image (↑) : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩

@[to_dual]
theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image (↑)) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe

@[to_dual]
theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)

@[to_dual]
theorem max_erase_ne_self {s : Finset α} : (s.erase x).max ≠ x := by
  by_cases! s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [s0, max_empty]
    exact WithBot.bot_ne_coe

@[to_dual exists_next_left]
theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
  ⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ <| mem_filter.2 ⟨hzs, by simpa⟩⟩

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card t + 1`. -/
theorem card_le_of_interleaved {s t : Finset α}
    (h : ∀ᵉ (x ∈ s) (y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 := by
  replace h : ∀ᵉ (x ∈ s) (y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y := by
    intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
    rcases h x hx a has hxa fun z hzs hz => hz.2.not_ge <| ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
    exact ⟨b, hbt, hxb, hba.trans_le <| ha _ hy hxy⟩
  set f : α → WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x ≤ a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
          WithTop.coe_lt_coe.2 <| hay.trans (by simpa using (mem_filter.1 hb).2)
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ ≤ (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
      card_mono <| image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ ≤ t.card + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card (t \ s) + 1`. -/
theorem card_le_sdiff_of_interleaved {s t : Finset α}
    (h :
      ∀ᵉ (x ∈ s) (y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

@[deprecated (since := "2026-06-03")]
alias card_le_diff_of_interleaved := card_le_sdiff_of_interleaved

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[to_dual (attr := elab_as_elim)
/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/]
theorem induction_on_max
    [DecidableEq α] {motive : Finset α → Prop} (s : Finset α) (empty : motive ∅)
    (insert : ∀ a s, (∀ x ∈ s, x < a) → motive s → motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact empty
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact insert _ _ (fun x ↦ s.lt_max'_of_mem_erase_max' hne) (ih _ H)

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[to_dual (attr := elab_as_elim)
/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/]
theorem induction_on_max_value
    [DecidableEq ι] (f : ι → α) {motive : Finset ι → Prop} (s : Finset ι) (empty : motive ∅)
    (insert : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → motive s → motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, empty]
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine insert _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

@[to_dual]
theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩

end ExistsMaxMin

@[to_dual]
theorem isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i := by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))

@[to_dual]
theorem isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1

end Finset

@[to_dual]
theorem Multiset.exists_max_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α}
    (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f z ≤ f y := by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz ↦ hy _ (mem_toFinset.mpr hz)⟩
