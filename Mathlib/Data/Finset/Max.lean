/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Maximum and minimum of finite sets
-/

assert_not_exists OrderedCommMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### max and min of finite sets -/

section MaxMin

variable [LinearOrder α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `WithBot α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max (s : Finset α) : WithBot α :=
  sup s (↑)

theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑) :=
  rfl

theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑) :=
  rfl

@[simp]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl

@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max :=
  fold_insert_idem

@[simp]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_empty_eq]
  exact max_insert

lemma max_pair (a b : α) :
    Finset.max {a, b} = max (↑a) (↑b) := by
  simp

theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b := by
  obtain ⟨b, h, _⟩ := le_sup (α := WithBot α) h _ rfl
  exact ⟨b, h⟩

theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨_, h⟩ := h
  max_of_mem h

theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h ↦ s.eq_empty_or_nonempty.elim id fun H ↦ by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h ↦ h.symm ▸ max_empty⟩

theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s := by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | insert b s _ ih =>
    intro a h
    by_cases p : b = a
    · induction p
      exact mem_insert_self b s
    · rcases max_choice (↑b) s.max with q | q <;> rw [max_insert, q] at h
      · cases h
        cases p rfl
      · exact mem_insert_of_mem (ih h)

theorem le_max {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as

theorem notMem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_ge

@[deprecated (since := "2025-05-23")] alias not_mem_of_max_lt_coe := notMem_of_max_lt_coe

theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (le_max h₁).trans h₂.le

theorem notMem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
  Finset.notMem_of_max_lt_coe <| h₂.trans_lt <| WithBot.coe_lt_coe.mpr h₁

@[deprecated (since := "2025-05-23")] alias not_mem_of_max_lt := notMem_of_max_lt

theorem max_union {s t : Finset α} : (s ∪ t).max = s.max ⊔ t.max := sup_union

@[gcongr]
theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st

protected theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a ∈ s, (a : WithBot α) ≤ M) :
    s.max ≤ M :=
  Finset.sup_le st

@[simp]
protected lemma max_le_iff {m : WithBot α} {s : Finset α} : s.max ≤ m ↔ ∀ a ∈ s, a ≤ m :=
  Finset.sup_le_iff

@[simp]
protected lemma max_eq_top [OrderTop α] {s : Finset α} : s.max = ⊤ ↔ ⊤ ∈ s :=
  Finset.sup_eq_top_iff.trans <| by simp

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `WithTop α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min (s : Finset α) : WithTop α :=
  inf s (↑)

theorem min_eq_inf_withTop (s : Finset α) : s.min = inf s (↑) :=
  rfl

@[simp]
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl

@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem

@[simp]
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) := by
  rw [← insert_empty_eq]
  exact min_insert

lemma min_pair (a b : α) :
    Finset.min {a, b} = min (↑a) (↑b) := by
  simp

theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b := by
  obtain ⟨b, h, _⟩ := inf_le (α := WithTop α) h _ rfl
  exact ⟨b, h⟩

theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨_, h⟩ := h
  min_of_mem h

@[simp]
theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ := by
  simp [Finset.min, eq_empty_iff_forall_notMem]

theorem mem_of_min {s : Finset α} : ∀ {a : α}, s.min = a → a ∈ s :=
  @mem_of_max αᵒᵈ _ s

theorem min_le {a : α} {s : Finset α} (as : a ∈ s) : s.min ≤ a :=
  inf_le as

theorem notMem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s :=
  mt min_le h.not_ge

@[deprecated (since := "2025-05-23")] alias not_mem_of_coe_lt_min := notMem_of_coe_lt_min

theorem min_le_of_eq {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : s.min = a) : a ≤ b :=
  WithTop.coe_le_coe.mp <| h₂.ge.trans (min_le h₁)

theorem notMem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) : a ∉ s :=
  Finset.notMem_of_coe_lt_min <| (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm

@[deprecated (since := "2025-05-23")] alias not_mem_of_lt_min := notMem_of_lt_min

theorem min_union {s t : Finset α} : (s ∪ t).min = s.min ⊓ t.min := inf_union

@[gcongr]
theorem min_mono {s t : Finset α} (st : s ⊆ t) : t.min ≤ s.min :=
  inf_mono st

protected theorem le_min {m : WithTop α} {s : Finset α} (st : ∀ a : α, a ∈ s → m ≤ a) : m ≤ s.min :=
  Finset.le_inf st

@[simp]
protected theorem le_min_iff {m : WithTop α} {s : Finset α} : m ≤ s.min ↔ ∀ a ∈ s, m ≤ a :=
  Finset.le_inf_iff

@[simp]
protected theorem min_eq_bot [OrderBot α] {s : Finset α} : s.min = ⊥ ↔ ⊥ ∈ s :=
  Finset.max_eq_top (α := αᵒᵈ)

/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `WithTop α`. -/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id

/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id

variable (s : Finset α) (H : s.Nonempty) {x : α}

theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by simp only [Finset.min, min', id_eq, coe_inf', Function.comp_def]

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _

theorem isLeast_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩

@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
  le_isGLB_iff (isLeast_min' s H).isGLB

/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']

theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _

theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB

@[simp]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩

@[simp]
theorem lt_min'_iff : x < s.min' H ↔ ∀ y ∈ s, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _

theorem max'_eq_sup' : s.max' H = s.sup' H id := rfl

theorem min'_eq_inf' : s.min' H = s.inf' H id := rfl

/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']

lemma min'_eq_iff (a : α) : s.min' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → a ≤ b :=
  ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩), fun h ↦ le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

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
    s.min' (Finset.card_pos.1 <| by cutsat) < s.max' (Finset.card_pos.1 <| by cutsat) := by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab

theorem max'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ ∪ s₂).max' (h₁.mono subset_union_left) = s₁.max' h₁ ⊔ s₂.max' h₂ := sup'_union h₁ h₂ id

theorem min'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ ∪ s₂).min' (h₁.mono subset_union_left) = s₁.min' h₁ ⊓ s₂.min' h₂ := inf'_union h₁ h₂ id

theorem map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  exact congr_fun WithBot.map_id _

theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _

theorem map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  exact congr_fun WithBot.map_id _

theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _

theorem ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

theorem toDual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))

theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))

@[simp] theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max a (s.max' H) :=
  (isGreatest_max' _ _).unique <| by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _

@[simp] theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min a (s.min' H) :=
  (isLeast_min' _ _).unique <| by
    rw [coe_insert]
    exact (isLeast_min' _ _).insert _

lemma min'_pair (a b : α) :
    min' {a, b} (insert_nonempty _ _) = min a b := by
  simp

lemma max'_pair (a b : α) :
    max' {a, b} (insert_nonempty _ _) = max a b := by
  simp

theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) :
    a < s.max' H :=
  lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| notMem_erase _ _

theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.min' H)) :
    s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

/-- To rewrite from right to left, use `Monotone.map_finset_max'`. -/
@[simp]
theorem max'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' h.of_image) := by
  simp only [max', sup'_image]
  exact .symm <| comp_sup'_eq_sup'_comp _ _ fun _ _ ↦ hf.map_max

/-- A version of `Finset.max'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/
lemma _root_.Monotone.map_finset_max' [LinearOrder β] {f : α → β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.max' h) = (s.image f).max' (h.image f) :=
  .symm <| max'_image hf ..

/-- To rewrite from right to left, use `Monotone.map_finset_min'`. -/
@[simp]
theorem min'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' h.of_image) := by
  simp only [min', inf'_image]
  exact .symm <| comp_inf'_eq_inf'_comp _ _ fun _ _ ↦ hf.map_min

/-- A version of `Finset.min'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/
lemma _root_.Monotone.map_finset_min' [LinearOrder β] {f : α → β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.min' h) = (s.image f).min' (h.image f) :=
  .symm <| min'_image hf ..

theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id

theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id

theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image (↑) : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩

theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min ∈ (s.image (↑) : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩

theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image (↑)) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe

theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min ∈ (insert ⊤ (s.image (↑)) : Finset (WithTop α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe

theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)

theorem min'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).min' s0 ≠ x :=
  ne_of_mem_erase (min'_mem _ s0)

theorem max_erase_ne_self {s : Finset α} : (s.erase x).max ≠ x := by
  by_cases s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [not_nonempty_iff_eq_empty.mp s0, max_empty]
    exact WithBot.bot_ne_coe

theorem min_erase_ne_self {s : Finset α} : (s.erase x).min ≠ x := by
  apply mt (congr_arg (WithTop.map toDual))
  rw [map_toDual_min, image_erase toDual.injective, WithTop.map_coe]
  apply max_erase_ne_self

theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
  ⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ <| mem_filter.2 ⟨hzs, by simpa⟩⟩

theorem exists_next_left {x : α} {s : Finset α} (h : ∃ y ∈ s, y < x) :
    ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y :=
  @exists_next_right αᵒᵈ _ x s h

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
theorem card_le_diff_of_interleaved {s t : Finset α}
    (h :
      ∀ᵉ (x ∈ s) (y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, x < a) → p s → p (insert a s)) : p s := by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact h0
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact step _ _ (fun x ↦ s.lt_max'_of_mem_erase_max' hne) (ih _ H)

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max αᵒᵈ _ _ _ s h0 step

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) : p s := by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, h0]
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine step _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f a ≤ f x) → p s → p (insert a s)) : p s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s h0 step

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩

theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h

end ExistsMaxMin

theorem isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i := by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))

theorem isLUB_iff_isGreatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @isGLB_iff_isLeast αᵒᵈ _ i s hs

theorem isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1

theorem isLUB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s :=
  @isGLB_mem αᵒᵈ _ i s his hs

end Finset

theorem Multiset.exists_max_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α}
    (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f z ≤ f y := by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz ↦ hy _ (mem_toFinset.mpr hz)⟩

theorem Multiset.exists_min_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α}
    (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f y ≤ f z :=
  @exists_max_image α Rᵒᵈ _ f s hs
