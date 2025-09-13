/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Data.List.Induction
import Mathlib.Order.MinMax
import Mathlib.Order.WithBot

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f [] = none`

`minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

namespace List

variable {α β : Type*}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp

private theorem foldl_argAux_mem (l) : ∀ a m : α, m ∈ foldl (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l (by simp [eq_comm])
    (by
      intro tl hd ih a m
      simp only [foldl_append, foldl_cons, foldl_nil, argAux]
      cases hf : foldl (argAux r) (some a) tl
      · simp +contextual
      · dsimp only
        split_ifs
        · simp +contextual
        · -- `finish [ih _ _ hf]` closes this goal
          simp only [List.mem_cons] at ih
          rcases ih _ _ hf with rfl | H
          · simp +contextual only [Option.mem_def, Option.some.injEq,
              eq_comm, mem_cons, mem_append, true_or, implies_true]
          · simp +contextual [@eq_comm _ _ m, H])

@[simp]
theorem argAux_self (hr₀ : Irreflexive r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀ _

theorem not_of_mem_foldl_argAux (hr₀ : Irreflexive r) (hr₁ : Transitive r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldl (argAux r) o l → ¬r a m := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append, foldl_cons, foldl_nil, argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_all [hf.1, hf.2, hr₀ _]
  rw [hf, Option.mem_def] at ho
  dsimp only at ho
  split_ifs at ho with hac <;> rcases mem_append.1 hb with h | h <;>
    injection ho with ho <;> subst ho
  · exact fun hba => ih h hf (hr₁ hba hac)
  · simp_all [hr₀ _]
  · exact ih h hf
  · simp_all

end ArgAux

section Preorder

variable [Preorder β] [DecidableLT β] {f : α → β} {l : List α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f [] = none`. -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none

/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f [] = none`. -/
def argmin (f : α → β) (l : List α) :=
  l.foldl (argAux fun b c => f b < f c) none

@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl

@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl

@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl

theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  not_of_mem_foldl_argAux _ (fun x h => lt_irrefl (f x) h)
    (fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy)

theorem not_lt_of_mem_argmin : a ∈ l → m ∈ argmin f l → ¬f a < f m :=
  not_of_mem_foldl_argAux _ (fun x h => lt_irrefl (f x) h)
    (fun x _ _ hxy hyz => lt_trans (a := f x) hxy hyz)

theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c := by
  rw [argmax, argmax]; simp [argAux]

theorem argmin_concat (f : α → β) (a : α) (l : List α) :
    argmin f (l ++ [a]) =
      Option.casesOn (argmin f l) (some a) fun c => if f a < f c then some a else some c :=
  @argmax_concat _ βᵒᵈ _ _ _ _ _

theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by simp
  | hd :: tl, m => by simpa [argmax, argAux] using foldl_argAux_mem _ tl hd m

theorem argmin_mem : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ βᵒᵈ _ _ _

@[simp]
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]

@[simp]
theorem argmin_eq_none : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ βᵒᵈ _ _ _ _

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α → β} {l : List α} {a m : α}

theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_gt <| not_lt_of_mem_argmax ha hm

theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_of_mem_argmax _ βᵒᵈ _ _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite, ← apply_ite]
    dsimp
    split_ifs <;> try rfl
    · exact absurd (lt_trans ‹f a < f m› ‹_›) ‹_›
    · cases (‹f a < f tl›.gt_or_lt _).elim ‹_› ‹_›

theorem argmin_cons (f : α → β) (a : α) (l : List α) :
    argmin f (a :: l) =
      Option.casesOn (argmin f l) (some a) fun c => if f c < f a then some c else some a :=
  @argmax_cons α βᵒᵈ _ _ _ _

variable [DecidableEq α]

theorem index_of_argmax :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.idxOf m ≤ l.idxOf a
  | [], m, _, _, _, _ => by simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [idxOf_cons, argmax_cons, Option.mem_def] at hm ⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
    rw [h] at hm
    dsimp only at hm
    simp only [cond_eq_if, beq_iff_eq]
    obtain ha | ha := ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne _ ‹f hd < f _›.ne
    · rw [if_pos rfl]
      exact Nat.zero_le _

theorem index_of_argmin :
    ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.idxOf m ≤ l.idxOf a :=
  @index_of_argmax _ βᵒᵈ _ _ _

theorem mem_argmax_iff :
    m ∈ argmax f l ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          _root_.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (index_of_argmax harg hml (ham _ (argmax_mem harg)))
        rw [(idxOf_inj hml (argmax_mem harg)).1 this, Option.mem_def]⟩

theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  mem_argmax_iff

theorem mem_argmin_iff :
    m ∈ argmin f l ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.idxOf m ≤ l.idxOf a :=
  @mem_argmax_iff _ βᵒᵈ _ _ _ _ _

theorem argmin_eq_some_iff :
    argmin f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.idxOf m ≤ l.idxOf a :=
  mem_argmin_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [DecidableLT α] {l : List α} {a m : α}

/-- `maximum l` returns a `WithBot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]` -/
def maximum (l : List α) : WithBot α :=
  argmax id l

/-- `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]` -/
def minimum (l : List α) : WithTop α :=
  argmin id l

@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl

@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl

theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem

@[simp]
theorem maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = [] :=
  argmax_eq_none

@[simp]
theorem minimum_eq_top {l : List α} : l.minimum = ⊤ ↔ l = [] :=
  argmin_eq_none

theorem not_maximum_lt_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax

theorem not_lt_minimum_of_mem : a ∈ l → (minimum l : WithTop α) = m → ¬a < m :=
  not_lt_of_mem_argmin

theorem not_maximum_lt_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

theorem not_lt_minimum_of_mem' (ha : a ∈ l) : ¬(a : WithTop α) < minimum l := by
  cases h : l.minimum <;> simp_all [not_lt_minimum_of_mem ha]

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax

theorem minimum_le_of_mem : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  le_of_mem_argmin

theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_gt <| not_maximum_lt_of_mem' ha

theorem minimum_le_of_mem' (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  le_of_not_gt <| not_lt_minimum_of_mem' ha

theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat αᵒᵈ _ _ _

theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l) :=
  List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc]

theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min ↑a (minimum l) :=
  @maximum_cons αᵒᵈ _ _ _

lemma maximum_append (l₁ l₂ : List α) : (l₁ ++ l₂).maximum = max l₁.maximum l₂.maximum := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

lemma minimum_append (l₁ l₂ : List α) : (l₁ ++ l₂).minimum = min l₁.minimum l₂.minimum :=
  @maximum_append αᵒᵈ _ _ _

theorem maximum_le_of_forall_le {b : WithBot α} (h : ∀ a ∈ l, a ≤ b) : l.maximum ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

theorem le_minimum_of_forall_le {b : WithTop α} (h : ∀ a ∈ l, b ≤ a) : b ≤ l.minimum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [minimum_cons, le_min_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

theorem maximum_mono {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₁.maximum ≤ l₂.maximum :=
  maximum_le_of_forall_le fun _ ↦ (le_maximum_of_mem' <| h ·)

theorem minimum_anti {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₂.minimum ≤ l₁.minimum :=
  @maximum_mono αᵒᵈ _ _ _ h

theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m := by
  rw [maximum, ← WithBot.some_eq_coe, argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

theorem minimum_eq_coe_iff : minimum l = m ↔ m ∈ l ∧ ∀ a ∈ l, m ≤ a :=
  @maximum_eq_coe_iff αᵒᵈ _ _ _

theorem coe_le_maximum_iff : a ≤ l.maximum ↔ ∃ b, b ∈ l ∧ a ≤ b := by
  induction l <;> simp [maximum_cons, *]

theorem minimum_le_coe_iff : l.minimum ≤ a ↔ ∃ b, b ∈ l ∧ b ≤ a := by
  induction l <;> simp [minimum_cons, *]

theorem maximum_ne_bot_of_ne_nil (h : l ≠ []) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

theorem minimum_ne_top_of_ne_nil (h : l ≠ []) : l.minimum ≠ ⊤ :=
  @maximum_ne_bot_of_ne_nil αᵒᵈ _ _ h

theorem maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

theorem minimum_ne_top_of_length_pos (h : 0 < l.length) : l.minimum ≠ ⊤ :=
  maximum_ne_bot_of_length_pos (α := αᵒᵈ) h

/-- The maximum value in a non-empty `List`. -/
def maximum_of_length_pos (h : 0 < l.length) : α :=
  WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

/-- The minimum value in a non-empty `List`. -/
def minimum_of_length_pos (h : 0 < l.length) : α :=
  maximum_of_length_pos (α := αᵒᵈ) h

@[simp]
lemma coe_maximum_of_length_pos (h : 0 < l.length) :
    (l.maximum_of_length_pos h : α) = l.maximum :=
  WithBot.coe_unbot _ _

@[simp]
lemma coe_minimum_of_length_pos (h : 0 < l.length) :
    (l.minimum_of_length_pos h : α) = l.minimum :=
  WithTop.coe_untop _ _

@[simp]
theorem le_maximum_of_length_pos_iff {b : α} (h : 0 < l.length) :
    b ≤ maximum_of_length_pos h ↔ b ≤ l.maximum :=
  WithBot.le_unbot_iff _

@[simp]
theorem minimum_of_length_pos_le_iff {b : α} (h : 0 < l.length) :
    minimum_of_length_pos h ≤ b ↔ l.minimum ≤ b :=
  WithTop.untop_le_iff _

theorem maximum_of_length_pos_mem (h : 0 < l.length) :
    maximum_of_length_pos h ∈ l := by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

theorem minimum_of_length_pos_mem (h : 0 < l.length) :
    minimum_of_length_pos h ∈ l :=
  maximum_of_length_pos_mem (α := αᵒᵈ) h

theorem le_maximum_of_length_pos_of_mem (h : a ∈ l) (w : 0 < l.length) :
    a ≤ l.maximum_of_length_pos w := by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

theorem minimum_of_length_pos_le_of_mem (h : a ∈ l) (w : 0 < l.length) :
    l.minimum_of_length_pos w ≤ a :=
  le_maximum_of_length_pos_of_mem (α := αᵒᵈ) h w

theorem getElem_le_maximum_of_length_pos {i : ℕ} (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l[i] ≤ l.maximum_of_length_pos h := by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

theorem minimum_of_length_pos_le_getElem {i : ℕ} (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l.minimum_of_length_pos h ≤ l[i] :=
  getElem_le_maximum_of_length_pos (α := αᵒᵈ) w

#adaptation_note
/-- 2025-08-14: We should stop using `max?_eq_some_iff_legacy` below, by connecting up Mathlib's
order typeclasses with the new classes in Lean. -/
set_option linter.deprecated false in
lemma getD_max?_eq_unbotD_maximum (l : List α) (d : α) : l.max?.getD d = l.maximum.unbotD d := by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· ≤ ·) := ⟨fun _ _ => _root_.le_antisymm⟩
      rw [List.max?_eq_some_iff_legacy] at hz
      · rw [Option.getD_some]
        exact _root_.le_antisymm (hy.right _ hz.left) (hz.right _ hy.left)
      all_goals simp [le_total]

lemma getD_min?_eq_untopD_minimum (l : List α) (d : α) : l.min?.getD d = l.minimum.untopD d :=
  getD_max?_eq_unbotD_maximum (α := αᵒᵈ) _ _

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

@[simp]
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a := by
  induction l with
  | nil => simp
  | cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x <| mem_cons_of_mem _ hx

theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ := by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

end OrderBot

section OrderTop

variable [OrderTop α] {l : List α}

@[simp]
theorem foldr_min_of_ne_nil (h : l ≠ []) : ↑(l.foldr min ⊤) = l.minimum :=
  @foldr_max_of_ne_nil αᵒᵈ _ _ _ h

theorem le_min_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, a ≤ x) : a ≤ l.foldr min ⊤ :=
  @max_le_of_forall_le αᵒᵈ _ _ _ _ h

theorem min_le_of_le (l : List α) (a : α) {x : α} (hx : x ∈ l) (h : x ≤ a) : l.foldr min ⊤ ≤ a :=
  @le_max_of_le αᵒᵈ _ _ _ _ _ hx h

end OrderTop

/-- If `a ≤ x` for some `x` in the list `l`, and `b : α`, then `a ≤ l.foldr max b`. -/
theorem le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : a ≤ x) :
    a ≤ l.foldr max b := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

theorem min_le_of_le' {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : x ≤ a) : l.foldr min b ≤ a :=
  @le_max_of_le' αᵒᵈ _ _ _ _ _ hx h

end Fold

end List
