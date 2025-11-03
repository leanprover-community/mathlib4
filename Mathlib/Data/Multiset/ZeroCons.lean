/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Defs
import Mathlib.Order.BoundedOrder.Basic

/-!
# Definition of `0` and `::ₘ`

This file defines constructors for multisets:

* `Zero (Multiset α)` instance: the empty multiset
* `Multiset.cons`: add one element to a multiset
* `Singleton α (Multiset α)` instance: multiset with one element

It also defines the following predicates on multisets:

* `Multiset.Rel`: `Rel r s t` lifts the relation `r` between two elements to a relation between `s`
  and `t`, s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`.

## Notation

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.

## Main results

* `Multiset.rec`: recursion on adding one element to a multiset at a time.
-/

-- No algebra should be required
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Empty multiset -/


/-- `0 : Multiset α` is the empty set -/
protected def zero : Multiset α :=
  @nil α

instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

instance : EmptyCollection (Multiset α) :=
  ⟨0⟩

instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩

instance [IsEmpty α] : Unique (Multiset α) where
  default := 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]
theorem coe_nil : (@nil α : Multiset α) = 0 :=
  rfl

@[simp]
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil

theorem coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.isEmpty :=
  Iff.trans (coe_eq_zero l) isEmpty_iff.symm

/-! ### `Multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more instance of `a`. -/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

instance : Insert α (Multiset α) :=
  ⟨cons⟩

@[simp]
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp]
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl

@[simp]
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
      singleton_perm_singleton.1 <| (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]
theorem cons_inj_right (a : α) : ∀ {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]
protected theorem induction {p : Multiset α → Prop} (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : ∀ s, p s := by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : p s :=
  Multiset.induction empty cons s

theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  Quot.inductionOn s fun _ => Quotient.sound <| Perm.swap _ _ _

section Rec

variable {C : Multiset α → Sort*}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `Multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected
def rec (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b))
    (m : Multiset α) : C m :=
  Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ ↦ by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

/-- Companion to `Multiset.rec` with more convenient argument order. -/
@[elab_as_elim]
protected
def recOn (m : Multiset α) (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)) :
    C m :=
  Multiset.rec C_0 C_cons C_cons_heq m

variable {C_0 : C 0} {C_cons : ∀ a m, C m → C (a ::ₘ m)}
  {C_cons_heq :
    ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)}

@[simp]
theorem recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp]
theorem recOn_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  Quotient.inductionOn m fun _ => rfl

end Rec

section Mem

@[simp, grind =]
theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun _ => List.mem_cons

theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  mem_cons.2 <| Or.inr h

theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)

theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
    (∀ x ∈ a ::ₘ s, p x) ↔ p a ∧ ∀ x ∈ s, p x :=
  Quotient.inductionOn' s fun _ => List.forall_mem_cons

theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
  Quot.inductionOn s fun l (h : a ∈ l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp, grind ←]
theorem notMem_zero (a : α) : a ∉ (0 : Multiset α) :=
  List.not_mem_nil

@[deprecated (since := "2025-05-23")] alias not_mem_zero := notMem_zero

theorem eq_zero_of_forall_notMem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

@[deprecated (since := "2025-05-23")] alias eq_zero_of_forall_not_mem := eq_zero_of_forall_notMem

theorem eq_zero_iff_forall_notMem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩

@[deprecated (since := "2025-05-23")] alias eq_zero_iff_forall_not_mem := eq_zero_iff_forall_notMem

theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
  Quot.inductionOn s fun l hl =>
    match l, hl with
    | [], h => False.elim <| h rfl
    | a :: l, _ => ⟨a, by simp⟩

theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m := fun h =>
  have : a ∈ (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  notMem_zero _ this

@[simp]
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 :=
  zero_ne_cons.symm

theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs := by
  haveI : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a ∈ b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a ∈ bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_and, ne_eq, not_false_eq_true, cons_inj_right, exists_eq_right',
        true_and, false_or]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by simp [eq, hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by rwa [cons_swap]
      simpa using this
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨_, cs, eq₁, eq₂⟩)
    · simp [*]
    · simp [*, cons_swap a b]

end Mem

/-! ### Singleton -/


instance : Singleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩

instance : LawfulSingleton α (Multiset α) :=
  ⟨fun _ => rfl⟩

@[simp]
theorem cons_zero (a : α) : a ::ₘ 0 = {a} :=
  rfl

@[simp, norm_cast]
theorem coe_singleton (a : α) : ([a] : Multiset α) = {a} :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]

theorem mem_singleton_self (a : α) : a ∈ ({a} : Multiset α) := by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]
theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b := by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]
theorem coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a] := by
  rw [← coe_singleton, coe_eq_coe, List.perm_singleton]

@[simp]
theorem singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧ m = 0 := by
  rw [← cons_zero, cons_eq_cons]
  simp [eq_comm]

theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

@[simp]
theorem zero_subset (s : Multiset α) : 0 ⊆ s := fun _ => not_mem_nil.elim

theorem subset_cons (s : Multiset α) (a : α) : s ⊆ a ::ₘ s := fun _ => mem_cons_of_mem

theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
  ⟨subset_cons _ _, fun h => ha <| h <| mem_cons_self _ _⟩

@[simp]
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp [subset_iff, or_imp, forall_and]

theorem cons_subset_cons {a : α} {s t : Multiset α} : s ⊆ t → a ::ₘ s ⊆ a ::ₘ t :=
  Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _

theorem eq_zero_of_subset_zero {s : Multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_notMem fun _ hx ↦ notMem_zero _ (h hx)

@[simp] lemma subset_zero : s ⊆ 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩

@[simp] lemma zero_ssubset : 0 ⊂ s ↔ s ≠ 0 := by simp [ssubset_iff_subset_not_subset]

@[simp] lemma singleton_subset : {a} ⊆ s ↔ a ∈ s := by simp [subset_iff]

theorem induction_on' {p : Multiset α → Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T ⊆ S → p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

end Subset

/-! ### Partial order on `Multiset`s -/

section

variable {s t : Multiset α} {a : α}

theorem zero_le (s : Multiset α) : 0 ≤ s :=
  Quot.inductionOn s fun l => (nil_sublist l).subperm

instance : OrderBot (Multiset α) where
  bot := 0
  bot_le := zero_le

/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl

theorem le_zero : s ≤ 0 ↔ s = 0 :=
  le_bot_iff

theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

theorem le_cons_self (s : Multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_lt <| lt_cons_self _ _

@[simp] theorem cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t fun _ _ => subperm_cons a

theorem cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  (cons_le_cons_iff a).2

@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

theorem le_cons_of_notMem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t := by
  refine ⟨?_, fun h => le_trans h <| le_cons_self _ _⟩
  suffices ∀ {t'}, s ≤ t' → a ∈ t' → a ::ₘ s ≤ t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
  exact
    perm_middle.subperm_left.2
      ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)

@[deprecated (since := "2025-05-23")] alias le_cons_of_not_mem := le_cons_of_notMem

theorem cons_le_of_notMem (hs : a ∉ s) : a ::ₘ s ≤ t ↔ a ∈ t ∧ s ≤ t := by
  apply Iff.intro (fun h ↦ ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_notMem hs).mp h₂)

@[deprecated (since := "2025-05-23")] alias cons_le_of_not_mem := cons_le_of_notMem

@[simp]
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) ≠ 0 :=
  ne_of_gt (lt_cons_self _ _)

@[simp]
theorem zero_ne_singleton (a : α) : 0 ≠ ({a} : Multiset α) := singleton_ne_zero _ |>.symm

@[simp]
theorem singleton_le {a : α} {s : Multiset α} : {a} ≤ s ↔ a ∈ s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

@[simp] lemma le_singleton : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
  Quot.induction_on s fun l ↦ by simp only [← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]

@[simp] lemma lt_singleton : s < {a} ↔ s = 0 := by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm

@[simp] lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = 0 := by
  refine ⟨fun hs ↦ eq_zero_of_subset_zero fun b hb ↦ (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp

end

/-! ### Cardinality -/

@[simp]
theorem card_zero : @card α 0 = 0 :=
  rfl

@[simp]
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← cons_zero, card_zero, card_cons]

theorem card_pair (a b : α) : card {a, b} = 2 := by
  rw [insert_eq_cons, card_cons, card_singleton]

theorem card_eq_one {s : Multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
  ⟨Quot.inductionOn s fun _l h => (List.length_eq_one_iff.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩

theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
  ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩

theorem card_pos {s : Multiset α} : 0 < card s ↔ s ≠ 0 :=
  Nat.pos_iff_ne_zero.trans <| not_congr card_eq_zero

theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
  Quot.inductionOn s fun _l => length_pos_iff_exists_mem

theorem card_eq_two {s : Multiset α} : card s = 2 ↔ ∃ x y, s = {x, y} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩

theorem card_eq_three {s : Multiset α} : card s = 3 ↔ ∃ x y z, s = {x, y, z} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩

theorem card_eq_four {s : Multiset α} : card s = 4 ↔ ∃ x y z w, s = {x, y, z, w} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_four.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => Exists.imp fun _d => congr_arg _,
    fun ⟨_a, _b, _c, _d, e⟩ => e.symm ▸ rfl⟩

/-! ### Map for partial functions -/

@[simp]
theorem pmap_zero {p : α → Prop} (f : ∀ a, p a → β) (h : ∀ a ∈ (0 : Multiset α), p a) :
    pmap f 0 h = 0 :=
  rfl

@[simp]
theorem pmap_cons {p : α → Prop} (f : ∀ a, p a → β) (a : α) (m : Multiset α) :
    ∀ h : ∀ b ∈ a ::ₘ m, p b,
      pmap f (a ::ₘ m) h =
        f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a <| mem_cons_of_mem ha :=
  Quotient.inductionOn m fun _l _h => rfl

@[simp]
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl

/-! ### Lift a relation to `Multiset`s -/

section Rel

/-- `Rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`. -/
@[mk_iff]
inductive Rel (r : α → β → Prop) : Multiset α → Multiset β → Prop
  | zero : Rel r 0 0
  | cons {a b as bs} : r a b → Rel r as bs → Rel r (a ::ₘ as) (b ::ₘ bs)

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih

theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩

theorem rel_refl_of_refl_on {m : Multiset α} {r : α → α → Prop} : (∀ x ∈ m, r x x) → Rel r m m := by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))

theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun _x _hx => rfl

theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t := by
  constructor
  · intro h
    induction h <;> simp [*]
  · intro h
    subst h
    exact rel_eq_refl

theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t)
    (h : ∀ a ∈ s, ∀ b ∈ t, r a b → p a b) : Rel p s t := by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by rw [rel_iff]; simp

@[simp]
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by rw [rel_iff]; simp

theorem rel_cons_left {a as bs} :
    Rel r (a ::ₘ as) bs ↔ ∃ b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' := by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨eq₁, eq₂⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · subst eq₁
        subst eq₂
        exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ Rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ Rel.cons hab h

theorem rel_cons_right {as b bs} :
    Rel r as (b ::ₘ bs) ↔ ∃ a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' := by
  rw [← rel_flip, rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip, flip]

theorem card_eq_card_of_rel {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    card s = card t := by induction h <;> simp [*]

theorem exists_mem_of_rel_of_mem {r : α → β → Prop} {s : Multiset α} {t : Multiset β}
    (h : Rel r s t) : ∀ {a : α}, a ∈ s → ∃ b ∈ t, r a b := by
  induction h with
  | zero => simp
  | @cons x y s t hxy _ ih =>
    intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩

theorem rel_of_forall {m1 m2 : Multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 := by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih ?_ ?_, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
    · simpa using hc

protected nonrec
theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
    (r2 : Rel r t u) : Rel r s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (_root_.trans ha1 hb1) (ih ha2 hb2)

end Rel

@[simp]
theorem pairwise_zero (r : α → α → Prop) : Multiset.Pairwise r 0 :=
  ⟨[], rfl, List.Pairwise.nil⟩

section Nodup

variable {s : Multiset α} {a : α}

@[simp]
theorem nodup_zero : @Nodup α 0 :=
  Pairwise.nil

@[simp]
theorem nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_cons

theorem Nodup.cons (m : a ∉ s) (n : Nodup s) : Nodup (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩

theorem Nodup.of_cons (h : Nodup (a ::ₘ s)) : Nodup s :=
  (nodup_cons.1 h).2

theorem Nodup.notMem (h : Nodup (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1

@[deprecated (since := "2025-05-23")] alias Nodup.not_mem := Nodup.notMem

end Nodup

end Multiset
