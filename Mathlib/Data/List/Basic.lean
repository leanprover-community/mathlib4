import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Simpa
import Std.Data.List.Lemmas
import Lean

open Function

@[simp]
theorem Option.mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]

namespace List

/-!
# Basic properties of Lists
-/

-- instance : is_left_id (List α) has_append.append [] :=
-- ⟨ nil_append ⟩

-- instance : is_right_id (List α) has_append.append [] :=
-- ⟨ append_nil ⟩

-- instance : is_associative (List α) has_append.append :=
-- ⟨ append_assoc ⟩

@[simp] theorem cons_injective {a : α} : injective (cons a) :=
λ _ _ Pe => tail_eq_of_cons_eq Pe

/-! ### mem -/

alias mem_cons ↔ eq_or_mem_of_mem_cons _

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
Or.elim (eq_or_mem_of_mem_cons h₂) (fun e => absurd e h₁) (fun r => r)

theorem ne_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ≠ b :=
fun nin aeqb => absurd (aeqb ▸ Mem.head ..) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ∉ l :=
fun nin nainl => absurd (Mem.tail _ nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → (a ∉ l) → (a ∉ y::l) :=
fun p1 p2 => fun Pain => absurd (eq_or_mem_of_mem_cons Pain) (not_or.mpr ⟨p1, p2⟩)

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : (a ∉ y::l) → a ≠ y ∧ a ∉ l :=
fun p => And.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

theorem mem_map_of_injective {f : α → β} (H : injective f) {a : α} {l : List α} :
  f a ∈ map f l ↔ a ∈ l :=
⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m
          H e ▸ m', mem_map_of_mem _⟩

/-! ### length -/

alias length_pos ↔ ne_nil_of_length_pos length_pos_of_ne_nil

lemma exists_of_length_succ {n} :
  ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
| [], H => absurd H.symm $ Nat.succ_ne_zero n
| h :: t, _ => ⟨h, t, rfl⟩

@[simp]
lemma length_injective_iff : injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨λ x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intros hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    case nil.nil => rfl
    case nil.cons => cases hl
    case cons.nil => cases hl
    case cons.cons ih _ _ => congr
                             · exact Subsingleton.elim _ _
                             · apply ih; simpa using hl

@[simp default+1]
lemma length_injective [Subsingleton α] : injective (length : List α → ℕ) :=
length_injective_iff.mpr inferInstance

/-! ### set-theoretic notation of Lists -/

--lemma singleton_eq (x : α) : ({x} : List α) = [x] := rfl
--lemma insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
--  has_insert.insert x l = x :: l :=
--if_neg h
--lemma insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
--  has_insert.insert x l = l :=
--if_pos h
-- lemma doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] := by
--   rw [insert_neg, singleton_eq]; rwa [singleton_eq, mem_singleton]

/-! ### bounded quantifiers over Lists -/

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x, x ∈ a :: l → p x) :
  ∀ x, x ∈ l → p x :=
(forall_mem_cons.1 h).2

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x := exists_mem_nil _

alias exists_mem_cons ↔ or_exists_of_exists_mem_cons _

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
exists_mem_cons.2 (.inl h)

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α}
    (h : ∃ x ∈ l, p x) : ∃ x ∈ a :: l, p x :=
exists_mem_cons.2 (.inr h)

/-! ### List subset -/

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
fun _ h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

alias subset_nil ↔ eq_nil_of_subset_nil _

-- theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : injective f) :
--   map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
-- begin
--   refine ⟨_, map_subset f⟩, intros h2 x hx,
--   rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩,
--   cases h hxx', exact hx'
-- end

/-! ### append -/

-- theorem append_eq_append_iff {a b c d : List α} :
--   a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
--   induction a generalizing c with
--   | nil =>
--     rw [nil_append]; constructor
--     · rintro rfl; left; exact ⟨_, rfl, rfl⟩
--     · rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩); {rfl}; rw [←append_assoc, ←H]; rfl
--   | cons a as ih =>
--     cases c
--     · simp only [cons_append, nil_append, false_and, exists_false, false_or, exists_eq_left']
--       exact eq_comm
--     · simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left,
--         exists_and_distrib_left]

-- @[simp] theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : List α), split_at n l = (take n l, drop n l)
-- | 0, a => rfl
-- | n+1, [] => rfl
-- | n+1, x :: xs => by simp only [split_at, split_at_eq_take_drop n xs, take, drop]

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  (append_right_inj _).1 h

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  (append_left_inj _).1 h

theorem append_right_injective (s : List α) : injective fun t => s ++ t :=
fun _ _ => append_left_cancel

theorem append_left_injective (t : List α) : injective fun s => s ++ t :=
fun _ _ => append_right_cancel

/-! ### nth element -/

theorem get?_injective {α : Type u} {xs : List α} {i j : ℕ}
  (h₀ : i < xs.length)
  (h₁ : Nodup xs)
  (h₂ : xs.get? i = xs.get? j) : i = j := by
  induction xs generalizing i j with
  | nil => cases h₀
  | cons x xs ih =>
    match i, j with
    | 0, 0 => rfl
    | i+1, j+1 => simp; cases h₁ with
      | cons ha h₁ => exact ih (Nat.lt_of_succ_lt_succ h₀) h₁ h₂
    | i+1, 0 => ?_ | 0, j+1 => ?_
    all_goals
      simp at h₂
      cases h₁; rename_i h' h
      have := h x ?_ rfl; cases this
      rw [mem_iff_get?]
    exact ⟨_, h₂⟩; exact ⟨_ , h₂.symm⟩

@[simp] theorem get?_map (f : α → β) : ∀ l n, (map f l).get? n = (l.get? n).map f
| [], _ => rfl
| _ :: _, 0 => rfl
| _ :: l, n+1 => get?_map f l n

@[simp]
theorem get_map (f : α → β) {l n} : get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) :=
  Option.some.inj $ by
    rw [←get?_eq_get, get?_map, get?_eq_get]; rfl

/-- If one has `get L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `get_of_eq` can be used to make
such a rewrite, with `rw (get_of_eq h)`. -/
theorem get_of_eq {L L' : List α} (h : L = L') (i : Fin  L.length) :
  get L i = get L' ⟨i, h ▸ i.2⟩ := by cases h; rfl

@[simp] theorem get_singleton (a : α) (n : Fin 1) : get [a] n = a := by
  have hn0 : n.1 = 0 := Nat.le_zero_iff.1 (Nat.le_of_lt_succ n.2)
  cases n
  subst hn0; rfl

theorem get_zero {L : List α} (h : 0 < L.length) : L.get ⟨0, h⟩ = L.head? := by
  cases L; {cases h}; simp

theorem get_append : ∀ {l₁ l₂ : List α} (n : ℕ) (h : n < l₁.length),
    (l₁ ++ l₂).get ⟨n, id (length_append .. ▸ Nat.lt_add_right _ _ _ h)⟩ = l₁.get ⟨n, h⟩
| a :: l, _, 0, h => rfl
| a :: l, _, n+1, h => by
  simp only [get, cons_append] <;> exact get_append _ _

theorem get?_append_right : ∀ {l₁ l₂ : List α} {n : ℕ}, l₁.length ≤ n →
  (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length)
| [], _, n, _ => rfl
| a :: l, _, n+1, h₁ => by
  rw [cons_append]; simp
  rw [Nat.add_sub_add_right, get?_append_right (Nat.lt_succ_iff.mp h₁)]

theorem get_append_right_aux {l₁ l₂ : List α} {n : ℕ}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length := by
  rw [length_append] at h₂
  exact Nat.sub_lt_left_of_lt_add h₁ h₂

theorem get_append_right' {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂).get ⟨n, h₂⟩ = l₂.get ⟨n - l₁.length, id <| get_append_right_aux h₁ h₂⟩ :=
Option.some.inj $ by rw [← get?_eq_get, ← get?_eq_get, get?_append_right h₁]

@[simp] theorem get_replicate (a : α) {n : ℕ} (m : Fin _) : (List.replicate n a).get m = a :=
  eq_of_mem_replicate (get_mem _ _ _)

theorem get?_append {l₁ l₂ : List α} {n : ℕ} (hn : n < l₁.length) :
  (l₁ ++ l₂).get? n = l₁.get? n := by
  have hn' : n < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn $ by
    rw [length_append] <;> exact Nat.le_add_right _ _
  rw [get?_eq_get hn, get?_eq_get hn', get_append]

theorem getLast_eq_get : ∀ (l : List α) (h : l ≠ []),
  getLast l h = l.get ⟨l.length - 1, id <| Nat.sub_lt (length_pos_of_ne_nil h) Nat.one_pos⟩
| [a], h => by
  rw [getLast_singleton, get_singleton]
| a :: b :: l, h => by rw [getLast_cons, getLast_eq_get (b :: l)]; {rfl}; exact cons_ne_nil b l

@[simp] theorem get?_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).get? l.length = some a
| [], a => rfl
| b :: l, a => by rw [cons_append, length_cons]; simp only [get?, get?_concat_length]

theorem get_cons_length (x : α) (xs : List α) (n : ℕ) (h : n = xs.length) :
  (x :: xs).get ⟨n, by simp [h]⟩ = (x :: xs).getLast (cons_ne_nil x xs) := by
  rw [getLast_eq_get]; cases h; rfl

@[ext] theorem ext : ∀ {l₁ l₂ : List α}, (∀ n, l₁.get? n = l₂.get? n) → l₁ = l₂
| [], [], _ => rfl
| a :: l₁, [], h => nomatch h 0
| [], a' :: l₂, h => nomatch h 0
| a :: l₁, a' :: l₂, h => by
  have h0 : some a = some a' := h 0
  injection h0 with aa; simp only [aa, ext fun n => h (n+1)]

theorem ext_get {l₁ l₂ : List α} (hl : length l₁ = length l₂)
  (h : ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩) : l₁ = l₂ :=
  ext fun n =>
    if h₁ : n < length l₁ then by
      rw [get?_eq_get, get?_eq_get, h n h₁ (by rwa [←hl])]
    else by
      have h₁ := le_of_not_lt h₁
      rw [get?_len_le h₁, get?_len_le]; rwa [← hl]

theorem modifyNthTail_id : ∀ n (l : List α), l.modifyNthTail id n = l
| 0, _ => rfl
| _+1, [] => rfl
| n+1, a :: l => congr_arg (List.cons a) (modifyNthTail_id n l)

theorem removeNth_eq_nth_tail : ∀ n (l : List α), removeNth l n = modifyNthTail tail n l
| 0, l => by cases l <;> rfl
| n+1, [] => rfl
| n+1, a :: l => congr_arg (cons _) (removeNth_eq_nth_tail _ _)

theorem set_eq_modifyNth (a : α) : ∀ n (l : List α), set l n a = modifyNth (fun _ => a) n l
| 0, l => by cases l <;> rfl
| n+1, [] => rfl
| n+1, b :: l => congr_arg (cons _) (set_eq_modifyNth _ _ _)

theorem modifyNth_eq_set (f : α → α) :
  ∀ n (l : List α), l.modifyNth f n = ((fun a => l.set n (f a)) <$> l.get? n).getD l
| 0, l => by cases l <;> rfl
| n+1, [] => rfl
| n+1, b :: l =>
  (congr_arg (cons b) (modifyNth_eq_set f n l)).trans $ by
    cases l.get? n <;> rfl

theorem get?_modifyNth (f : α → α) :
  ∀ n (l : List α) m, (modifyNth f n l).get? m = (fun a => if n = m then f a else a) <$> l.get? m
| n, l, 0 => by cases l <;> cases n <;> rfl
| n, [], m+1 => by cases n <;> rfl
| 0, _ :: l, m+1 => by cases l.get? m <;> rfl
| n+1, a :: l, m+1 =>
  (get?_modifyNth f n l m).trans $ by
    cases l.get? m <;> by_cases h : n = m <;>
      simp only [h, if_pos, if_true, if_false, Option.map, mt Nat.succ.inj, not_false_iff]

theorem modifyNthTail_length (f : List α → List α) (H : ∀ l, length (f l) = length l) :
  ∀ n l, length (modifyNthTail f n l) = length l
| 0, _ => H _
| _+1, [] => rfl
| _+1, _ :: _ => congr_arg (·+1) (modifyNthTail_length _ H _ _)

@[simp] theorem modify_get?_length (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modifyNthTail_length _ fun l => by cases l <;> rfl

@[simp] theorem get?_modifyNth_eq (f : α → α) (n) (l : List α) :
  (modifyNth f n l).get? n = f <$> l.get? n := by
  simp only [get?_modifyNth, if_pos]

@[simp] theorem get?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
  (modifyNth f m l).get? n = l.get? n := by
  simp only [get?_modifyNth, if_neg h, id_map']

theorem get?_set_eq (a : α) (n) (l : List α) : (set l n a).get? n = (fun _ => a) <$> l.get? n := by
  simp only [set_eq_modifyNth, get?_modifyNth_eq]

theorem get?_set_of_lt (a : α) {n} {l : List α} (h : n < length l) :
  (set l n a).get? n = some a := by rw [get?_set_eq, get?_eq_get h]; rfl

theorem get?_set_ne (a : α) {m n} (l : List α) (h : m ≠ n) : (set l m a).get? n = l.get? n := by
  simp only [set_eq_modifyNth, get?_modifyNth_ne _ _ h]

@[simp] theorem set_nil (n : ℕ) (a : α) : [].set n a = [] := rfl

@[simp] theorem set_succ (x : α) (xs : List α) (n : ℕ) (a : α) :
  (x :: xs).set n.succ a = x :: xs.set n a := rfl

theorem set_comm (a b : α) : ∀ {n m : ℕ} (l : List α), n ≠ m →
  (l.set n a).set m b = (l.set m b).set n a
| _, _, [], _ => by simp
| n+1, 0, _ :: _, _ => by simp [set]
| 0, m+1, _ :: _, _ => by simp [set]
| n+1, m+1, x :: t, h => by
  simp only [set, true_and, eq_self_iff_true]
  conv => lhs; rhs; tactic' =>
    exact set_comm a b t fun h' => h $ Nat.succ_inj'.mpr h'

@[simp] theorem get_set_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).get ⟨i, h⟩ = a := by
  rw [← Option.some_inj, ← get?_eq_get, get?_set_eq, get?_eq_get] <;> simp_all

@[simp] theorem get_set_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
  (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simp at hj; exact hj⟩ := by
  rw [← Option.some_inj, ← List.get?_eq_get, List.get?_set_ne _ _ h, List.get?_eq_get]

theorem mem_or_eq_of_mem_set : ∀ {l : List α} {n : ℕ} {a b : α}, a ∈ l.set n b → a ∈ l ∨ a = b
| _ :: _, 0, _, _, h => ((mem_cons ..).1 h).elim Or.inr (Or.inl ∘ mem_cons_of_mem _)
| _ :: _, _+1, _, _, h =>
  ((mem_cons ..).1 h).elim (fun h => h ▸ Or.inl (mem_cons_self ..))
    fun h => (mem_or_eq_of_mem_set h).elim (Or.inl ∘ mem_cons_of_mem _) Or.inr

/-! ### insert -/
section insert
variable [DecidableEq α]

@[simp] theorem insert_of_mem {a : α} {l : List α} (h : a ∈ l) : l.insert a = l := by
  simp only [List.insert, if_pos h]

@[simp] theorem insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.insert a = a :: l := by
  simp only [List.insert, if_neg h]

@[simp] theorem mem_insert_iff {a b : α} {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
  by_cases h : b ∈ l
  · rw [insert_of_mem h]
    constructor; {apply Or.inr}
    intro
    | Or.inl h' => rw [h']; exact h
    | Or.inr h' => exact h'
  · rw [insert_of_not_mem h, mem_cons]

@[simp 1100] theorem mem_insert_self (a : α) (l : List α) : a ∈ l.insert a :=
mem_insert_iff.2 (Or.inl rfl)

theorem mem_insert_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ l.insert b :=
mem_insert_iff.2 (Or.inr h)

theorem eq_or_mem_of_mem_insert {a b : α} {l : List α} (h : a ∈ l.insert b) : a = b ∨ a ∈ l :=
mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {a : α} {l : List α} (h : a ∈ l) :
  length (l.insert a) = length l := by
  rw [insert_of_mem h]

@[simp] theorem length_insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) :
  length (l.insert a) = length l + 1 := by
  rw [insert_of_not_mem h]; rfl

end insert

/-! ### erasep -/

section erasep

@[simp] theorem erasep_nil : [].erasep p = [] := rfl

theorem erasep_cons (a : α) (l : List α) :
  (a :: l).erasep p = bif p a then l else a :: l.erasep p := rfl

@[simp] theorem erasep_cons_of_pos {a : α} {l : List α} (p) (h : p a) : (a :: l).erasep p = l := by
  simp [erasep_cons, h]

@[simp] theorem erasep_cons_of_neg {a : α} {l : List α} (p) (h : ¬ p a) :
  (a::l).erasep p = a :: l.erasep p := by
  simp [erasep_cons, h]

theorem erasep_of_forall_not {l : List α}
  (h : ∀ a, a ∈ l → ¬ p a) : l.erasep p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (Mem.head ..), ih (forall_mem_of_forall_mem_cons h)]

theorem exists_of_erasep {l : List α} {a} (al : a ∈ l) (pa : p a) :
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
  induction l with
  | nil => cases al
  | cons b l ih =>
    by_cases pb : p b
    · exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
    · cases al with
      | head => cases pb pa
      | tail _ al =>
        let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := ih al
        exact ⟨c, b::l₁, l₂, (forall_mem_cons ..).2 ⟨pb, h₁⟩,
          h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_erasep (p) (l : List α) :
    l.erasep p = l ∨
      ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
  if h : ∃ a ∈ l, p a then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_erasep ha pa)
  else
    .inl (erasep_of_forall_not (h ⟨·, ·, ·⟩))

@[simp] theorem length_erasep_of_mem {l : List α} {a} (al : a ∈ l) (pa : p a) :
   length (l.erasep p) = Nat.pred (length l) := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_erasep al pa
  rw [e₂]; simp [length_append, e₁]; rfl

theorem erasep_append_left {a : α} (pa : p a) :
  ∀ {l₁ : List α} (l₂), a ∈ l₁ → (l₁++l₂).erasep p = l₁.erasep p ++ l₂
| (x::xs), l₂, h => by
  by_cases h' : p x <;> simp [h']
  rw [erasep_append_left pa l₂ (mem_of_ne_of_mem (mt _ h') h)]
  intro | rfl => exact pa

theorem erasep_append_right :
  ∀ {l₁ : List α} (l₂), (∀ b ∈ l₁, ¬ p b) → erasep p (l₁++l₂) = l₁ ++ l₂.erasep p
| [],      l₂, _ => rfl
| (x::xs), l₂, h => by
  simp [((forall_mem_cons ..).1 h).1, erasep_append_right _ ((forall_mem_cons ..).1 h).2]

-- theorem erasep_sublist (l : List α) : l.erasep p <+ l :=
-- by rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩;
--    [rw h, {rw [h₄, h₃], simp}]

theorem erasep_subset (l : List α) : l.erasep p ⊆ l := fun a => by
  match exists_or_eq_self_of_erasep p l with
  | Or.inl h => rw [h]; apply Subset.refl
  | Or.inr ⟨c, l₁, l₂, _, _, h₃, h₄⟩ =>
    rw [h₄, h₃, mem_append, mem_append]
    intro
    | Or.inl h => exact Or.inl h
    | Or.inr h => exact Or.inr $ mem_cons_of_mem _ h
-- the proof was:
-- (erasep_sublist l).subset

-- theorem sublist.erasep {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
-- begin
--   induction s,
--   case List.sublist.slnil { refl },
--   case List.sublist.cons : l₁ l₂ a s IH {
--     by_cases h : p a; simp [h],
--     exacts [IH.trans (erasep_sublist _), IH.cons _ _ _] },
--   case List.sublist.cons2 : l₁ l₂ a s IH {
--     by_cases h : p a; simp [h],
--     exacts [s, IH.cons2 _ _ _] }
-- end

theorem mem_of_mem_erasep {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
  (erasep_subset _ ·)

@[simp] theorem mem_erasep_of_neg {a : α} {l : List α} (pa : ¬ p a) : a ∈ l.erasep p ↔ a ∈ l := by
  refine ⟨mem_of_mem_erasep, fun al => ?_⟩
  apply Or.elim (exists_or_eq_self_of_erasep p l)
  · intro h; rw [h]; assumption
  intro ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩
  rw [h₄]
  rw [h₃] at al
  have : a ≠ c := fun h => by rw [h] at pa; exact pa.elim h₂
  simp [this] at al
  simp [al]

theorem erasep_map (f : β → α) : ∀ (l : List β), (map f l).erasep p = map f (l.erasep (p ∘ f))
  | [] => rfl
  | b::l => by by_cases h : p (f b) <;> simp [h, erasep_map f l, erasep_cons_of_pos]

-- @[simp] theorem extractp_eq_find_erasep :
--   ∀ l : List α, extractp p l = (find p l, erasep p l)
-- | []     => rfl
-- | (a::l) => by by_cases pa : p a; simp [extractp, pa, extractp_eq_find_erasep l]

end erasep

/-! ### erase -/

section erase
variable [DecidableEq α]

@[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

theorem erase_cons (a b : α) (l : List α) :
    (b :: l).erase a = if b = a then l else b :: l.erase a :=
  if h : b = a then by simp [List.erase, h]
  else by simp [List.erase, h, (beq_eq_false_iff_ne _ _).2 h]

@[simp] theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) :
  (b::l).erase a = b :: l.erase a :=
by simp only [erase_cons, if_neg h]

theorem erase_eq_erasep (a : α) (l : List α) : l.erase a = l.erasep (Eq a) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h, ih]

theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [mem_cons, not_or] at h
    rw [erase_cons, if_neg (Ne.symm h.1), ih h.2]

-- TODO: ∉ should have higher priority
theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, (a ∉ l₁) ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
  match exists_of_erasep h (beq_self_eq_true _) with
  | ⟨_, l₁, l₂, h₁, e, h₂, h₃⟩ => by
    rw [erase_eq_erasep]; exact ⟨l₁, l₂, fun h => h₁ _ h (beq_self_eq_true _), eq_of_beq e ▸ h₂, h₃⟩

@[simp] theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) :
  length (l.erase a) = Nat.pred (length l) := by
  rw [erase_eq_erasep]; exact length_erasep_of_mem h (decide_eq_true rfl)

theorem erase_append_left {a : α} {l₁ : List α} (l₂) (h : a ∈ l₁) :
  (l₁++l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_erasep]; exact erasep_append_left (by exact decide_eq_true rfl) l₂ h

theorem erase_append_right {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁++l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right]
  intros b h' h''; rw [of_decide_eq_true h''] at h; exact h h'

-- theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l :=
-- by rw erase_eq_erasep; apply erasep_sublist

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l := by
  rw [erase_eq_erasep]; apply erasep_subset
--(erase_sublist a l).subset

-- theorem sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a :=
-- by simp [erase_eq_erasep]; exact sublist.erasep h

theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
  @erase_subset _ _ _ _ _

@[simp] theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l := by
  rw [erase_eq_erasep]; exact mem_erasep_of_neg (mt of_decide_eq_true ab.symm)

-- theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a :=
-- if ab : a = b then by rw ab else
-- if ha : a ∈ l then
-- if hb : b ∈ l then match l, l.erase a, exists_erase_eq ha, hb with
-- | ._, ._, ⟨l₁, l₂, ha', rfl, rfl⟩, hb :=
--   if h₁ : b ∈ l₁ then
--     by rw [erase_append_left _ h₁, erase_append_left _ h₁,
--            erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
--   else
--     by rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
--            erase_cons_tail _ ab, erase_cons_head]
-- end
-- else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
-- else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]

-- theorem map_erase [DecidableEq β] {f : α → β} (finj : injective f) {a : α}
--   (l : List α) : map f (l.erase a) = (map f l).erase (f a) :=
-- by rw [erase_eq_erasep, erase_eq_erasep, erasep_map]; congr;
--    ext b; simp [finj.eq_iff]

-- theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : injective f) {l₁ l₂ : List α} :
--   map f (foldl List.erase l₁ l₂) = foldl (fun  l a, l.erase (f a)) (map f l₁) l₂ :=
-- by induction l₂ generalizing l₁; [refl,
-- simp only [foldl_cons, map_erase finj, *]]

-- @[simp] theorem count_erase_self (a : α) :
--   ∀ (s : List α), count a (List.erase s a) = pred (count a s)
-- | [] => by simp
-- | (h :: t) :=
-- begin
--   rw erase_cons,
--   by_cases p : h = a,
--   { rw [if_pos p, count_cons', if_pos p.symm], simp },
--   { rw [if_neg p, count_cons', count_cons', if_neg (fun  x : a = h, p x.symm), count_erase_self],
--     simp, }
-- end

-- @[simp] theorem count_erase_of_ne {a b : α} (ab : a ≠ b) :
--   ∀ (s : List α), count a (List.erase s b) = count a s
-- | [] := by simp
-- | (x :: xs) :=
-- begin
--   rw erase_cons,
--   split_ifs with h,
--   { rw [count_cons', h, if_neg ab], simp },
--   { rw [count_cons', count_cons', count_erase_of_ne] }
-- end

end erase

-- /-! ### disjoint -/

section disjoint

variable {α : Type _} {l l₁ l₂ : List α} {p : α → Prop} {a : α}

lemma disjoint_symm (d : disjoint l₁ l₂) : disjoint l₂ l₁ := λ _ i₂ i₁ => d i₁ i₂

lemma disjoint_comm : disjoint l₁ l₂ ↔ disjoint l₂ l₁ := ⟨disjoint_symm, disjoint_symm⟩

lemma disjoint_left : disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₁ → a ∉ l₂ := by simp [disjoint]

lemma disjoint_right : disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₂ → a ∉ l₁ := disjoint_comm

lemma disjoint_iff_ne : disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
  ⟨fun h _ al1 _ bl2 ab => h al1 (ab ▸ bl2), fun h _ al1 al2 => h _ al1 _ al2 rfl⟩

lemma disjoint_of_subset_left (ss : l₁ ⊆ l) (d : disjoint l l₂) : disjoint l₁ l₂ :=
λ _ m => d (ss m)

lemma disjoint_of_subset_right (ss : l₂ ⊆ l) (d : disjoint l₁ l) : disjoint l₁ l₂ :=
λ _ m m₁ => d m (ss m₁)

lemma disjoint_of_disjoint_cons_left {l₁ l₂} : disjoint (a :: l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (List.subset_cons _ _)

lemma disjoint_of_disjoint_cons_right {l₁ l₂} : disjoint l₁ (a :: l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (List.subset_cons _ _)

@[simp] lemma disjoint_nil_left (l : List α) : disjoint [] l := λ a => (not_mem_nil a).elim

@[simp] lemma disjoint_nil_right (l : List α) : disjoint l [] := by
  rw [disjoint_comm]; exact disjoint_nil_left _

-- TODO: this lemma is marked with simp and priority 1100 in mathlib3
lemma singleton_disjoint : disjoint [a] l ↔ a ∉ l := by
simp [disjoint]

-- TODO: this lemma is marked with priority 1100 in mathlib3
@[simp] lemma disjoint_singleton : disjoint l [a] ↔ a ∉ l := by
rw [disjoint_comm, singleton_disjoint]

@[simp] lemma disjoint_append_left : disjoint (l₁ ++ l₂) l ↔ disjoint l₁ l ∧ disjoint l₂ l :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

-- @[simp] lemma disjoint_append_right : disjoint l (l₁ ++ l₂) ↔ disjoint l l₁ ∧ disjoint l l₂ :=
-- disjoint_comm.trans $ by simp [disjoint_comm, disjoint_append_left]

@[simp] lemma disjoint_cons_left : disjoint (a::l₁) l₂ ↔ (a ∉ l₂) ∧ disjoint l₁ l₂ :=
(@disjoint_append_left _ l₂ [a] l₁).trans $ by simp [singleton_disjoint]

-- @[simp] lemma disjoint_cons_right : disjoint l₁ (a :: l₂) ↔ (a ∉ l₁) ∧ disjoint l₁ l₂ :=
-- disjoint_comm.trans $ by simp [disjoint_comm, disjoint_cons_left]

lemma disjoint_of_disjoint_append_left_left (d : disjoint (l₁ ++ l₂) l) : disjoint l₁ l :=
(disjoint_append_left.1 d).1

lemma disjoint_of_disjoint_append_left_right (d : disjoint (l₁ ++ l₂) l) : disjoint l₂ l :=
(disjoint_append_left.1 d).2

-- lemma disjoint_of_disjoint_append_right_left (d : disjoint l (l₁ ++ l₂)) : disjoint l l₁ :=
-- (disjoint_append_right.1 d).1

-- lemma disjoint_of_disjoint_append_right_right (d : disjoint l (l₁ ++ l₂)) : disjoint l l₂ :=
-- (disjoint_append_right.1 d).2

-- lemma disjoint_take_drop {m n : ℕ} (hl : l.nodup) (h : m ≤ n) : disjoint (l.take m) (l.drop n) :=
-- begin
--   induction l generalizing m n,
--   case list.nil : m n
--   { simp },
--   case list.cons : x xs xs_ih m n
--   { cases m; cases n; simp only [disjoint_cons_left, mem_cons_iff, disjoint_cons_right, drop,
--                                  true_or, eq_self_iff_true, not_true, false_and,
--                                  disjoint_nil_left, take],
--     { cases h },
--     cases hl with _ _ h₀ h₁, split,
--     { intro h, exact h₀ _ (mem_of_mem_drop h) rfl, },
--     solve_by_elim [le_of_succ_le_succ] { max_depth := 4 } },
-- end

end disjoint

-- /-! ### union -/

section union

variable [DecidableEq α]

@[simp] theorem nil_union (l : List α) : nil.union l = l := by simp [List.union, foldr]

@[simp] theorem cons_union (a : α) (l₁ l₂ : List α) :
  (a :: l₁).union l₂ = (l₁.union l₂).insert a := by simp [List.union, foldr]

@[simp] theorem mem_union_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁.union l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l' ih => simp [ih, or_assoc]

end union

-- /-! ### inter -/

@[simp] theorem mem_inter_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁.inter l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  cases l₁ <;> simp [List.inter, mem_filter]

/--
List.prod satisfies a specification of cartesian product on lists.
-/
theorem product_spec (xs : List α) (ys : List β) (x : α) (y : β) :
  (x, y) ∈ product xs ys <-> (x ∈ xs ∧ y ∈ ys) := by
  constructor
  · simp only [List.product, and_imp, exists_prop, List.mem_map, Prod.mk.injEq,
      exists_eq_right_right', List.mem_bind]
    exact And.intro
  · simp only [product, mem_bind, mem_map, Prod.mk.injEq, exists_eq_right_right', exists_prop]
    exact id

section Pairwise

variable {R : α → α → Prop}

@[simp]
theorem Pairwise_cons {a : α} {l : List α} :
  Pairwise R (a::l) ↔ (∀ a', a' ∈ l -> R a a') ∧ Pairwise R l :=
  ⟨fun | Pairwise.cons h1 h2 => ⟨h1, h2⟩, And.elim Pairwise.cons⟩

instance decidablePairwise [DecidableRel R] (l : List α) : Decidable (Pairwise R l) :=
  match l with
  | [] => isTrue Pairwise.nil
  | hd :: tl =>
    match decidablePairwise tl with
    | isTrue ht =>
      match decidableBAll (R hd) tl with
      | isFalse hf => isFalse fun hf' =>
        have hAnd : (∀ a', a' ∈ tl -> R hd a') ∧ Pairwise R tl := Pairwise_cons.mp hf'
        hf hAnd.left
      | isTrue ht' =>  isTrue $ Pairwise_cons.mpr (And.intro ht' ht)
    | isFalse hf => isFalse fun
      | Pairwise.cons _ ih => hf ih

end Pairwise

instance nodupDecidable [DecidableEq α] : ∀ l : List α, Decidable (Nodup l) :=
List.decidablePairwise

/-- pad `l : List α` with repeated occurrences of `a : α` until it's of length `n`.
  If `l` is initially larger than `n`, just return `l`. -/
def leftpad (n : ℕ) (a : α) (l : List α) : List α := replicate (n - length l) a ++ l

/-- The length of the List returned by `List.leftpad n a l` is equal
  to the larger of `n` and `l.length` -/
theorem leftpad_length (n : ℕ) (a : α) (l : List α) : (leftpad n a l).length = max n l.length :=
by simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]

theorem leftpad_prefix (n : ℕ) (a : α) (l : List α) : isPrefix (replicate (n - length l) a) (leftpad n a l) :=
by
  simp only [isPrefix, leftpad]
  exact Exists.intro l rfl

theorem leftpad_suffix (n : ℕ) (a : α) (l : List α) : isSuffix l (leftpad n a l) :=
by
  simp only [isSuffix, leftpad]
  exact Exists.intro (replicate (n - length l) a) rfl

end List
