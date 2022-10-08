import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Subtype
import Std.Tactic.Simpa
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

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    cases h with
    | head => exact ⟨[], l, rfl⟩
    | tail _ h =>
      rcases ih h with ⟨s, t, rfl⟩
      exact ⟨b :: s, t, rfl⟩

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

/--
List.prod satisfies a specification of cartesian product on lists.
-/
theorem product_spec (xs : List α) (ys : List β) (x : α) (y : β) :
  (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  constructor
  · simp only [List.product, and_imp, exists_prop, List.mem_map, Prod.mk.injEq,
      exists_eq_right_right', List.mem_bind]
    exact And.intro
  · simp only [product, mem_bind, mem_map, Prod.mk.injEq, exists_eq_right_right', exists_prop]
    exact id

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], H => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap f l (forall_mem_cons.1 H).2

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l (fun _ => id)

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l with
  | nil => rfl
  | cons => simp only [*, pmap, map]

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [pmap, pmap, h _ (mem_cons_self _ _), ih (fun a ha => h a (mem_cons_of_mem _ ha))]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l with
  | nil => rfl
  | cons => simp only [*, pmap, map]

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l with
  | nil => rfl
  | cons => simp only [*, pmap, map]

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, map_pmap] <;> exact pmap_congr l fun _ _ _ _ => rfl

theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l := by
  rw [attach, map_pmap] <;> exact (pmap_eq_map _ _ _ _).trans (map_id l)

@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_val] <;> exact h)
    rcases this with ⟨⟨_, _⟩, m, rfl⟩
    exact m

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]
  rfl
