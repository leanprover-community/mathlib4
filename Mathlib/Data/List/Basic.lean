import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.SetNotation
import Lean
namespace List

/-- The same as append, but with simpler defeq. (The one in the standard library is more efficient,
because it is implemented in a tail recursive way.) -/
@[simp] def append' : List α → List α → List α
| [], r => r
| a::l, r => a :: append' l r

theorem append'_eq_append : (l r : List α) → append' l r = l ++ r
| [], r => rfl
| a::l, r => by simp only [append', cons_append, append'_eq_append]; rfl

/-- The same as length, but with simpler defeq. (The one in the standard library is more efficient,
because it is implemented in a tail recursive way.) -/
@[simp] def length' : List α → ℕ
| [] => 0
| a::l => l.length'.succ

theorem length'_eq_length : (l : List α) → length' l = l.length
| [] => rfl
| a::l => by simp only [length', length_cons, length'_eq_length]; rfl

theorem concat_eq_append' : ∀ (l : List α) a, concat l a = l.append' [a]
| [], a => (append_nil _).symm
| x::xs, a => by simp only [concat, append', concat_eq_append' xs]; rfl

theorem concat_eq_append (l : List α) (a) : concat l a = l ++ [a] :=
(concat_eq_append' _ _).trans (append'_eq_append _ _)

theorem get_cons_drop : ∀ (l : List α) i h,
  List.get l i h :: List.drop (i + 1) l = List.drop i l
| _::_, 0, h => rfl
| _::_, i+1, h => get_cons_drop _ i _

theorem drop_eq_nil_of_le' : ∀ {l : List α} {k : Nat} (h : l.length' ≤ k), l.drop k = []
| [], k, _ => by cases k <;> rfl
| a::l, 0, h => by cases h
| a::l, k+1, h => by have h0 : length' (a :: l) = length' l + 1 := rfl
                     have h1 : length' l ≤ k := by rw [h0] at h
                                                   exact Nat.le_of_succ_le_succ h
                     exact drop_eq_nil_of_le' (l := l) h1

theorem drop_eq_nil_of_le {l : List α} {k : Nat} : (h : l.length ≤ k) → l.drop k = [] :=
by rw [← length'_eq_length]; exact drop_eq_nil_of_le'

@[simp] theorem map_nil {f : α → β} : map f [] = [] := rfl
@[simp] theorem map_cons {f : α → β} : map f (b :: l) = f b :: l.map f := rfl

@[simp] theorem join_nil : join ([] : List (List α)) = [] := rfl

@[simp] theorem join_cons : join (a :: l : List (List α)) = a ++ join l := rfl

/-!
# Basic properties of Lists
-/

-- instance : is_left_id (List α) has_append.append [] :=
-- ⟨ nil_append ⟩

-- instance : is_right_id (List α) has_append.append [] :=
-- ⟨ append_nil ⟩

-- instance : is_associative (List α) has_append.append :=
-- ⟨ append_assoc ⟩

theorem cons_ne_nil (a : α) (l : List α) : a::l ≠ [] := by intro h; cases h

theorem cons_ne_self (a : α) (l : List α) : a::l ≠ l :=
  mt (congr_arg length') (Nat.succ_ne_self _)

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
fun Peq => List.noConfusion Peq fun Pheq Pteq => Pheq

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
fun Peq => List.noConfusion Peq (fun Pheq Pteq => Pteq)

-- @[simp] theorem cons_injective {a : α} : injective (cons a) :=
-- assume l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

-- theorem cons_inj (a : α) {l l' : List α} : a::l = a::l' ↔ l = l' :=
-- cons_injective.eq_iff

theorem exists_cons_of_ne_nil {l : List α} (h : l ≠ nil) : ∃ b L, l = b :: L := by
  induction l with
    | nil          => contradiction
    | cons c l' ih => exact ⟨c, l', rfl⟩

/-! ### bind -/

@[simp] lemma nil_bind (f : α → List β) : List.bind [] f = [] :=
by simp [join, List.bind]

@[simp] lemma cons_bind (x xs) (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f :=
by simp [join, List.bind]

@[simp] lemma append_bind (xs ys) (f : α → List β) :
  List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp [ih, cons_bind, List.append_assoc]

/-! ### map -/

@[simp] lemma map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = (map f l₁) ++ (map f l₂) := by
  intros l₁ l₂
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [cons_append, ih]

lemma map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
rfl

@[simp] lemma map_id (l : List α) : map id l = l := by
  induction l with
  | nil => simp
  | cons a l' ih => simp [ih]

@[simp] lemma map_map (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by
  induction l with
  | nil => simp
  | cons a l' ih => simp [ih]

@[simp] lemma length_map (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l with
  | nil => simp
  | cons a l' ih => simp [ih]

/-! ### mem -/

def mem (a : α) : List α → Prop
| [] => False
| (b :: l) => a = b ∨ mem a l

instance : Mem α (List α) := ⟨mem⟩

@[simp] lemma mem_nil (a : α) : a ∈ [] ↔ False := Iff.rfl

@[simp] lemma mem_cons {a b : α} {l : List α} :
  a ∈ (b :: l) ↔ a = b ∨ a ∈ l := Iff.rfl

lemma mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False :=
Iff.rfl

@[simp] lemma not_mem_nil (a : α) : a ∉ ([] : List α) :=
not_false

lemma mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
Or.inl rfl

@[simp] lemma mem_cons_iff (a y : α) (l : List α) : a ∈ y :: l ↔ (a = y ∨ a ∈ l) :=
Iff.rfl

lemma mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
rfl

lemma mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l :=
fun H => Or.inr H

lemma eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y::l → a = y ∨ a ∈ l :=
fun h => h

@[simp] lemma mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s with
  | nil => simp
  | cons a s' ih => simp [or_assoc, ih]

lemma mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
propext mem_append

lemma mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
mem_append.2 (Or.inl h)

lemma mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
mem_append.2 (Or.inr h)

lemma not_bex_nil (p : α → Prop) : ¬ (∃ x ∈ @nil α, p x) :=
fun ⟨x, hx, px⟩ => hx

lemma ball_nil (p : α → Prop) : ∀ x, x ∈ @nil α → p x :=
fun x => False.elim

lemma bex_cons (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ (a :: l), p x) ↔ (p a ∨ ∃ x ∈ l, p x) := by
  split; focus
    intro ⟨x, h, px⟩
    simp at h
    cases h with
      | inl h => { rw [h] at px; exact Or.inl px }
      | inr h => { exact Or.inr ⟨x, h, px⟩ }
  intro h
  apply Or.elim h
  { exact fun pa => ⟨a, mem_cons_self a l, pa⟩ }
  exact fun ⟨x, xmem, px⟩ => ⟨x, mem_cons_of_mem _ xmem, px⟩

lemma ball_cons (p : α → Prop) (a : α) (l : List α) :
    (∀ x ∈ (a :: l), p x) ↔ (p a ∧ ∀ x ∈ l, p x) :=
Iff.intro
 (fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩)
 (fun ⟨pa, al⟩ x o => o.elim (fun e => by rw [e]; exact pa) (al x))

instance decidableMem [DecidableEq α] (a : α) : ∀ (l : List α), Decidable (a ∈ l)
  | []     => isFalse not_false
  | b :: l =>
    if h₁ : a = b then isTrue (Or.inl h₁)
    else match decidableMem a l with
      | isTrue h₂  => isTrue (Or.inr h₂)
      | isFalse h₂ => isFalse (not_or_intro h₁ h₂)

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
fun this : a ∈ [b] => Or.elim
  (eq_or_mem_of_mem_cons this)
  (fun this : a = b => this)
  (fun this : a ∈ [] => absurd this (not_mem_nil a))

@[simp] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
⟨eq_of_mem_singleton, Or.inl⟩

theorem mem_of_mem_cons_of_mem {a b : α} {l : List α} : a ∈ b::l → b ∈ l → a ∈ l :=
fun ainbl binl => Or.elim
  (eq_or_mem_of_mem_cons ainbl)
  (fun this : a = b => by subst a; exact binl)
  (fun this : a ∈ l => this)

theorem _root_.decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
  {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
Decidable.byCases Or.inl fun this : a ≠ b => h.elim Or.inl $ fun h => Or.inr ⟨this, h⟩

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} : a ∈ b :: l → a = b ∨ (a ≠ b ∧ a ∈ l) := by
  byCases h : a = b
  { exact fun _ => Or.inl h }
  exact fun h' => Or.inr ⟨h, Or.resolve_left h' h⟩

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ (not_or _ _).mpr ⟨h₁, h₂⟩

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by intro e; rw [e] at h; cases h

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
  induction l with
  | nil => cases h --exact ⟨[], l, rfl⟩
  | cons b l ih =>
      cases h with
      | inl heq => rw [heq]; exact ⟨[], l, rfl⟩
      | inr hmem =>
        match ih hmem with
        | ⟨s, t, h'⟩ =>
          refine ⟨b::s, t, ?_⟩
          rw [h', cons_append]

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
Or.elim (eq_or_mem_of_mem_cons h₂) (fun e => absurd e h₁) (fun r => r)

theorem ne_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ≠ b :=
fun nin aeqb => absurd (Or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ∉ l :=
fun nin nainl => absurd (Or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → (a ∉ l) → (a ∉ y::l) :=
fun p1 p2 => fun Pain => absurd (eq_or_mem_of_mem_cons Pain) ((not_or _ _).mpr ⟨p1, p2⟩)

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : (a ∉ y::l) → a ≠ y ∧ a ∉ l :=
fun p => And.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

theorem mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l := by
  induction l with
  | nil => cases h
  | cons b l' ih =>
      cases h with
      | inl h' => rw [h']; exact Or.inl rfl
      | inr h' => exact Or.inr $ ih h'

theorem exists_of_mem_map {f : α → β} {b : β} {l : List α} (h : b ∈ List.map f l) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => cases h
  | cons c l' ih =>
      cases eq_or_mem_of_mem_cons h with
      | inl h => exact ⟨c, mem_cons_self _ _, h.symm⟩
      | inr h =>
        match ih h with
        | ⟨a, ha₁, ha₂⟩ => exact ⟨a, mem_cons_of_mem _ ha₁, ha₂⟩

theorem mem_map {f : α → β} {b} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ b = f a
| [] => by simp
| b :: l => by
  rw [map_cons, mem_cons, mem_map];
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

-- theorem mem_map_of_injective {f : α → β} (H : injective f) {a : α} {l : List α} :
--   f a ∈ map f l ↔ a ∈ l :=
-- ⟨fun m => let ⟨a', m', e⟩ := exists_of_mem_map m
--           H e ▸ m', mem_map_of_mem _⟩

lemma forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
  (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) := by
  split
  { intros H j hj; exact H (f j) (mem_map_of_mem f hj) }
    intros H i hi
    match mem_map.1 hi with
    | ⟨j, hj, ji⟩ => rw [ji]; exact H j hj

@[simp] lemma map_eq_nil {f : α → β} {l : List α} : List.map f l = [] ↔ l = [] := by
  split
    cases l with
    | nil => intro _; rfl
    | cons b l => intro h; exact List.noConfusion h
  intro h; rw [h]; rfl

theorem mem_join {a} : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
| [] => by simp
| b :: l => by
  simp only [join, mem_append, mem_join]
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

theorem exists_of_mem_join {a : α} {L : List (List α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
mem_join.1

theorem mem_join_of_mem {a : α} {L : List (List α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
mem_join.2 ⟨l, lL, al⟩

theorem mem_bind {f : α → List β} {b} {l : List α} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_map, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
  b ∈ List.bind l f :=
mem_bind.2 ⟨a, al, h⟩

lemma bind_map {g : α → List β} {f : β → γ} :
  ∀(l : List α), List.map f (l.bind g) = l.bind (fun a => (g a).map f)
| [] => rfl
| a::l => by simp only [cons_bind, map_append, bind_map l]; rfl

/-! ### length -/

@[simp] lemma length_append (s t : List α) : length (s ++ t) = length s + length t := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih, Nat.add_comm, Nat.add_left_comm, Nat.succ_add]

-- @[simp] lemma length_repeat (a : α) (n : ℕ) : length (repeat a n) = n :=
-- by induction n; simp [*]; refl

-- @[simp] lemma length_tail (l : list α) : length (tail l) = length l - 1 :=
-- by cases l; refl

-- -- TODO(Leo): cleanup proof after arith dec proc
-- @[simp] lemma length_drop : ∀ (i : ℕ) (l : list α), length (drop i l) = length l - i
-- | 0 l         := rfl
-- | (succ i) [] := eq.symm (nat.zero_sub (succ i))
-- | (succ i) (x::l) := calc
--   length (drop (succ i) (x::l))
--           = length l - i             : length_drop i l
--       ... = succ (length l) - succ i : (nat.succ_sub_succ_eq_sub (length l) i).symm

theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] := by
  induction l with
  | nil => intros; rfl
  | cons a l ih => intro h; simp at h

theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = Nat.succ n → l ≠ [] := by
  induction l with
  | nil => intros; contradiction
  | cons a l ih => intros _ _ h; exact List.noConfusion h

-- -- TODO: here we need min_zero
-- @[simp] theorem length_map₂ (f : α → β → γ) (l₁) :
--     ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
--   induction l₁ with
--   | nil =>
--       intro l₂
--       simp
--       rw [min_zero]
--   | cons a l ih => _

-- -- by { induction l₁; intro l₂; cases l₂; simp [*, add_one, min_succ_succ, Nat.zero_min, Nat.min_zero] }

-- @[simp] theorem length_take : ∀ (i : ℕ) (l : List α), length (take i l) = min i (length l)
-- | 0        l      := by simp [Nat.zero_min]
-- | (succ n) []     := by simp [Nat.min_zero]
-- | (succ n) (a::l) := by simp [*, Nat.min_succ_succ, add_one]

-- theorem length_take_le (n) (l : List α) : length (take n l) ≤ n :=
-- by simp [min_le_left]

-- theorem length_remove_nth : ∀ (l : List α) (i : ℕ), i < length l → length (remove_nth l i) = length l - 1
-- | []      _     h := rfl
-- | (x::xs) 0     h := by simp [remove_nth]
-- | (x::xs) (i+1) h := have i < length xs, from lt_of_succ_lt_succ h,
--   by dsimp [remove_nth]; rw [length_remove_nth xs i this, Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) this)]; refl

theorem length_eq_zero {l : List α} : length l = 0 ↔ l = [] :=
⟨eq_nil_of_length_eq_zero, fun h => by rw [h]; rfl⟩

@[simp] lemma length_singleton (a : α) : length [a] = 1 := rfl

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
| nil,  h => by cases h
| b::l, _ => by rw [length_cons]; exact Nat.zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
| nil,    h => by cases h
| b::l, _   => ⟨b, mem_cons_self _ _⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
⟨exists_mem_of_length_pos, fun  ⟨a, h⟩ => length_pos_of_mem h⟩

theorem ne_nil_of_length_pos {l : List α} : 0 < length l → l ≠ [] :=
fun h1 h2 => Nat.lt_irrefl 0 ((length_eq_zero.2 h2).subst h1)

theorem length_pos_of_ne_nil {l : List α} : l ≠ [] → 0 < length l :=
fun h => Nat.pos_iff_ne_zero.2 $ fun h0 => h $ length_eq_zero.1 h0

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

lemma exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
exists_mem_of_length_pos (length_pos_of_ne_nil h)

theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] := by
  split
    intro h
    match l with
    | nil => contradiction
    | [a] => exact ⟨_, rfl⟩
    | a::b::l => simp at h; contradiction
  exact fun ⟨a, leq⟩ => by rw [leq]; simp

lemma exists_of_length_succ {n} :
  ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
| [], H => absurd H.symm $ Nat.succ_ne_zero n
| (h :: t), H => ⟨h, t, rfl⟩

-- @[simp] lemma length_injective_iff : injective (List.length : List α → ℕ) ↔ subsingleton α :=
-- begin
--   split,
--   { intro h, refine ⟨fun  x y, _⟩, suffices : [x] = [y], { simpa using this }, apply h, refl },
--   { intros hα l1 l2 hl, induction l1 generalizing l2; cases l2,
--     { refl }, { cases hl }, { cases hl },
--     congr, exactI subsingleton.elim _ _, apply l1_ih, simpa using hl }
-- end

-- @[simp] lemma length_injective [subsingleton α] : injective (length : List α → ℕ) :=
-- length_injective_iff.mpr $ by apply_instance

/-! ### set-theoretic notation of Lists -/

lemma empty_eq : (∅ : List α) = [] := by rfl
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

theorem forall_mem_nil (p : α → Prop) : ∀ x∈ @nil α, p x := fun x h => by cases h

theorem forall_mem_cons : ∀ {p : α → Prop} {a : α} {l : List α},
  (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
ball_cons _ _ _

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x, x ∈ a :: l → p x) :
  ∀ x, x ∈ l → p x :=
(forall_mem_cons.1 h).2

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]; rfl

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
  (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp only [mem_append, or_imp_distrib, forall_and_distrib]; rfl

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x
  | ⟨_, ⟨h, _⟩⟩ => by cases h

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
⟨a, (mem_cons_self _ _), h⟩

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} :
    (∃ x ∈ l, p x) → ∃ x ∈ a :: l, p x
| ⟨x, h, px⟩ => ⟨x, Or.inr h, px⟩

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∃ x ∈ a :: l, p x) → p a ∨ ∃ x ∈ l, p x
| ⟨x, xal, px⟩ => by
  cases xal with
  | inl h => rw [←h]; exact Or.inl px
  | inr h => exact Or.inr ⟨x, h, px⟩

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
Iff.intro or_exists_of_exists_mem_cons
  (fun h => Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists)

/-! ### List subset -/

protected def subset (l₁ l₂ : List α) := ∀ {a : α}, a ∈ l₁ → a ∈ l₂

instance : Subset (List α) := ⟨List.subset⟩

@[simp] lemma nil_subset (l : List α) : [] ⊆ l :=
λ {b} i => False.elim (Iff.mp (mem_nil_iff b) i)

@[simp] lemma subset.refl (l : List α) : l ⊆ l :=
λ {b} i => i

lemma subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ {b} i => h₂ (h₁ i)

@[simp] lemma subset_cons (a : α) (l : List α) : l ⊆ a::l :=
λ {b} i => Or.inr i

lemma subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s {b} i => s (mem_cons_of_mem _ i)

lemma cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ {b} hin => Or.elim
  (eq_or_mem_of_mem_cons hin)
  (λ e : b = a => Or.inl e)
  (λ i : b ∈ l₁ => Or.inr (s i))

@[simp] lemma subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁++l₂ :=
λ {b} => mem_append_left _

@[simp] lemma subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁++l₂ :=
λ {b} => mem_append_right _

lemma subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁) => Or.inr (s i)

theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := Iff.rfl

theorem subset_append_of_subset_left (l l₁ l₂ : List α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
fun s => subset.trans s $ subset_append_left _ _

theorem subset_append_of_subset_right (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
fun s => subset.trans s $ subset_append_right _ _

@[simp] theorem cons_subset {a : α} {l m : List α} :
    a::l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  simp only [subset_def, mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq]; rfl

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
fun {a} h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

@[simp] theorem append_subset_iff {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  split
  { intro h; simp only [subset_def] at *
    split
      intros; apply h; apply mem_append_left; assumption
      intros; apply h; apply mem_append_right; assumption }
  { intro h; match h with | ⟨h1, h2⟩ => apply append_subset_of_subset_of_subset h1 h2 }

theorem eq_nil_of_subset_nil : ∀ {l : List α}, l ⊆ [] → l = []
| [],     s => rfl
| (a::l), s => False.elim $ s $ mem_cons_self a l

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l :=
show l = [] ↔ l ⊆ []
from ⟨fun e => e ▸ subset.refl _, eq_nil_of_subset_nil⟩

theorem map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
fun {x} => by simp only [mem_map, not_and, exists_imp_distrib, and_imp]
              exact fun a h e => ⟨a, H h, e⟩

-- theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : injective f) :
--   map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
-- begin
--   refine ⟨_, map_subset f⟩, intros h2 x hx,
--   rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩,
--   cases h hxx', exact hx'
-- end

@[simp] theorem mem_reverseAux (x : α) : ∀ as bs, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], bs => by simp [reverseAux]
  | a :: as, bs => by simp [reverseAux, mem_reverseAux]; rw [←or_assoc, @or_comm (x = a)]

@[simp] theorem mem_reverse (x : α) (as : List α) : x ∈ reverse as ↔ x ∈ as := by simp [reverse]

-- TODO: better automation needed
theorem mem_filterAux (x : α) (p : α → Bool) :
    ∀ as bs, x ∈ filterAux p as bs ↔ (x ∈ as ∧ p x) ∨ x ∈ bs
  | [], bs => by simp [filterAux]
  | (a :: as), bs => by
      simp [filterAux]
      cases pa : p a with
      | true =>
        simp [mem_filterAux x p as (a :: bs)]
        split; focus
          intro h'
          cases h' with
          | inl h'' => exact Or.inl ⟨Or.inr h''.1, h''.2⟩
          | inr h'' =>
            cases h'' with
            | inl h₃ => exact Or.inl ⟨Or.inl h₃, h₃ ▸ pa⟩
            | inr h₃ => exact Or.inr h₃
        intro h'
        cases h' with
        | inl h'' =>
          cases h''.1 with
          | inl h₃ => exact Or.inr (Or.inl h₃)
          | inr h₃ => exact Or.inl ⟨h₃, h''.2⟩
        | inr h'' => exact Or.inr (Or.inr h'')
      | false =>
        simp [mem_filterAux x p as bs]
        split; focus
          intro h'
          cases h' with
          | inl h'' => exact Or.inl ⟨Or.inr h''.1, h''.2⟩
          | inr h'' => exact Or.inr h''
        intro h'
        cases h' with
        | inl h'' =>
          cases h''.1 with
          | inl h₃ => rw [←h₃, h''.2] at pa; contradiction
          | inr h₃ => exact Or.inl ⟨h₃, h''.2⟩
        | inr h'' => exact Or.inr h''

theorem mem_filter (as : List α) (p : α → Bool) (x : α) :
    x ∈ filter p as ↔ x ∈ as ∧ p x = true := by simp [filter, mem_filterAux]

/-! ### append -/

lemma append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ := rfl

@[simp] lemma singleton_append {x : α} {l : List α} : [x] ++ l = x :: l := rfl

theorem append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by
  induction s with
  | nil => intros; contradiction
  | cons a s ih => rw [cons_append]; intros _ h; contradiction

theorem append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by
  induction s with
  | nil => intros; rw [nil_append]; assumption
  | cons a s ih => rw [cons_append]; intros _ h; contradiction

@[simp] lemma append_eq_nil {p q : List α} : (p ++ q) = [] ↔ p = [] ∧ q = [] := by
  cases p with
  | nil => simp
  | cons a p => simp

@[simp] lemma nil_eq_append_iff {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] :=
by rw [eq_comm, append_eq_nil]

-- lemma append_eq_cons_iff {a b c : List α} {x : α} :
--   a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
--   cases a with
--   | nil => simp
--   | cons a as =>
--       simp
--       split
--         intro h
--         exact ⟨as, by simp [h]⟩
--       focus
--         intro ⟨a', ⟨aeq, aseq⟩, h⟩
--         split; apply aeq
--         rw [aseq, h]

-- lemma cons_eq_append_iff {a b c : List α} {x : α} :
--     (x :: c : List α) = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
--   rw [eq_comm, append_eq_cons_iff]

-- lemma append_eq_append_iff {a b c d : List α} :
--   a ++ b = c ++ d ↔ (∃a', c = a ++ a' ∧ b = a' ++ d) ∨ (∃c', a = c ++ c' ∧ d = c' ++ b) :=
-- begin
--   induction a generalizing c,
--   case nil { rw nil_append, split,
--     { rintro rfl, left, exact ⟨_, rfl, rfl⟩ },
--     { rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩), {refl}, {rw [← append_assoc, ← H], refl} } },
--   case cons : a as ih {
--     cases c,
--     { simp only [cons_append, nil_append, false_and, exists_false, false_or, exists_eq_left'],
--       exact eq_comm },
--     { simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left,
--         exists_and_distrib_left] } }
-- end

-- @[simp] theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : List α), split_at n l = (take n l, drop n l)
-- | 0        a         := rfl
-- | (succ n) []        := rfl
-- | (succ n) (x :: xs) := by simp only [split_at, split_at_eq_take_drop n xs, take, drop]

-- @[simp] theorem take_append_drop : ∀ (n : ℕ) (l : List α), take n l ++ drop n l = l
-- | 0        a         := rfl
-- | (succ n) []        := rfl
-- | (succ n) (x :: xs) := congr_arg (cons x) $ take_append_drop n xs

-- -- TODO(Leo): cleanup proof after arith dec proc
-- theorem append_inj :
--   ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
-- | []      []      t₁ t₂ h hl := ⟨rfl, h⟩
-- | (a::s₁) []      t₁ t₂ h hl := List.noConfusion $ eq_nil_of_length_eq_zero hl
-- | []      (b::s₂) t₁ t₂ h hl := List.noConfusion $ eq_nil_of_length_eq_zero hl.symm
-- | (a::s₁) (b::s₂) t₁ t₂ h hl := List.noConfusion h $ fun ab hap,
--   let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl) in
--   by rw [ab, e1, e2]; exact ⟨rfl, rfl⟩

-- theorem append_inj_right {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
--   (hl : length s₁ = length s₂) : t₁ = t₂ :=
-- (append_inj h hl).right

-- theorem append_inj_left {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
--   (hl : length s₁ = length s₂) : s₁ = s₂ :=
-- (append_inj h hl).left

-- theorem append_inj' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
--   s₁ = s₂ ∧ t₁ = t₂ :=
-- append_inj h $ @Nat.add_right_cancel _ (length t₁) _ $
-- let hap := congr_arg length h in by simp only [length_append] at hap; rwa [← hl] at hap

-- theorem append_inj_right' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
--   (hl : length t₁ = length t₂) : t₁ = t₂ :=
-- (append_inj' h hl).right

-- theorem append_inj_left' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
--   (hl : length t₁ = length t₂) : s₁ = s₂ :=
-- (append_inj' h hl).left

-- theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
-- append_inj_right h rfl

-- theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
-- append_inj_left' h rfl

-- theorem append_right_injective (s : List α) : function.injective (fun  t, s ++ t) :=
-- fun  t₁ t₂, append_left_cancel

-- theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
-- (append_right_injective s).eq_iff

-- theorem append_left_injective (t : List α) : function.injective (fun  s, s ++ t) :=
-- fun  s₁ s₂, append_right_cancel

-- theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
-- (append_left_injective t).eq_iff

-- theorem map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
--   (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
-- begin
--   have := h, rw [← take_append_drop (length s₁) l] at this ⊢,
--   rw map_append at this,
--   refine ⟨_, _, rfl, append_inj this _⟩,
--   rw [length_map, length_take, min_eq_left],
--   rw [← length_map f l, h, length_append],
--   apply Nat.le_add_right
-- end

/-! ### repeat -/

@[simp] def repeat (a: α): ℕ -> List α
| 0 => []
| Nat.succ n => a :: repeat a n

@[simp] def repeatSucc (a: α) (n: ℕ): repeat a (n + 1) = a :: repeat a n := rfl
theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} :
  b ∈ List.bind l f → ∃ a, a ∈ l ∧ b ∈ f a :=
mem_bind.1

/-! ### insert -/
section insert
variable [DecidableEq α]

def insert (a : α) (l : List α) := if a ∈ l then l else a :: l

@[simp] theorem insert_of_mem  {a : α} {l : List α} (h : a ∈ l) : insert a l = l := by
  simp only [insert, if_pos h]; rfl

@[simp] theorem insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : insert a l = a :: l := by
  simp only [insert, if_neg h]; rfl

@[simp] theorem mem_insert_iff {a b : α} {l : List α} : a ∈ insert b l ↔ a = b ∨ a ∈ l := by
  byCases h : b ∈ l
  focus
    rw [insert_of_mem h]
    split; apply Or.inr
    intro h
    cases h with
    | inl h' => rw [h']; exact h
    | inr h' => exact h'
  focus
    rw [insert_of_not_mem h]; rfl

@[simp] theorem mem_insert_self (a : α) (l : List α) : a ∈ insert a l :=
mem_insert_iff.2 (Or.inl rfl)

theorem mem_insert_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ insert b l :=
mem_insert_iff.2 (Or.inr h)

theorem eq_or_mem_of_mem_insert {a b : α} {l : List α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {a : α} {l : List α} (h : a ∈ l) :
    length (insert a l) = length l := by
  rw [insert_of_mem h]

@[simp] theorem length_insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) :
  length (insert a l) = length l + 1 := by
rw [insert_of_not_mem h, ←length'_eq_length, ←length'_eq_length]; rfl

end insert

/-! ### erasep -/

def erasep (p : α → Prop) [DecidablePred p] : List α → List α
| []     => []
| (a::l) => if p a then l else a :: erasep p l

section erasep

variable {p : α → Prop} [DecidablePred p]

@[simp] theorem erasep_nil : [].erasep p = [] := rfl

theorem erasep_cons (a : α) (l : List α) :
  (a :: l).erasep p = if p a then l else a :: l.erasep p := rfl

@[simp] theorem erasep_cons_of_pos {a : α} {l : List α} (h : p a) : (a :: l).erasep p = l := by
  simp [erasep_cons, h]

@[simp] theorem erasep_cons_of_neg {a : α} {l : List α} (h : ¬ p a) :
  (a::l).erasep p = a :: l.erasep p := by
  simp [erasep_cons, h]

theorem erasep_of_forall_not {l : List α}
  (h : ∀ a, a ∈ l → ¬ p a) : l.erasep p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (Or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]

theorem exists_of_erasep {l : List α} {a} (al : a ∈ l) (pa : p a) :
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
  induction l with
  | nil => cases al
  | cons b l ih =>
    byCases pb : p b; focus
      exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
    focus
      cases al with
      | inl aeqb => rw [aeqb] at pa; exact False.elim $ pb pa
      | inr al =>
        match ih al with
        | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ =>
            exact ⟨c, b::l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩,
              h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_erasep (p : α → Prop) [DecidablePred p] (l : List α) :
    l.erasep p = l ∨
      ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
  byCases h : ∃ a ∈ l, p a; focus
    match h with
    | ⟨a, ha, pa⟩ => exact Or.inr (exists_of_erasep ha pa)
  focus
    simp at h
    exact Or.inl (erasep_of_forall_not h)

@[simp] theorem length_erasep_of_mem {l : List α} {a} (al : a ∈ l) (pa : p a) :
   length (l.erasep p) = Nat.pred (length l) :=
  match exists_of_erasep al pa with
  | ⟨_, l₁, l₂, _, _, e₁, e₂⟩ => by
    rw [e₂]; simp [length_append, e₁]; rfl

theorem erasep_append_left {a : α} (pa : p a) :
  ∀ {l₁ : List α} (l₂), a ∈ l₁ → (l₁++l₂).erasep p = l₁.erasep p ++ l₂
| (x::xs), l₂, h => by
  byCases h' : p x; focus
    simp [h']
  simp [h']
  rw [erasep_append_left pa l₂ (mem_of_ne_of_mem (mt _ h') h)]
  intro h
  cases h
  exact pa

theorem erasep_append_right :
  ∀ {l₁ : List α} (l₂), (∀ b ∈ l₁, ¬ p b) → erasep p (l₁++l₂) = l₁ ++ l₂.erasep p
| [],      l₂, h => rfl
| (x::xs), l₂, h =>
  by simp [(forall_mem_cons.1 h).1,
     erasep_append_right _ (forall_mem_cons.1 h).2]

-- theorem erasep_subList (l : List α) : l.erasep p <+ l :=
-- by rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩;
--    [rw h, {rw [h₄, h₃], simp}]

theorem erasep_subset (l : List α) : l.erasep p ⊆ l := by
  intro a
  cases exists_or_eq_self_of_erasep p l with
  | inl h => rw [h]; apply subset.refl
  | inr h =>
    match h with
    | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ =>
      rw [h₄, h₃, mem_append, mem_append]
      intro
      | Or.inl h => exact Or.inl h
      | Or.inr h => exact Or.inr $ mem_cons_of_mem _ h
-- the proof was:
-- (erasep_subList l).subset

-- theorem subList.erasep {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
-- begin
--   induction s,
--   case List.subList.slnil { refl },
--   case List.subList.cons : l₁ l₂ a s IH {
--     by_cases h : p a; simp [h],
--     exacts [IH.trans (erasep_subList _), IH.cons _ _ _] },
--   case List.subList.cons2 : l₁ l₂ a s IH {
--     by_cases h : p a; simp [h],
--     exacts [s, IH.cons2 _ _ _] }
-- end

theorem mem_of_mem_erasep {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
@erasep_subset _ _ _ _ _

@[simp] theorem mem_erasep_of_neg {a : α} {l : List α} (pa : ¬ p a) : a ∈ l.erasep p ↔ a ∈ l := by
  refine ⟨mem_of_mem_erasep, ?_⟩
  intro al
  apply Or.elim (exists_or_eq_self_of_erasep p l)
  { intro h; rw [h]; assumption }
  intro ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩
  rw [h₄]
  rw [h₃] at al
  have : a ≠ c := by { intro h; rw [h] at pa; exact pa.elim h₂ }
  simp [this] at al
  simp [al]

theorem erasep_map (f : β → α) :
  ∀ (l : List β), (map f l).erasep p = map f (l.erasep (p ∘ f))
| []     => rfl
| (b::l) => by
  (byCases h : p (f b))
  - simp [h, erasep_map f l, @erasep_cons_of_pos β (p ∘ f) _ b l h]
  - simp [h, erasep_map f l, @erasep_cons_of_neg β (p ∘ f) _ b l h]

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
    (b :: l).erase a = if b = a then l else b :: l.erase a := by
  byCases h : a = b
  focus
    simp only [if_pos h.symm, List.erase, EqIffBeqTrue.mp h.symm]; rfl
  simp only [if_neg (Ne.symm h), List.erase, NeqIffBeqFalse.mp (Ne.symm h)]; rfl

@[simp] theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) :
  (b::l).erase a = b :: l.erase a :=
by simp only [erase_cons, if_neg h]; rfl

theorem erase_eq_erasep (a : α) (l : List α) : l.erase a = l.erasep (Eq a) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      byCases h : a = b; focus
        simp [h]
      simp [h, Ne.symm h, ih]

@[simp]
theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l := by
  induction l with
    | nil => rfl
    | cons b l ih =>
      rw [mem_cons, not_or] at h
      rw [erase_cons, if_neg (Ne.symm h.1), ih h.2]

-- TODO: ∉ should have higher priority
theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, (a ∉ l₁) ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
  match exists_of_erasep h rfl with
  | ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩ => by
    rw [erase_eq_erasep]; exact ⟨l₁, l₂, fun h => h₁ _ h rfl, h₂, h₃⟩

@[simp] theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) :
  length (l.erase a) = Nat.pred (length l) :=
by rw [erase_eq_erasep]; exact length_erasep_of_mem h rfl

theorem erase_append_left {a : α} {l₁ : List α} (l₂) (h : a ∈ l₁) :
  (l₁++l₂).erase a = l₁.erase a ++ l₂ :=
by simp [erase_eq_erasep]; exact erasep_append_left (by rfl) l₂ h

theorem erase_append_right {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁++l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right]
  intros b h' h''; rw [h''] at h; exact h h'

-- theorem erase_subList (a : α) (l : List α) : l.erase a <+ l :=
-- by rw erase_eq_erasep; apply erasep_subList

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l :=
by rw [erase_eq_erasep]; apply erasep_subset
--(erase_subList a l).subset

-- theorem subList.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a :=
-- by simp [erase_eq_erasep]; exact subList.erasep h

theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
@erase_subset _ _ _ _ _

@[simp] theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
by rw [erase_eq_erasep]; exact mem_erasep_of_neg ab.symm

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

-- /-! ### union -/

section

variable [DecidableEq α]

protected def union (l₁ l₂ : List α) : List α :=
foldr insert l₂ l₁

@[simp] theorem nil_union (l : List α) : nil.union l = l := by simp [List.union, foldr]

@[simp] theorem cons_union (a : α) (l₁ l₂ : List α) :
  (a :: l₁).union l₂ = insert a (l₁.union l₂) := by simp [List.union, foldr]

@[simp] theorem mem_union_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁.union l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l' ih => simp [ih, or_assoc]

end

-- /-! ### inter -/

protected def inter [DecidableEq α] (l₁ l₂ : List α) : List α :=
filter (fun a => a ∈ l₂) l₁

@[simp] theorem mem_inter_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁.inter l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  induction l₁ with
  | nil => simp [List.inter, mem_filter]
  | cons a l' ih => simp [List.inter, mem_filter, decide_eq_true_iff (x ∈ l₂)]

end List
