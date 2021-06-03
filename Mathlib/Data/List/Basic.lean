import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Mem
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
| a::l, k+1, h => drop_eq_nil_of_le' (l := l) h

theorem drop_eq_nil_of_le {l : List α} {k : Nat} : (h : l.length ≤ k) → l.drop k = [] :=
by rw [← length'_eq_length]; exact drop_eq_nil_of_le'

/-- List membership. -/
def mem (a : α) : List α → Prop
| [] => False
| (b :: l) => a = b ∨ mem a l

instance : Mem α (List α) := ⟨mem⟩
--infix:50 " ∈ " => mem

@[simp] lemma mem_nil (a : α) : a ∈ [] ↔ False := Iff.rfl

@[simp] lemma mem_cons {a b : α} {l : List α} :
  a ∈ (b :: l) ↔ a = b ∨ a ∈ l := Iff.rfl

theorem mem_append {a} : ∀ {l₁ l₂ : List α}, a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂
| [], _ => by simp
| b :: l₁, l₂ => by simp [or_assoc, mem_append];

@[simp] theorem map_nil {f : α → β} : map f [] = [] := rfl
@[simp] theorem map_cons {f : α → β} : map f (b :: l) = f b :: l.map f := rfl

theorem mem_map {f : α → β} {b} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ b = f a
| [] => by simp; intro ⟨_, e⟩; exact e
| b :: l => by
  rw [map_cons, mem_cons, mem_map];
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

@[simp] theorem join_nil : join ([] : List (List α)) = [] := rfl

@[simp] theorem join_cons : join (a :: l : List (List α)) = a ++ join l := rfl

theorem mem_join {a} : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
| [] => by simp; intro ⟨_, e⟩; exact e
| b :: l => by
  simp only [join, mem_append, mem_join]
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

theorem mem_bind {f : α → List β} {b} {l : List α} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_map, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

end List
