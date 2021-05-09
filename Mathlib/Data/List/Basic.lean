import Mathlib.Logic.Basic

namespace List

/-- List membership. -/
def mem (a : α) : List α → Prop
| [] => False
| (b :: l) => a = b ∨ mem a l

infix:50 " ∈ " => mem

theorem mem_append {a} : ∀ {l₁ l₂ : List α}, a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂
| [], _ => by simp [mem]
| b :: l₁, l₂ => by simp only [List.cons_append, mem, or_assoc, mem_append]; exact Iff.rfl

theorem mem_map {f : α → β} {b} : ∀ {l}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ b = f a
| [] => by simp [mem]; intro ⟨_, e⟩; exact e
| b :: l => by
  simp only [join, mem, mem_map]
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

theorem mem_join {a} : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
| [] => by simp [mem]; intro ⟨_, e⟩; exact e
| b :: l => by
  simp only [join, mem, mem_append, mem_join]
  exact ⟨fun | Or.inl h => ⟨_, Or.inl rfl, h⟩
             | Or.inr ⟨l, h₁, h₂⟩ => ⟨l, Or.inr h₁, h₂⟩,
         fun | ⟨_, Or.inl rfl, h⟩ => Or.inl h
             | ⟨l, Or.inr h₁, h₂⟩ => Or.inr ⟨l, h₁, h₂⟩⟩

theorem mem_bind {f : α → List β} {b} {l} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_map, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

end List
