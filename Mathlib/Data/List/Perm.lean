import Mathlib.Init.Set
import Mathlib.Data.List.Basic

namespace List

/-- `Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are Permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive Perm {α} : List α → List α → Prop
| nil   : Perm [] []
| cons  : ∀ (x : α) {l₁ l₂ : List α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
| swap  : ∀ (x y : α) (l : List α), Perm (y::x::l) (x::y::l)
| trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

open Perm

infixl:50 " ~ " => Perm

protected theorem Perm.refl : ∀ (l : List α), l ~ l
| []      => Perm.nil
| (x::xs) => (Perm.refl xs).cons x

protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ := by
induction p with
| nil => exact Perm.nil
| cons x _ ih => exact Perm.cons x ih
| swap x y l => exact Perm.swap y x l
| trans _ _ ih₁ ih₂ => exact Perm.trans ih₂ ih₁

theorem Perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y::x::l₁ ~ x::y::l₂ :=
  have h1 : y :: l₁ ~ y :: l₂ := Perm.cons y p
  have h2 : x :: y :: l₁ ~ x :: y :: l₂ := Perm.cons x h1
  have h3 : y :: x :: l₁ ~ x :: y :: l₁ := Perm.swap x y l₁
  Perm.trans h3 h2

theorem Perm.Equivalence : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩

instance (α : Type u) : Setoid (List α) := ⟨Perm, Perm.Equivalence⟩

theorem Perm.subset {α : Type u} {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := by
  induction p with
  | nil => exact nil_subset _
  | cons _ _ ih => exact cons_subset_cons _ ih
  | swap x y l =>
    intro a
    rw [mem_cons]
    exact fun
    | Or.inl rfl => Mem.tail _ (Mem.head ..)
    | Or.inr (Mem.head ..) => Mem.head ..
    | Or.inr (Mem.tail _ a_mem_l) => Mem.tail _ (Mem.tail _ a_mem_l)
  | trans _ _ ih₁ ih₂ => exact subset.trans ih₁ ih₂

theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁++a::l₂ ~ a::(l₁++l₂)
| [], _ => Perm.refl _
| b::l₁, l₂ =>
  let h2 := @perm_middle α a l₁ l₂
  (h2.cons _).trans (swap a b _)


set_option linter.unusedVariables false in -- FIXME: lean4#1214
theorem perm_insertNth {x : α} : ∀ {l : List α} {n : Nat}, n ≤ l.length →
  insertNth n x l ~ x :: l
| [], 0, _ => Perm.refl _
| [], _+1, h => False.elim (Nat.not_succ_le_zero _ h)
| _::_, 0, _ => Perm.refl _
| _::_, _+1, h =>
  Perm.trans
    (Perm.cons _ (perm_insertNth (Nat.le_of_succ_le_succ h)))
    (Perm.swap _ _ _)
