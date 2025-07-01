import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/- FINSET and FINTYPES -/

/- Finsets have a computational interpetation -/

variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp; tauto

#check ({0, 2, 5} : Finset Nat)
#check ({0, 2, 5} : Set Nat)

def example1 : Finset ℕ := {0, 1, 2}

example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide
example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide
example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : ℕ) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : ℕ) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp; tauto

example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s).erase a = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h

set_option pp.notation false in
#check ({0, 2, 2} : Finset ℕ)

example : {m ∈ range n | Even m} = (range n).filter Even := rfl
example : {m ∈ range n | Even m ∧ m ≠ 3} = (range n).filter (fun m ↦ Even m ∧ m ≠ 3) := rfl
example : {m ∈ range 10 | Even m} = {0, 2, 4, 6, 8} := by decide

#check (range 5).image (fun x ↦ x * 2)

example : (range 5).image (fun x ↦ x * 2) = {x ∈ range 10 | Even x} := by decide

#check s ×ˢ t
#check s.powerset

def f (n : ℕ) : Int := n ^ 2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i ^ 2
#check ∏ i ∈ range 5, i + 1

variable (g : ℕ → Finset Int)

#check (range 5).biUnion g

#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ) (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s anins ih =>
    rw [prod_insert anins]
    apply mul_ne_zero
    · apply h; apply mem_insert_self
    apply ih
    intro x xs
    exact h x (mem_insert_of_mem xs)

/- If `s` is a finset, Finset.Nonempty `s` is defined to be `∃ x, x ∈ s`. -/

noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s := Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩

example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial

#check Finset.card

#eval (range 5).card

example (s : Finset ℕ) : s.card = #s := by rfl

example (s : Finset ℕ) : s.card = ∑ _ ∈ s, 1 := by rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ _ ∈ s, 1 := by simp

/- By definition a fintype is just a data type that comes equipped with a finset `univ` that
contains all its elements -/

variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x

#check Fintype.card α

example : Fintype.card α = (Finset.univ : Finset α).card := rfl

example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp

/- Counting Arguments -/

section Finset

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]

open Fintype

end Finset

section Fintype

open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α) ^ n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

end Fintype

/- Examples -/

#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_image_of_injective, card_range]; omega
  · apply add_right_injective
  · simp [disjoint_iff_ne]; omega

def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (·, j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    · rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  trans (∑ i in range (n + 1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
          omega
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          congr 1
          rw [card_image_of_injOn]
          intro x hx y hy h
          simp [triangle, turn] at *
          have ⟨h1, h2⟩ := h
          rw[Nat.sub_eq_iff_eq_add', ← Nat.sub_eq_iff_eq_add, Nat.sub_sub_eq_min,
            Nat.min_eq_right] at h1 h2
          · ext
            · exact h1.symm
            · exact h2.symm
          all_goals omega
    _ = #(range n ×ˢ range (n + 1)) := by
          rw [← card_union_of_disjoint]; swap
          · sorry
          congr
          sorry
    _ = (n + 1) * n := by
          simp [mul_comm]
