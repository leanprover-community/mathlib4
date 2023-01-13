/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.multiset.sections
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Bind

/-!
# Sections of a multiset
-/


namespace Multiset

variable {α : Type _}

section Sections

/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/
def sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ s pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]
#align multiset.sections Multiset.sections

@[simp]
theorem sections_zero : sections (0 : Multiset (Multiset α)) = {0} :=
  rfl
#align multiset.sections_zero Multiset.sections_zero

@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    sections (m ::ₘ s) = m.bind fun a => (sections s).map (Multiset.cons a) :=
  rec_on_cons m s
#align multiset.sections_cons Multiset.sections_cons

theorem coe_sections :
    ∀ l : List (List α),
      sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    simp [List.sections, (· ∘ ·), List.bind]
#align multiset.coe_sections Multiset.coe_sections

@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
    sections (s + t) = (sections s).bind fun m => (sections t).map ((· + ·) m) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map, -add_comm]
#align multiset.sections_add Multiset.sections_add

theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ sections s ↔ s.Rel (fun s a => a ∈ s) a :=
  Multiset.induction_on s (by simp) fun a s ih a' => by
    simp [ih, rel_cons_left, -exists_and_left, exists_and_distrib_left.symm, eq_comm]
#align multiset.mem_sections Multiset.mem_sections

theorem card_sections {s : Multiset (Multiset α)} : card (sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
#align multiset.card_sections Multiset.card_sections

theorem prod_map_sum [CommSemiring α] {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
#align multiset.prod_map_sum Multiset.prod_map_sum

end Sections

end Multiset

