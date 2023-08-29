/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Multiset.Bind

#align_import data.multiset.sections from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Sections of a multiset
-/


namespace Multiset

variable {α : Type*}

section Sections

/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is a member of the corresponding multiset.
-/

def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]
    -- 🎉 no goals
#align multiset.sections Multiset.Sections

@[simp]
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl
#align multiset.sections_zero Multiset.sections_zero

@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s
#align multiset.sections_cons Multiset.sections_cons

theorem coe_sections :
    ∀ l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp
    -- ⊢ Sections ↑(↑a :: List.map (fun l => ↑l) l) = ↑(List.map (fun l => ↑l) (List. …
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    -- ⊢ (bind ↑(List.map (fun l => ↑l) (List.sections l)) fun b => map (fun a => a : …
    simp [List.sections, (· ∘ ·), List.bind]
    -- 🎉 no goals
#align multiset.coe_sections Multiset.coe_sections

@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map ((· + ·) m) :=
  Multiset.induction_on s (by simp) fun a s ih => by
                              -- 🎉 no goals
    simp [ih, bind_assoc, map_bind, bind_map]
    -- 🎉 no goals
#align multiset.sections_add Multiset.sections_add

theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ Sections s ↔ s.Rel (fun s a => a ∈ s) a := by
  induction s using Multiset.induction_on
  -- ⊢ ∀ {a : Multiset α}, a ∈ Sections 0 ↔ Rel (fun s a => a ∈ s) 0 a
  case empty => simp
  -- ⊢ ∀ {a : Multiset α}, a ∈ Sections (a✝¹ ::ₘ s✝) ↔ Rel (fun s a => a ∈ s) (a✝¹  …
  -- 🎉 no goals
  case cons a a' ih => simp [ih, rel_cons_left, eq_comm]
  -- 🎉 no goals
  -- 🎉 no goals
#align multiset.mem_sections Multiset.mem_sections

theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.card_sections Multiset.card_sections

theorem prod_map_sum [CommSemiring α] {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
                              -- 🎉 no goals
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
    -- 🎉 no goals
#align multiset.prod_map_sum Multiset.prod_map_sum

end Sections

end Multiset
