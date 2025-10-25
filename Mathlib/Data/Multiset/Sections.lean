/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Multiset.Bind

/-!
# Sections of a multiset
-/

assert_not_exists Ring

namespace Multiset

variable {α : Type*}

section Sections

/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is a member of the corresponding multiset.
-/
def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl

@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s

theorem coe_sections :
    ∀ l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sections]
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    simp [Function.comp_def, List.flatMap]

@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map (m + ·) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]

theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ Sections s ↔ s.Rel (fun s a => a ∈ s) a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih, rel_cons_left, eq_comm]

theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp +contextual)

end Sections

end Multiset
