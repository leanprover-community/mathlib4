/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Monotone.Monovary
import Mathlib.SetTheory.Cardinal.Order

/-!
# Interpreting monovarying functions as monotone functions

This file proves that monovarying functions to linear orders can be made simultaneously monotone by
setting the correct order on their shared indexing type.
-/

open Function Set

variable {ι ι' α β γ : Type*}

section
variable [LinearOrder α] [LinearOrder β] (f : ι → α) (g : ι → β) {s : Set ι}

/-- If `f : ι → α` and `g : ι → β` are monovarying, then `MonovaryOrder f g` is a linear order on
`ι` that makes `f` and `g` simultaneously monotone.
We define `i < j` if `f i < f j`, or if `f i = f j` and `g i < g j`, breaking ties arbitrarily. -/
def MonovaryOrder (i j : ι) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)

instance : IsStrictTotalOrder ι (MonovaryOrder f g) where
  trichotomous i j := by
    convert trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc, imp_and, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [MonovaryOrder]; exact irrefl _
  trans i j k := by rw [MonovaryOrder]; exact _root_.trans

variable {f g}

lemma monovaryOn_iff_exists_monotoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ MonotoneOn g s := by
  classical
  letI := linearOrderOfSTO (MonovaryOrder f g)
  refine ⟨fun hfg => ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_,
    monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_⟩, ?_⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 hij
    · exact hfg.symm hi hj h
    obtain h | ⟨h, -⟩ := Prod.lex_iff.1 h <;> exact h.le
  · rintro ⟨_, hf, hg⟩
    exact hf.monovaryOn hg

lemma antivaryOn_iff_exists_monotoneOn_antitoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

lemma monovaryOn_iff_exists_antitoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]

lemma antivaryOn_iff_exists_antitoneOn_monotoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ MonotoneOn g s := by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]

lemma monovary_iff_exists_monotone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Monotone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]

lemma monovary_iff_exists_antitone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Antitone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]

lemma antivary_iff_exists_monotone_antitone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Antitone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]

lemma antivary_iff_exists_antitone_monotone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Monotone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn
alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn
alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exists_monotoneOn_antitoneOn
alias ⟨AntivaryOn.exists_antitoneOn_monotoneOn, _⟩ := antivaryOn_iff_exists_antitoneOn_monotoneOn
alias ⟨Monovary.exists_monotone, _⟩ := monovary_iff_exists_monotone
alias ⟨Monovary.exists_antitone, _⟩ := monovary_iff_exists_antitone
alias ⟨Antivary.exists_monotone_antitone, _⟩ := antivary_iff_exists_monotone_antitone
alias ⟨Antivary.exists_antitone_monotone, _⟩ := antivary_iff_exists_antitone_monotone

end
