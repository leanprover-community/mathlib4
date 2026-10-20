/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal arithmetic commutativity

Results on the commutativity of ordinal arithmetic operations.

## References

* [Wacław Sierpiński, *Cardinal and Ordinal Numbers*][sierpinski1958]
-/

public section

namespace Ordinal

theorem addCommute_iff_eq_mul_natCast {o₁ o₂ : Ordinal} :
    AddCommute o₁ o₂ ↔ ∃ (o : Ordinal) (n₁ n₂ : ℕ), o * n₁ = o₁ ∧ o * n₂ = o₂ := by
  refine ⟨fun hcomm ↦ ?_, ?_⟩
  · induction h : o₁ + o₂ using WellFoundedLT.induction generalizing o₁ o₂ with | ind o ih
    subst h
    wlog hle : o₁ ≤ o₂
    · grind [hcomm.symm]
    rcases eq_or_ne o₁ 0 with (rfl | h₁)
    · exact ⟨o₂, 0, 1, by simp, by simp⟩
    let o₃ := o₂ - o₁
    have hsub : o₁ + o₃ = o₂ := Ordinal.add_sub_cancel_of_le hle
    have hcomm' : AddCommute o₁ o₃ := add_left_cancel (a := o₁) <| by grind
    have hlt : o₁ + o₃ < o₁ + o₂ := by simpa [hsub, hcomm.eq] using h₁.pos
    rcases ih _ hlt hcomm' rfl with ⟨o, n₁, n₃, hn₁, hn₃⟩
    use o, n₁, n₁ + n₃, hn₁
    rw [Nat.cast_add, mul_add, hn₁, hn₃, hsub]
  · rintro ⟨o, n₁, n₂, rfl, rfl⟩
    rw [addCommute_iff_eq, ← mul_add, ← mul_add, ← Nat.cast_add, add_comm, Nat.cast_add]

end Ordinal
