/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordinal arithmetic commutativity

Results on the commutativity of ordinal arithmetic operations.

## References

* [Wacław Sierpiński, *Cardinal and Ordinal Numbers*][sierpinski1958]
-/

public section

namespace Ordinal

variable (o a b : Ordinal)

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

/-- Ordinal addition annihilates the terms in the left-summand which are smaller than the most
significant term of the right-summand -/
theorem omega0_opow_log_mul_div_add : ω ^ log ω b * (a / ω ^ log ω b) + b = a + b := by
  have : a % ω ^ log ω b + b = b :=
    add_of_lt_omega0_opow_log <| mod_lt a <| opow_ne_zero _ omega0_ne_zero
  nth_rw 3 [← this]
  rw [← add_assoc, div_add_mod]

theorem addCommute_omega0_opow_log_add_mod : AddCommute o <| ω ^ log ω o + o % ω ^ log ω o := by
  rcases eq_or_ne o 0 with (rfl | h0)
  · simp
  nth_rw 1 [← div_add_mod o <| ω ^ log ω o]
  rw [addCommute_iff_eq]
  have hlt := mod_lt o <| opow_ne_zero (log ω o) omega0_ne_zero
  rw [add_assoc, ← add_assoc <| o % _, add_omega0_opow hlt, add_assoc, ← add_assoc <| o % _,
    add_of_omega0_opow_le hlt <| le_mul_left _ <| div_opow_log_pos ω h0, ← add_assoc, ← add_assoc,
    ← mul_add_one, ← mul_one_add]
  rcases lt_omega0.mp <| div_opow_log_lt o one_lt_omega0 with ⟨n, hn⟩
  simp [hn]

variable {a b} in
theorem add_lt_add_of_lt_omega0_opow_log_add_mod (hle : ω ^ log ω a ≤ b)
    (hlt : b < ω ^ log ω a + a % ω ^ log ω a) : a + b < b + a := by
  rcases eq_or_ne b 0 with (rfl | h0')
  · simp at hle
  rcases eq_or_ne a 0 with (rfl | h0)
  · exact absurd h0' <| by simpa using hlt
  rw [← div_add_mod a <| ω ^ log ω a, ← div_add_mod b <| ω ^ log ω a]
  have hr := mod_lt a <| opow_ne_zero (log ω a) omega0_ne_zero
  have hr' := mod_lt b <| opow_ne_zero (log ω a) omega0_ne_zero
  have hlog : log ω b = log ω a := log_eq_iff one_lt_omega0 h0' _ |>.mpr <| by
    refine ⟨hle, lt_omega0_opow_succ.mpr ⟨2, hlt.trans_le ?_⟩⟩
    grw [hr, Nat.cast_two, Ordinal.mul_two]
  have hc' := hlog ▸ div_opow_log_pos ω h0'
  rw [add_assoc, ← add_assoc <| a % _, add_of_omega0_opow_le hr <| le_mul_left _ hc', add_assoc,
    ← add_assoc <| b % _, add_of_omega0_opow_le hr' <| le_mul_left _ <| div_opow_log_pos ω h0,
    ← add_assoc, ← add_assoc, ← mul_add, ← mul_add]
  rcases lt_omega0.mp <| div_opow_log_lt a one_lt_omega0 with ⟨n, hn⟩
  rcases lt_omega0.mp <| hlog ▸ div_opow_log_lt b one_lt_omega0 with ⟨n', hn'⟩
  rw [hn, hn', ← Nat.cast_add, add_comm, Nat.cast_add, add_lt_add_iff_left,
    ← add_lt_add_iff_left <| ω ^ log ω a]
  refine lt_of_le_of_lt ?_ hlt
  nth_rw 2 [← div_add_mod b <| ω ^ log ω a]
  grw [← le_mul_left _ <| (div_pos <| opow_ne_zero _ omega0_ne_zero).mpr hle]

variable {a b} in
theorem omega0_opow_log_add_mod_le_of_addCommute (h0 : b ≠ 0) (h : AddCommute a b) :
    ω ^ log ω a + a % ω ^ log ω a ≤ b := by
  rw [addCommute_iff_eq] at h
  contrapose! h
  rcases lt_or_ge b <| ω ^ log ω a with (h' | h')
  · grind [add_ne_left, add_of_lt_omega0_opow_log]
  have := add_lt_add_of_lt_omega0_opow_log_add_mod h' h
  grind

/-- `ω ^ log ω o + o % ω ^ log ω o` is the smallest nonzero ordinal that add-commutes with `o`.
This value can also be calculated by considering the CNF of `o` with base `ω` and changing the first
coefficient to `1`. -/
theorem minimal_addCommute_omega0_opow_log_add_mod :
    Minimal (fun x ↦ x ≠ 0 ∧ AddCommute o x) <| ω ^ log ω o + o % ω ^ log ω o := by
  refine ⟨?_, fun x ⟨h0, h⟩ hle ↦ omega0_opow_log_add_mod_le_of_addCommute h0 h⟩
  simpa using o.addCommute_omega0_opow_log_add_mod

end Ordinal
