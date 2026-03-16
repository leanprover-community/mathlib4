/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Analyzing ordinal arithmetic

We analyze arithmetic operations on ordinals and prove various properties about them.
-/

public section

namespace Ordinal

/-- Ordinal addition annihilates the terms in the left-summand which are smaller than the most
significant term of the right-summand -/
theorem omega0_opow_log_mul_div_add (o o' : Ordinal) :
    (ω ^ log ω o') * (o / (ω ^ log ω o')) + o' = o + o' := by
  have : (o % (ω ^ log ω o')) + o' = o' :=
    add_absorp_of_lt_omega0_opow_log <| mod_lt o <| opow_ne_zero _ omega0_ne_zero
  nth_rw 3 [← this]
  rw [← add_assoc, div_add_mod]

theorem addCommute_omega0_opow_log_add_mod (o : Ordinal) :
    AddCommute o ((ω ^ log ω o) + o % (ω ^ log ω o)) := by
  rcases eq_or_ne o 0 with (rfl | h0)
  · simp
  nth_rw 1 [← div_add_mod o <| ω ^ log ω o]
  rw [addCommute_iff_eq]
  have hlt := mod_lt o <| opow_ne_zero (log ω o) omega0_ne_zero
  rw [add_assoc, ← add_assoc <| o % _, add_omega0_opow hlt, add_assoc, ← add_assoc <| o % _,
    add_absorp hlt <| le_mul_left _ <| div_opow_log_pos ω h0, ← add_assoc, ← add_assoc,
    ← mul_add_one, ← mul_one_add]
  rcases lt_omega0.mp <| div_opow_log_lt o one_lt_omega0 with ⟨n, hn⟩
  simp [hn]

theorem add_lt_add_of_lt_omega0_opow_log_add_mod {o o' : Ordinal} (hle : ω ^ log ω o ≤ o')
    (hlt : o' < (ω ^ log ω o) + o % (ω ^ log ω o)) : o + o' < o' + o := by
  rcases eq_or_ne o' 0 with (rfl | h0')
  · simp at hle
  rcases eq_or_ne o 0 with (rfl | h0)
  · exact absurd h0' <| by simpa using hlt
  rw [← div_add_mod o <| ω ^ log ω o, ← div_add_mod o' <| ω ^ log ω o]
  have hr := mod_lt o <| opow_ne_zero (log ω o) omega0_ne_zero
  have hr' := mod_lt o' <| opow_ne_zero (log ω o) omega0_ne_zero
  have hlog : log ω o' = log ω o := log_eq_iff one_lt_omega0 h0' _ |>.mpr <| by
    refine ⟨hle, lt_omega0_opow_succ.mpr ⟨2, hlt.trans_le ?_⟩⟩
    grw [hr, Nat.cast_two, Ordinal.mul_two]
  have hc' := hlog ▸ div_opow_log_pos ω h0'
  rw [add_assoc, ← add_assoc <| o % _, add_absorp hr <| le_mul_left _ hc', add_assoc,
    ← add_assoc <| o' % _, add_absorp hr' <| le_mul_left _ <| div_opow_log_pos ω h0, ← add_assoc,
    ← add_assoc, ← mul_add, ← mul_add]
  rcases lt_omega0.mp <| div_opow_log_lt o one_lt_omega0 with ⟨n, hn⟩
  rcases lt_omega0.mp <| hlog ▸ div_opow_log_lt o' one_lt_omega0 with ⟨n', hn'⟩
  rw [hn, hn', ← Nat.cast_add, add_comm, Nat.cast_add, add_lt_add_iff_left,
    ← add_lt_add_iff_left <| ω ^ log ω o]
  refine lt_of_le_of_lt ?_ hlt
  nth_rw 2 [← div_add_mod o' <| ω ^ log ω o]
  grw [← le_mul_left _ <| (div_pos <| opow_ne_zero _ omega0_ne_zero).mpr hle]

theorem omega0_opow_log_add_mod_le_of_addCommute {o o' : Ordinal} (h0 : o' ≠ 0)
    (h : AddCommute o o') : (ω ^ log ω o) + o % (ω ^ log ω o) ≤ o' := by
  rw [addCommute_iff_eq] at h
  contrapose! h
  rcases lt_or_ge o' (ω ^ log ω o) with (h' | h')
  · grind [add_ne_left, add_absorp_of_lt_omega0_opow_log]
  have := add_lt_add_of_lt_omega0_opow_log_add_mod h' h
  grind

/-- `(ω ^ log ω o) + o % (ω ^ log ω o)` is the smallest nonzero ordinal that add-commutes with `o`.
This value can also be calculated by considering the CNF of `o` with base `ω` and changing the first
coefficient to `1`. -/
theorem minimal_addCommute_omega0_opow_log_add_mod (o : Ordinal) :
    Minimal (fun o' ↦ o' ≠ 0 ∧ AddCommute o o') ((ω ^ log ω o) + o % (ω ^ log ω o)) := by
  refine ⟨?_, fun o' ⟨h0, h⟩ hle ↦ omega0_opow_log_add_mod_le_of_addCommute h0 h⟩
  simpa using o.addCommute_omega0_opow_log_add_mod

end Ordinal
