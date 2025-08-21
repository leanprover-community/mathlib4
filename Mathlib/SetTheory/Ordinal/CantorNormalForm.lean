/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Family

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open List

namespace Ordinal.CNF

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
protected def rec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[deprecated (since := "2025-08-18")]
noncomputable alias _root_.Ordinal.CNFRec := CNF.rec

@[simp]
theorem rec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNF.rec b H0 H 0 = H0 := by
  rw [CNF.rec, dif_pos rfl]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNFRec_zero := rec_zero

theorem rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNF.rec b H0 H o = H o ho (@CNF.rec b C H0 H _) := by
  rw [CNF.rec, dif_neg]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNFRec_pos := rec_pos

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def _root_.Ordinal.CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNF.rec b [] (fun o _ IH ↦ (log b o, o / b ^ log b o)::IH) o

@[simp]
theorem zero_right (b : Ordinal) : CNF b 0 = [] :=
  rec_zero b _ _

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_zero := zero_right

/-- Recursive definition for the Cantor normal form. -/
protected theorem ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  rec_pos b ho _ _

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_ne_zero := CNF.ne_zero

protected theorem zero_left {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.zero_CNF := CNF.zero_left

protected theorem one_left {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.one_CNF := CNF.one_left

protected theorem of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [(0, o)] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_of_le_one := CNF.of_le_one

protected theorem of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [(0, o)] := by
  rw [CNF.ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, zero_right]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_of_lt := CNF.of_lt

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
protected theorem foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho, foldr_cons, IH, div_add_mod]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_foldr := CNF.foldr

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNF.rec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_fst_le_log := fst_le_log

/-- Every coefficient in a Cantor normal form is positive. -/
theorem lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNF.rec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_lt_snd := lt_snd

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_snd_lt := snd_lt

/-- The exponents of the Cantor normal form are decreasing. -/
protected theorem sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) := by
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · rw [zero_right]
    exact sorted_nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exact sorted_singleton _
      · rw [CNF.ne_zero ho, map_cons, sorted_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_sorted := CNF.sorted

end Ordinal.CNF
