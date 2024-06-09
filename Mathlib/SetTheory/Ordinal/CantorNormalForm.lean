/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

#align_import set_theory.ordinal.cantor_normal_form from "leanprover-community/mathlib"@"991ff3b5269848f6dd942ae8e9dd3c946035dc8b"

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

namespace Ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
noncomputable def CNFRec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o := fun o ↦ by
    by_cases h : o = 0
    · rw [h]; exact H0
    · exact H o h (CNFRec _ H0 H (o % b ^ log b o))
    termination_by o => o
    decreasing_by exact mod_opow_log_lt_self b h
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_rec Ordinal.CNFRec

@[simp]
theorem CNFRec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : @CNFRec b C H0 H 0 = H0 := by
  rw [CNFRec, dif_pos rfl]
  rfl
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_rec_zero Ordinal.CNFRec_zero

theorem CNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    @CNFRec b C H0 H o = H o ho (@CNFRec b C H0 H _) := by rw [CNFRec, dif_neg ho]
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_rec_pos Ordinal.CNFRec_pos

-- Porting note: unknown attribute @[pp_nodot]
/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
def CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNFRec b [] (fun o _ho IH ↦ (log b o, o / b ^ log b o)::IH) o
set_option linter.uppercaseLean3 false in
#align ordinal.CNF Ordinal.CNF

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_zero Ordinal.CNF_zero

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  CNFRec_pos b ho _ _
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_ne_zero Ordinal.CNF_ne_zero

theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
set_option linter.uppercaseLean3 false in
#align ordinal.zero_CNF Ordinal.zero_CNF

theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
set_option linter.uppercaseLean3 false in
#align ordinal.one_CNF Ordinal.one_CNF

theorem CNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [⟨0, o⟩] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
  · exact one_CNF ho
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_of_le_one Ordinal.CNF_of_le_one

theorem CNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [⟨0, o⟩] := by
  simp only [CNF_ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, CNF_zero]
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_of_lt Ordinal.CNF_of_lt

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o :=
  CNFRec b (by rw [CNF_zero]; rfl)
    (fun o ho IH ↦ by rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]) o
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_foldr Ordinal.CNF_foldr

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNFRec b ?_ (fun o ho H ↦ ?_) o
  · rw [CNF_zero]
    intro contra; contradiction
  · rw [CNF_ne_zero ho, mem_cons]
    rintro (rfl | h)
    · exact le_rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_fst_le_log Ordinal.CNF_fst_le_log

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) : x.1 ≤ o :=
  (CNF_fst_le_log h).trans <| log_le_self _ _
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_fst_le Ordinal.CNF_fst_le

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNFRec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF_ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_lt_snd Ordinal.CNF_lt_snd

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · simp only [CNF_zero, not_mem_nil, IsEmpty.forall_iff]
  · rw [CNF_ne_zero ho]
    intro h
    cases' (mem_cons.mp h) with h h
    · rw [h]; simpa only using div_opow_log_lt o hb
    · exact IH h
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_snd_lt Ordinal.CNF_snd_lt

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · simp only [gt_iff_lt, CNF_zero, map_nil, sorted_nil]
  · rcases le_or_lt b 1 with hb | hb
    · simp only [CNF_of_le_one hb ho, gt_iff_lt, map_cons, map, sorted_singleton]
    · cases' lt_or_le o b with hob hbo
      · simp only [CNF_of_lt ho hob, gt_iff_lt, map_cons, map, sorted_singleton]
      · rw [CNF_ne_zero ho, map_cons, sorted_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb ho hbo)
set_option linter.uppercaseLean3 false in
#align ordinal.CNF_sorted Ordinal.CNF_sorted

end Ordinal
