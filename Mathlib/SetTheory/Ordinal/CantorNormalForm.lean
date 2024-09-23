/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

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
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNFRec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
theorem CNFRec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNFRec b H0 H 0 = H0 := by
  rw [CNFRec, dif_pos rfl]

theorem CNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNFRec b H0 H o = H o ho (@CNFRec b C H0 H _) := by
  rw [CNFRec, dif_neg]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNFRec b [] (fun o _ IH ↦ (log b o, o / b ^ log b o)::IH) o

/-- The exponents of the Cantor normal form are stored in the first entries. -/
def CNF.exponents (b o : Ordinal) := (CNF b o).map Prod.fst
/-- The coefficients of the Cantor normal form are stored in the second entries. -/
def CNF.coeffs (b o : Ordinal) := (CNF b o).map Prod.snd

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _

@[simp]
theorem CNF.exponents_zero (b : Ordinal) : CNF.exponents b 0 = [] := by
  rw [exponents, CNF_zero, map_nil]

theorem mem_CNF_exponents_iff {b o e : Ordinal} :
    e ∈ CNF.exponents b o ↔ ∃ c, (e, c) ∈ CNF b o := by
  simp [CNF.exponents]

theorem mem_CNF_exponents_of_mem {b o e c : Ordinal.{u}} (h : (e, c) ∈ CNF b o) :
    e ∈ CNF.exponents b o :=
  mem_CNF_exponents_iff.2 ⟨c, h⟩

@[simp]
theorem CNF.coeffs_zero (b : Ordinal) : CNF.coeffs b 0 = [] := by
  rw [coeffs, CNF_zero, map_nil]

theorem mem_CNF_coeffs_iff {b o c : Ordinal} :
    c ∈ CNF.coeffs b o ↔ ∃ e, (e, c) ∈ CNF b o := by
  simp [CNF.coeffs]

theorem mem_CNF_coeffs_of_mem {b o e c : Ordinal.{u}} (h : (e, c) ∈ CNF b o) :
    c ∈ CNF.coeffs b o :=
  mem_CNF_coeffs_iff.2 ⟨e, h⟩

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = ⟨log b o, o / b ^ log b o⟩::CNF b (o % b ^ log b o) :=
  CNFRec_pos b ho _ _

theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [(0, o)] := by simp [CNF_ne_zero ho]

theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [(0, o)] := by simp [CNF_ne_zero ho]

theorem CNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [(0, o)] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  exacts [zero_CNF ho, one_CNF ho]

theorem CNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [(0, o)] := by
  rw [CNF_ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, CNF_zero]

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero, foldr_nil]
  · intro o ho IH
    rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem le_log_of_mem_CNF_exponents {b o x : Ordinal} :
    x ∈ CNF.exponents b o → x ≤ log b o := by
  refine CNFRec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF.exponents, CNF_ne_zero ho, map_cons, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

@[deprecated le_log_of_mem_CNF_exponents (since := "2024-09-21")]
theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) :
    x.1 ≤ log b o :=
  le_log_of_mem_CNF_exponents (mem_CNF_exponents_of_mem h)

set_option linter.deprecated false in
/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
@[deprecated CNF_fst_le_log (since := "2024-09-21")]
theorem CNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) : x.1 ≤ o :=
  (CNF_fst_le_log h).trans <| log_le_self _ _

/-- Every coefficient in a Cantor normal form is positive. -/
theorem pos_of_mem_CNF_coeffs {b o : Ordinal.{u}} {x : Ordinal} :
    x ∈ CNF.coeffs b o → 0 < x := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF_ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

@[deprecated pos_of_mem_CNF_coeffs (since := "2024-09-21")]
theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) : 0 < x.2 :=
  pos_of_mem_CNF_coeffs (mem_CNF_coeffs_of_mem h)

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem lt_of_mem_CNF_coeffs {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal} :
    x ∈ CNF.coeffs b o → x < b := by
  refine CNFRec b ?_ (fun o ho IH h ↦ ?_) o
  · simp
  · rw [CNF.coeffs, CNF_ne_zero ho] at h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

@[deprecated lt_of_mem_CNF_coeffs (since := "2024-09-21")]
theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} (h : x ∈ CNF b o) :
    x.2 < b :=
  lt_of_mem_CNF_coeffs hb (mem_CNF_coeffs_of_mem h)

/-- The exponents of the `CNF` are a decreasing sequence. -/
theorem CNF_exponents_sorted (b o : Ordinal) : (CNF.exponents b o).Sorted (· > ·) := by
  rw [CNF.exponents]
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · rw [CNF_zero]
    exact sorted_nil
  · rcases le_or_lt b 1 with hb | hb
    · rw [CNF_of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_le o b
      · rw [CNF_of_lt ho hob]
        exact sorted_singleton _
      · rw [CNF_ne_zero ho, map_cons, sorted_cons]
        refine ⟨?_, IH⟩
        intro a H
        exact (le_log_of_mem_CNF_exponents H).trans_lt <| log_mod_opow_log_lt_log_self hb hbo

@[deprecated CNF_exponents_sorted (since := "2024-09-21")]
theorem CNF_sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) :=
  CNF_exponents_sorted b o

end Ordinal
