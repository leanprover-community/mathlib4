/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
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

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open List

namespace Ordinal

/-! ### Cantor normal form as a list -/

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

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
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
theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNFRec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF_ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNFRec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF_ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF_ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) := by
  refine CNFRec b ?_ (fun o ho IH ↦ ?_) o
  · rw [CNF_zero]
    exact sorted_nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF_of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF_of_lt ho hob]
        exact sorted_singleton _
      · rw [CNF_ne_zero ho, map_cons, sorted_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

theorem CNF_nodupKeys (b o : Ordinal) : (CNF b o).NodupKeys :=
  (CNF_exponents_sorted b o).nodup

/-! ### Cantor normal form as a finsupp -/

open AList Finsupp

/-- `CNF_coeff b o` is the finitely supported function returning the coefficient of `b ^ e` in the
`CNF` of `o`, for each `e`. -/
@[pp_nodot]
def CNF_coeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  lookupFinsupp ⟨_, CNF_nodupKeys b o⟩

theorem CNF_coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    CNF_coeff b o e = c := by
  rw [CNF_coeff, lookupFinsupp_apply, mem_lookup_iff.2 h, Option.getD_some]

theorem CNF_coeff_of_not_mem_CNF {b o e : Ordinal} (h : e ∉ CNF.exponents b o) :
    CNF_coeff b o e = 0 := by
  rw [CNF_coeff, lookupFinsupp_apply, lookup_eq_none.2 h, Option.getD_none]

theorem CNF_coeff_zero_apply (b e : Ordinal) : CNF_coeff b 0 e = 0 := by
  apply CNF_coeff_of_not_mem_CNF
  rw [CNF.exponents_zero]
  exact not_mem_nil e

@[simp]
theorem CNF_coeff_zero (b : Ordinal) : CNF_coeff b 0 = 0 := by
  ext e
  exact CNF_coeff_zero_apply b e

theorem CNF_coeff_of_le_one {b : Ordinal} (hb : b ≤ 1) (o : Ordinal) :
    CNF_coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply CNF_coeff_of_mem_CNF
      rw [CNF_of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha.symm]
      apply CNF_coeff_of_not_mem_CNF
      rw [CNF.exponents, CNF_of_le_one hb ho]
      simpa using ha

@[simp]
theorem zero_CNF_coeff (o : Ordinal) : CNF_coeff 0 o = single 0 o :=
  CNF_coeff_of_le_one zero_le_one o

@[simp]
theorem one_CNF_coeff (o : Ordinal) : CNF_coeff 1 o = single 0 o :=
  CNF_coeff_of_le_one le_rfl o

end Ordinal
