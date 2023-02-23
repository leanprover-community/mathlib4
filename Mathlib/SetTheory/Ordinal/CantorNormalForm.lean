/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.ordinal.cantor_normal_form
! leanprover-community/mathlib commit f1e061e3caef3022f0daa99d670ecf2c30e0b5c6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.SetTheory.Ordinal.Exponential

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
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

open Order

namespace Ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
noncomputable def cNFRec (b : Ordinal) {C : Ordinal → Sort _} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o
  | o =>
    if ho : o = 0 then by rwa [ho]
    else
      let hwf := mod_opow_log_lt_self b ho
      H o ho (CNF_rec (o % b ^ log b o))
#align ordinal.CNF_rec Ordinal.cNFRec

@[simp]
theorem cNFRec_zero {C : Ordinal → Sort _} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : @cNFRec b C H0 H 0 = H0 :=
  by
  rw [CNF_rec, dif_pos rfl]
  rfl
#align ordinal.CNF_rec_zero Ordinal.cNFRec_zero

theorem cNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort _} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    @cNFRec b C H0 H o = H o ho (@cNFRec b C H0 H _) := by rw [CNF_rec, dif_neg ho]
#align ordinal.CNF_rec_pos Ordinal.cNFRec_pos

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def cNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  cNFRec b [] (fun o ho IH => (log b o, o / b ^ log b o)::IH) o
#align ordinal.CNF Ordinal.cNF

@[simp]
theorem cNF_zero (b : Ordinal) : cNF b 0 = [] :=
  cNFRec_zero b _ _
#align ordinal.CNF_zero Ordinal.cNF_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursive definition for the Cantor normal form. -/
theorem cNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    cNF b o = (log b o, o / b ^ log b o)::cNF b (o % b ^ log b o) :=
  cNFRec_pos b ho _ _
#align ordinal.CNF_ne_zero Ordinal.cNF_ne_zero

theorem zero_cNF {o : Ordinal} (ho : o ≠ 0) : cNF 0 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
#align ordinal.zero_CNF Ordinal.zero_cNF

theorem one_cNF {o : Ordinal} (ho : o ≠ 0) : cNF 1 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
#align ordinal.one_CNF Ordinal.one_cNF

theorem cNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : cNF b o = [⟨0, o⟩] :=
  by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
  · exact one_CNF ho
#align ordinal.CNF_of_le_one Ordinal.cNF_of_le_one

theorem cNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : cNF b o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho, log_eq_zero hb]
#align ordinal.CNF_of_lt Ordinal.cNF_of_lt

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem cNF_foldr (b o : Ordinal) : (cNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  cNFRec b
    (by
      rw [CNF_zero]
      rfl)
    (fun o ho IH => by rw [CNF_ne_zero ho, List.foldr_cons, IH, div_add_mod]) o
#align ordinal.CNF_foldr Ordinal.cNF_foldr

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem cNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ cNF b o → x.1 ≤ log b o :=
  by
  refine' CNF_rec b _ (fun o ho H => _) o
  · rw [CNF_zero]
    exact False.elim
  · rw [CNF_ne_zero ho, List.mem_cons]
    rintro (rfl | h)
    · exact le_rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)
#align ordinal.CNF_fst_le_log Ordinal.cNF_fst_le_log

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem cNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ cNF b o) : x.1 ≤ o :=
  (cNF_fst_le_log h).trans <| log_le_self _ _
#align ordinal.CNF_fst_le Ordinal.cNF_fst_le

/-- Every coefficient in a Cantor normal form is positive. -/
theorem cNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ cNF b o → 0 < x.2 :=
  by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · rcases eq_zero_or_pos b with (rfl | hb)
    · rw [zero_CNF ho, List.mem_singleton]
      rintro rfl
      exact Ordinal.pos_iff_ne_zero.2 ho
    · rw [CNF_ne_zero ho]
      rintro (rfl | h)
      · simp
        rw [div_pos]
        · exact opow_log_le_self _ ho
        · exact (opow_pos _ hb).ne'
      · exact IH h
#align ordinal.CNF_lt_snd Ordinal.cNF_lt_snd

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem cNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ cNF b o → x.2 < b := by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · rw [CNF_ne_zero ho]
    rintro (rfl | h)
    · simpa using div_opow_log_lt o hb
    · exact IH h
#align ordinal.CNF_snd_lt Ordinal.cNF_snd_lt

/-- The exponents of the Cantor normal form are decreasing. -/
theorem cNF_sorted (b o : Ordinal) : ((cNF b o).map Prod.fst).Sorted (· > ·) :=
  by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · cases' le_or_lt b 1 with hb hb
    · simp [CNF_of_le_one hb ho]
    · cases' lt_or_le o b with hob hbo
      · simp [CNF_of_lt ho hob]
      · rw [CNF_ne_zero ho, List.map_cons, List.sorted_cons]
        refine' ⟨fun a H => _, IH⟩
        rw [List.mem_map'] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb ho hbo)
#align ordinal.CNF_sorted Ordinal.cNF_sorted

end Ordinal

