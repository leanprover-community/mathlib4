/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Fermat Last Theorem in the case `n = 3`
The goal of this file is to prove Fermats Last theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree_case_1`: the first case of Fermat Last Theorem when `n = 3`:
  if `a b c : ℕ` are such that `¬ 3 ∣ a * b * c` then `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## TODO
Prove case 2.
-/

open ZMod

private lemma three_dvd_nine : 3 ∣ 9 := by norm_num

private lemma mem_of_castHom_ne_zero {a : ZMod 9} (ha : castHom three_dvd_nine (ZMod 3) a ≠ 0) :
    a ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9)) := by
  fin_cases a
  · aesop
  rotate_left 2
  · exfalso
    exact ha rfl
  rotate_left 2
  · exfalso
    exact ha rfl
  all_goals decide

private lemma mem_of_coe_ne_zero {a : ℕ} (ha : (a : ZMod 3) ≠ 0) :
    (a : ZMod 9) ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9)) :=
  mem_of_castHom_ne_zero (fun h ↦ ha <| by simpa using h)

private lemma biz {a : ZMod 9} (ha : a ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9))) :
    a ^ 3 ∈ ({1, 8} : Finset (ZMod 9)) := by
  fin_cases ha
  all_goals decide

private lemma fermatLastTheoremThree_ZMod9_case_1 {a b c : ZMod 9}
  (ha : a ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9)))
  (hb : b ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9)))
  (hc : c ∈ ({1, 2, 4, 5, 7, 8} : Finset (ZMod 9))) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have : Fact (1 < 9) := ⟨by norm_num⟩
  replace ha := biz ha; replace hb := biz hb; replace hc := biz hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with (ha | ha) <;> rcases hb with (hb | hb) <;> rcases hc with (hc | hc)
  all_goals simp only [ha, hb, hc]; decide

/--If `a b c : ℕ` are such that `¬ 3 ∣ a * b * c` then `a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
theorem fermatLastTheoremThree_case_1 :
    ∀ a b c : ℕ, ¬ 3 ∣ a * b * c → a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro a b c hdvd H
  have hA := mem_of_coe_ne_zero <|
    fun h ↦ hdvd <| (((nat_cast_zmod_eq_zero_iff_dvd _ _).1 h).mul_right b).mul_right c
  have hB := mem_of_coe_ne_zero <|
    fun h ↦ hdvd <| (((nat_cast_zmod_eq_zero_iff_dvd _ _).1 h).mul_left a).mul_right c
  have hC := mem_of_coe_ne_zero <|
    fun h ↦ hdvd <| mul_assoc a b c ▸ (((nat_cast_zmod_eq_zero_iff_dvd _ _).1 h).mul_left b).mul_left a
  exact fermatLastTheoremThree_ZMod9_case_1 hA hB hC
    (by convert congr_arg ((↑) : ℕ → ZMod 9) H using 1 <;> simp)
