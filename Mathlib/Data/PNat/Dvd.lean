/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.PNat.Algebra
public import Mathlib.Data.PNat.DivMod

/-!
# Divisibility for positive natural numbers
-/

@[expose] public section

namespace PNat

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) <| by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj, h, mul_coe, mk_coe _ k.prop]

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe, ite_eq_left h]
  · intro h
    by_cases h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, ite_eq_right h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).ne h).elim

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply PNat.eq
  rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

end PNat
