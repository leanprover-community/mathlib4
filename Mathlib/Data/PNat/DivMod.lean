/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.PNat.Defs

/-!
# Division and modulus for positive natural numbers

The positive remainder is always nonzero. When the natural remainder is zero,
`PNat.mod` returns the divisor and `PNat.div` returns the predecessor of the
natural quotient.
-/

@[expose] public section

namespace PNat

/-- Auxiliary function for positive remainder and quotient. -/
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | _, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩

/-- The positive remainder and quotient associated to two positive naturals. -/
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- Positive remainder, with zero remainders represented by the divisor. -/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1

/-- Quotient paired with `mod`, with exact divisions represented by the predecessor quotient. -/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2

theorem mod_coe (m k : ℕ+) :
    (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [ite_eq_left rfl]
    rfl
  | succ n =>
    rw [ite_eq_right n.succ_ne_zero]
    rfl

theorem div_coe (m k : ℕ+) :
    (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) := by
  dsimp [div, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [ite_eq_left rfl]
    rfl
  | succ n =>
    rw [ite_eq_right n.succ_ne_zero]
    rfl

/-- If `k ∣ m`, `divExact m k` is the usual positive quotient. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩

theorem modDivAux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (_ : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | _, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, _ => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | _, _ + 1, _, _ => rfl

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀

theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)

theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm ⊢
    simp
    lia
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩

end PNat
