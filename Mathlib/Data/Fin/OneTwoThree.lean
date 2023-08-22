import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

namespace Fin

instance Zero.of_lt (n : ℕ) [Fact $ 0 < n] : Zero (Fin n) :=
⟨0, Fact.out⟩

instance (n : ℕ) [Fact $ 2 ≤ n] : Fact $ 0 ≤ n := ⟨by linarith [(Fact.out : 2 ≤ n)]⟩

instance One.of_le (n : ℕ) [Fact $ 2 ≤ n] : One (Fin n) :=
⟨1, by linarith [(Fact.out : 2 ≤ n)]⟩

lemma coe_one_eq_of_le (n : ℕ) [Fact $ 2 ≤ n] : ((1 : Fin n) : ℕ) = 1 := rfl

lemma one_pos_of_le (n : ℕ) [Fact $ 2 ≤ n] : (0 : Fin n) < (1 : Fin n) :=
show 0 < _ by { rw [one_val_eq_of_le n]; exact nat.zero_lt_one }

lemma two_val_eq_of_le (n : ℕ) [Fact $ 3 ≤ n] : (2 : Fin n).val = 2 :=
begin
  haveI : Fact (2 ≤ n) := ⟨by linarith [show 3 ≤ n, from Fact.out _]⟩,
  rw [show (bit0 1 : Fin n) = 2, from rfl, val_eq_coe, Fin.coe_bit0, coe_one_eq_of_le],
  reFine nat.mod_eq_of_lt (by linarith [show 3 ≤ n, from Fact.out _]),
end

lemma coe_two_eq_of_le (n : ℕ) [Fact $ 3 ≤ n] : (2 : Fin n).val = 2 :=
two_val_eq_of_le n

end Fin
