import Mathlib.Lean.Expr.Rat
import Mathlib.Tactic.NormNum.Result
import Mathlib.Util.Qq
import Lean.Elab.Tactic.Location
import Mathlib.Algebra.CharP.Defs

open Lean Qq

universe u

namespace Mathlib.Meta.NormNum

variable {p : ℕ} {u : Level}

lemma IsNat.modCharP {α : Type u} [AddMonoidWithOne α] [CharP α p] {e : α} {n n' : ℕ}
    (hn' : n % p = n')
    (H : IsNat e n) :
    IsNat e n' := by
  obtain ⟨rfl⟩ := H
  rw [← Nat.mod_add_div n p, Nat.cast_add, (CharP.cast_eq_zero_iff α p (p * _)).mpr ⟨_, rfl⟩]
  exact ⟨by simp [hn']⟩

lemma IsNegNat.modCharP {α : Type u} [Ring α] [CharP α p] {e : α} {n n' : ℕ}
    (hn' : (n + n') % p = 0)
    (H : IsInt e (-n)) :
    IsNat e n' := by
  obtain ⟨rfl⟩ := H
  rw [← Nat.dvd_iff_mod_eq_zero, ← CharP.cast_eq_zero_iff α, Nat.cast_add,
    add_eq_zero_iff_eq_neg] at hn'
  exact ⟨by simp [hn']⟩

def reduceCharP (p : ℕ) {α : Q(Type u)} (e : Q($α)) (res : Result e) : MetaM (Result e) := do
  match res with
  | .isBool _ _ => failure
  | .isNat _ lit proof =>
    let _ ← synthInstanceQ q(CharP $α $p)
    have n' : Q(ℕ) := mkRawNatLit (lit.natLit! % p)
    let pf_eq ← mkDecideProofQ q($lit % $p = $n')
    trace[Tactic.norm_num] m!"reduceCharP:\n{e} ==> {n'}"
    return .isNat _ n' q(IsNat.modCharP $pf_eq $proof)
  | .isNegNat _ lit proof =>
    let _ ← synthInstanceQ q(CharP $α $p)
    have n' : Q(ℕ) := mkRawNatLit ((p - lit.natLit! % p) % p)
    let pf_eq ← mkDecideProofQ q(($lit + $n') % $p = 0)
    trace[Tactic.norm_num] m!"reduceCharP:\n{e} ==> {n'}"
    return .isNat _ n' q(IsNegNat.modCharP $pf_eq $proof)
  | .isRat _ _ _ _ _ => failure

def tryReduceCharP (p : ℕ) {α : Q(Type u)} (e : Q($α)) (res : Result e) : MetaM (Result e) := do
  try
    reduceCharP p e res
  catch e =>
    trace[norm_num] m!"reduceCharP failed with error: {e.toMessageData}"
    return res

end Mathlib.Meta.NormNum
