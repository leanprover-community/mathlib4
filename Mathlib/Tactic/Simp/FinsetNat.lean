/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Util.Qq
import Mathlib.Tactic.NormNum.Basic

/-!
# Simproc for intervals of natural numbers
-/

open Qq Lean Mathlib.Meta.NormNum Finset

namespace Mathlib.Tactic.Simp

private lemma Icc_eq_insert_of_Icc_succ_eq {m n : ℕ} {s : Finset ℕ} (hmn : m ≤ n)
    (hs : Icc (m + 1) n = s) : Icc m n = insert m s := by
  rw [← hs, Nat.Icc_insert_succ_left hmn]

/-- Given natural numbers `m` and `n`, returns `(s, ⊢ Finset.Icc m n = s)`. -/
partial def evalFinsetIccNat {em eml en enl : Q(ℕ)} (hm : Q(IsNat $em $eml))
    (hn : Q(IsNat $en $enl)) : MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  let m := eml.natLit!
  let n := enl.natLit!
  if m ≤ n then
    let hmn ← mkDecideProofQq q($em ≤ $en)
    let hm := q(isNat_natSucc $hm rfl)
    let ⟨s, hs⟩ ← evalFinsetIccNat hm hn
    return ⟨q(insert $em $s), q(Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  else
    let hnm ← mkDecideProofQq q($en < $em)
    return ⟨q(∅), q(Finset.Icc_eq_empty_of_lt $hnm)⟩

scoped simproc finsetIcc_nat (Icc _ _) := fun e ↦ do
  let ⟨1, ~q(Finset ℕ), ~q(Icc (OfNat.ofNat $em) (OfNat.ofNat $en))⟩ ← inferTypeQ e
    | return .continue
  let hm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
  let hn : Q(IsNat (OfNat.ofNat $en) $en) := q(⟨rfl⟩)
  let ⟨s, p⟩ ← evalFinsetIccNat hm hn
  return .done { expr := s, proof? := p }

example : Icc 1 0 = ∅ := by simp [-Icc_eq_empty_of_lt, -Icc_eq_empty_iff]
-- TODO: The following time out
-- example : Icc 1 1 = {1} := by simp [-Icc_self]
-- example : Icc 1 2 = {1, 2} := by simp

end Mathlib.Tactic.Simp
