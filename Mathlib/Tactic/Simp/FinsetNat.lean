/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
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
partial def evalFinsetIccNat {em eml en enl : Q(ℕ)} (m n : ℕ) (hm : Q(IsNat $em $eml))
    (hn : Q(IsNat $en $enl)) : MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  if m ≤ n then
    let hmn ← mkDecideProofQq q($em ≤ $en)
    let hm' := q(isNat_natSucc $hm rfl)
    let ⟨s, hs⟩ ← evalFinsetIccNat (m+1) n hm' hn
    return ⟨q(insert $em $s), q(Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  else
    let hnm ← mkDecideProofQq q($en < $em)
    return ⟨q(∅), q(Finset.Icc_eq_empty_of_lt $hnm)⟩

simproc_decl finsetIcc_nat (Icc _ _) := fun e ↦ do
  let ⟨1, ~q(Finset ℕ), ~q(Icc (OfNat.ofNat $em) (OfNat.ofNat $en))⟩ ← inferTypeQ e
    | return .continue
  let hm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
  let hn : Q(IsNat (OfNat.ofNat $en) $en) := q(⟨rfl⟩)
  unless em.isRawNatLit && en.isRawNatLit do
    return .continue
  let m := em.natLit!
  let n := en.natLit!
  let ⟨s, p⟩ ← evalFinsetIccNat m n hm hn
  return .done { expr := s, proof? := p }

example : Icc 1 0 = ∅ := by simp [finsetIcc_nat, -Icc_eq_empty_of_lt, -Icc_eq_empty_iff]
example : Icc 1 1 = {1} := by simp [finsetIcc_nat, -Icc_self]
example : Icc 1 2 = {1, 2} := by simp [finsetIcc_nat]

end Mathlib.Tactic.Simp
