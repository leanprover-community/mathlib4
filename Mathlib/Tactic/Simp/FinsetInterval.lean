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
section lemmas
variable {m n : ℕ} {s : Finset ℕ}

private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m ≤ n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, Nat.Icc_insert_succ_left hmn]

private lemma Icc_of_eq (hmn : m = n) : Icc m n = {m} := by simp [hmn]

private lemma Ico_eq_of_Icc_pred_eq (hn : n ≠ 0) (hs : Icc m (n - 1) = s) : Ico m n = s := by
  rw [← hs, Nat.Icc_pred_right _ hn.bot_lt]

private lemma Ico_zero (m : ℕ) : Ico m 0 = ∅ := by simp

private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Nat.Icc_succ_left]

private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Nat.Icc_eq_Ioo]

end lemmas

/-- Given natural numbers `m` and `n`, returns `(s, ⊢ Finset.Icc m n = s)`. -/
partial def evalFinsetIccNat {em eml en enl : Q(ℕ)} (m n : ℕ) (hm : Q(IsNat $em $eml))
    (hn : Q(IsNat $en $enl)) : MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not synteq to `{m}`.
  if m = n then
    let hmn ← mkDecideProofQq q($em = $en)
    return ⟨q({$em}), q(Icc_of_eq $hmn)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn ← mkDecideProofQq q($em ≤ $en)
    let hm := q(isNat_natSucc $hm rfl)
    let ⟨s, hs⟩ ← evalFinsetIccNat (m+1) n hm hn
    return ⟨q(insert $em $s), q(Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm ← mkDecideProofQq q($en < $em)
    return ⟨q(∅), q(Finset.Icc_eq_empty_of_lt $hnm)⟩

end Mathlib.Tactic.Simp

open Mathlib.Tactic.Simp

namespace Finset

/-- Simproc to compute `Finset.Icc a b` when `a b : ℕ`. -/
simproc_decl Icc_nat (Icc _ _) := fun e ↦ do
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

/-- Simproc to compute `Finset.Ico a b` when `a b : ℕ`. -/
simproc_decl Ico_nat (Ico _ _) := fun e ↦ do
  let ⟨1, ~q(Finset ℕ), ~q(Ico (OfNat.ofNat $em) (OfNat.ofNat $en))⟩ ← inferTypeQ e
    | return .continue
  let hm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
  let hn : Q(IsNat (OfNat.ofNat $en) $en) := q(⟨rfl⟩)
  unless em.isRawNatLit && en.isRawNatLit do
    return .continue
  let m := em.natLit!
  let n := en.natLit!
  match n with
  | 0 =>
    return .done { expr := (q(∅) : Q(Finset ℕ)), proof? := q(Ico_zero $em) }
  | n + 1 =>
    let hn₀ ← mkDecideProofQq q($en ≠ 0)
    let hn := q(isNat_natPred $hn rfl)
    let ⟨s, p⟩ ← evalFinsetIccNat m n hm hn
    return .done { expr := s, proof? := q(Ico_eq_of_Icc_pred_eq $hn₀ $p) }

/-- Simproc to compute `Finset.Ioc a b` when `a b : ℕ`. -/
simproc_decl Ioc_nat (Ioc _ _) := fun e ↦ do
  let ⟨1, ~q(Finset ℕ), ~q(Ioc (OfNat.ofNat $em) (OfNat.ofNat $en))⟩ ← inferTypeQ e
    | return .continue
  let hm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
  let hn : Q(IsNat (OfNat.ofNat $en) $en) := q(⟨rfl⟩)
  unless em.isRawNatLit && en.isRawNatLit do
    return .continue
  let m := em.natLit!
  let n := en.natLit!
  let hm := q(isNat_natSucc $hm rfl)
  let ⟨s, p⟩ ← evalFinsetIccNat (m + 1) n hm hn
  return .done { expr := s, proof? := q(Ioc_eq_of_Icc_succ_eq $p) }

/-- Simproc to compute `Finset.Ioo a b` when `a b : ℕ`. -/
simproc_decl Ioo_nat (Ioo _ _) := fun e ↦ do
  let ⟨1, ~q(Finset ℕ), ~q(Ioo (OfNat.ofNat $em) (OfNat.ofNat $en))⟩ ← inferTypeQ e
    | return .continue
  let hm : Q(IsNat (OfNat.ofNat $em) $em) := q(⟨rfl⟩)
  let hn : Q(IsNat (OfNat.ofNat $en) $en) := q(⟨rfl⟩)
  unless em.isRawNatLit && en.isRawNatLit do
    return .continue
  let m := em.natLit!
  let n := en.natLit!
  let hm := q(isNat_natSucc $hm rfl)
  let hn := q(isNat_natPred $hn rfl)
  let ⟨s, p⟩ ← evalFinsetIccNat (m + 1) (n - 1) hm hn
  return .done { expr := s, proof? := q(Ioo_eq_of_Icc_succ_pred_eq $p) }

example : Icc 1 0 = ∅ := by simp only [Icc_nat]
example : Icc 1 1 = {1} := by simp only [Icc_nat]
example : Icc 1 2 = {1, 2} := by simp only [Icc_nat]

example : Ico 1 1 = ∅ := by simp only [Ico_nat]
example : Ico 1 2 = {1} := by simp only [Ico_nat]
example : Ico 1 3 = {1, 2} := by simp only [Ico_nat]

example : Ioc 1 1 = ∅ := by simp only [Ioc_nat]
example : Ioc 1 2 = {2} := by simp only [Ioc_nat]
example : Ioc 1 3 = {2, 3} := by simp only [Ioc_nat]

example : Ioo 1 2 = ∅ := by simp only [Ioo_nat]
example : Ioo 1 3 = {2} := by simp only [Ioo_nat]
example : Ioo 1 4 = {2, 3} := by simp only [Ioo_nat]

end Finset
