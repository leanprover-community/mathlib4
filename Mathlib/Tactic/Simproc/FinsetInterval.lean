/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Util.Qq

/-!
# Simproc for intervals of natural numbers
-/

open Qq Lean Finset

namespace Mathlib.Tactic.Simp
section lemmas
variable {m n : ℕ} {s : Finset ℕ}

private lemma Icc_eq_empty_of_lt (hnm : n.blt m) : Icc m n = ∅ := by simpa using hnm

private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m.ble n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, Nat.Icc_insert_succ_left (by simpa using hmn)]

private lemma Ico_eq_of_Icc_pred_eq (hn : n ≠ 0) (hs : Icc m (n - 1) = s) : Ico m n = s := by
  rw [← hs, Icc_sub_one_right_eq_Ico_of_not_isMin (by simpa)]

private lemma Ico_zero (m : ℕ) : Ico m 0 = ∅ := by simp

private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Icc_add_one_left_eq_Ioc]

private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Icc_add_one_sub_one_eq_Ioo]

private lemma Iic_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iic n = s := hs

private lemma Iio_eq_of_Icc_zero_pred_eq (hn : n ≠ 0) (hs : Icc 0 (n - 1) = s) : Iio n = s :=
  Ico_eq_of_Icc_pred_eq hn hs

private lemma Iio_zero : Iio 0 = ∅ := by simp

end lemmas

/-- Given natural numbers `m` and `n`, returns `(s, ⊢ Finset.Icc m n = s)`. -/
def evalFinsetIccNat (m n : ℕ) (em en : Q(ℕ)) :
    MetaM ((s : Q(Finset ℕ)) × Q(.Icc (OfNat.ofNat $em) (OfNat.ofNat $en) = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
    have : $em =Q $en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(ℕ) := mkNatLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Icc_eq_empty_of_lt $hnm)⟩

end Mathlib.Tactic.Simp

open Mathlib.Tactic.Simp

/-!
Note that these simprocs are not made simp to avoid simp blowing up on goals containing things of
the form `Iic (2 ^ 1024)`.
-/
namespace Finset

/-- Simproc to compute `Finset.Icc a b` when `a b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Icc_nat (Icc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Icc (OfNat.ofNat $em) (OfNat.ofNat $en)) =>
    let some m := em.rawNatLit? | return .continue
    let some n := en.rawNatLit? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat m n em en
    return .done <| .mk es <| .some p
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ico a b` when `a b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ico_nat (Ico _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ico (OfNat.ofNat $em) (OfNat.ofNat $en)) =>
    let some m := em.rawNatLit? | return .continue
    let some n := en.rawNatLit? | return .continue
    match n with
    | 0 =>
      have : $en =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Ico_zero $em)
    | n + 1 =>
      let ⟨es, p⟩ ← evalFinsetIccNat m n em q($en - 1)
      return .done { expr := es, proof? := q(Ico_eq_of_Icc_pred_eq (Nat.succ_ne_zero _) $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioc a b` when `a b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioc_nat (Ioc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioc (OfNat.ofNat $em) (OfNat.ofNat $en)) =>
    let some m := em.rawNatLit? | return .continue
    let some n := en.rawNatLit? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) n q($em + 1) en
    return .done <| .mk es <| .some q(Ioc_eq_of_Icc_succ_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioo a b` when `a b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioo_nat (Ioo _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioo (OfNat.ofNat $em) (OfNat.ofNat $en)) =>
    let some m := em.rawNatLit? | return .continue
    let some n := en.rawNatLit? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) (n - 1) q($em + 1) q($en - 1)
    return .done <| .mk es <| .some q(Ioo_eq_of_Icc_succ_pred_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iic b` when `b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iic_nat (Iic _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iic (OfNat.ofNat $en)) =>
    let some n := en.rawNatLit? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) en
    return .done <| .mk es <| .some q(Iic_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iio b` when `b : ℕ`.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iio_nat (Iio _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iio (OfNat.ofNat $en)) =>
    let some n := en.rawNatLit? | return .continue
    match n with
    | 0 =>
      have : $en  =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Iio_zero)
    | n + 1 =>
      let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) q($en - 1)
      return .done { expr := es, proof? := q(Iio_eq_of_Icc_zero_pred_eq (Nat.succ_ne_zero _) $p) }
  | _, _, _ => return .continue

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

example : Iic 0 = {0} := by simp only [Iic_nat]
example : Iic 1 = {0, 1} := by simp only [Iic_nat]
example : Iic 2 = {0, 1, 2} := by simp only [Iic_nat]

example : Iio 0 = ∅ := by simp only [Iio_nat]
example : Iio 1 = {0} := by simp only [Iio_nat]
example : Iio 2 = {0, 1} := by simp only [Iio_nat]

end Finset
