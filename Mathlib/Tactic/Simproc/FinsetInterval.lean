/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public meta import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public meta import Mathlib.Data.Nat.SuccPred
public meta import Mathlib.Data.Int.Interval
public meta import Mathlib.Data.Int.SuccPred
public meta import Mathlib.Order.Interval.Finset.Nat
public meta import Mathlib.Util.Qq

/-!
# Simproc for intervals of natural numbers
-/

public meta section

open Qq Lean Finset

namespace Mathlib.Tactic.Simp
namespace Nat
variable {m n : ℕ} {s : Finset ℕ}

private lemma Icc_eq_empty_of_lt (hnm : n.blt m) : Icc m n = ∅ := by simpa using hnm

private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m.ble n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

private lemma Ico_succ_eq_of_Icc_eq (hs : Icc m n = s) : Ico m (n + 1) = s := by
  rw [← hs, Ico_add_one_right_eq_Icc]

private lemma Ico_zero (m : ℕ) : Ico m 0 = ∅ := by simp

private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Icc_add_one_left_eq_Ioc]

private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Icc_add_one_sub_one_eq_Ioo]

private lemma Iic_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iic n = s := hs

private lemma Iio_succ_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iio (n + 1) = s := by
  rw [Iio_eq_Ico, Ico_add_one_right_eq_Icc, bot_eq_zero, hs]

private lemma Iio_zero : Iio 0 = ∅ := by simp

end Nat

namespace Int
variable {m n : ℤ} {s : Finset ℤ}

private lemma Icc_eq_empty_of_lt (hnm : n < m) : Icc m n = ∅ := by simpa using hnm

private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m ≤ n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

private lemma Ico_eq_of_Icc_pred_eq (hs : Icc m (n - 1) = s) : Ico m n = s := by
  rw [← hs, Icc_sub_one_right_eq_Ico]

private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Icc_add_one_left_eq_Ioc]

private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Icc_add_one_sub_one_eq_Ioo]

private lemma Iio_zero : Iio 0 = ∅ := by simp

end Int

/-- Given natural numbers `m` and `n` and corresponding natural literals `em` and `en`,
returns `(s, ⊢ Finset.Icc m n = s)`.

This cannot be easily merged with `evalFinsetIccInt` since they require different
handling of numerals for `ℕ` and `ℤ`. -/
def evalFinsetIccNat (m n : ℕ) (em en : Q(ℕ)) :
    MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
    have : $em =Q $en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc (m + 1) n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(ℕ) := mkNatLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Nat.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Nat.Icc_eq_empty_of_lt $hnm)⟩

/-- Given integers `m` and `n` and corresponding integer literals `em` and `en`,
returns `(s, ⊢ Finset.Icc m n = s)`.

This cannot be easily merged with `evalFinsetIccNat` since they require different
handling of numerals for `ℕ` and `ℤ`. -/
partial def evalFinsetIccInt (m n : ℤ) (em en : Q(ℤ)) :
    MetaM ((s : Q(Finset ℤ)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
    have : $em =Q $en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn ← mkDecideProofQ q($em ≤ $en)
    have em' : Q(ℤ) := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccInt (m + 1) n em' en
    return ⟨q(insert $em $s), q(Int.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm ← mkDecideProofQ q($en < $em)
    return ⟨q(∅), q(Icc_eq_empty_of_lt $hnm)⟩

end Mathlib.Tactic.Simp

open Mathlib.Tactic.Simp

/-!
Note that these simprocs are not made simp to avoid simp blowing up on goals containing things of
the form `Iic (2 ^ 1024)`.
-/
namespace Finset

/-- Simproc to compute `Finset.Icc a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Icc_ofNat_ofNat (Icc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Icc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat m n em en
    return .done <| .mk es <| .some p
  | 1, ~q(Finset ℤ), ~q(Icc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccInt m n em en
    return .done <| .mk es <| .some p
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ico a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ico_ofNat_ofNat (Ico _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ico $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
      have : $en =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Nat.Ico_zero $em)
    | n + 1 =>
      have en' := mkNatLitQ n
      have : $en =Q $en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat m n em en'
      return .done { expr := es, proof? := q(Nat.Ico_succ_eq_of_Icc_eq $p) }
  | 1, ~q(Finset ℤ), ~q(Ico $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have en' := mkIntLitQ (n - 1)
    have : $en' =Q $en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt m (n - 1) em en'
    return .done { expr := es, proof? := q(Int.Ico_eq_of_Icc_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioc a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioc_ofNat_ofNat (Ioc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    have em' := mkNatLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) n em' en
    return .done <| .mk es <| .some q(Nat.Ioc_eq_of_Icc_succ_eq $p)
  | 1, ~q(Finset ℤ), ~q(Ioc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) n em' en
    return .done { expr := es, proof? := q(Int.Ioc_eq_of_Icc_succ_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioo a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioo_ofNat_ofNat (Ioo _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioo $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) (n - 1) q($em + 1) q($en - 1)
    return .done <| .mk es <| .some q(Nat.Ioo_eq_of_Icc_succ_pred_eq $p)
  | 1, ~q(Finset ℤ), ~q(Ioo $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    have en' := mkIntLitQ (n - 1)
    have : $en' =Q $en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) (n - 1) em' en'
    return .done { expr := es, proof? := q(Int.Ioo_eq_of_Icc_succ_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iic b` where `b` is a numeral.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iic_ofNat (Iic _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iic $en) =>
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) en
    return .done <| .mk es <| .some q(Nat.Iic_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iio b` where `b` is a numeral.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iio_ofNat (Iio _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iio $en) =>
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
      have : $en =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Nat.Iio_zero)
    | n + 1 =>
      have en' := mkNatLitQ n
      have : $en =Q $en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) q($en')
      return .done  <| .mk es <| some q(Nat.Iio_succ_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

attribute [nolint unusedHavesSuffices]
  Iio_ofNat Ico_ofNat_ofNat Ioc_ofNat_ofNat Ioo_ofNat_ofNat

/-! ### `ℕ` -/

example : Icc 1 0 = ∅ := by simp only [Icc_ofNat_ofNat]
example : Icc 1 1 = {1} := by simp only [Icc_ofNat_ofNat]
example : Icc 1 2 = {1, 2} := by simp only [Icc_ofNat_ofNat]

example : Ico 1 1 = ∅ := by simp only [Ico_ofNat_ofNat]
example : Ico 1 2 = {1} := by simp only [Ico_ofNat_ofNat]
example : Ico 1 3 = {1, 2} := by simp only [Ico_ofNat_ofNat]

example : Ioc 1 1 = ∅ := by simp only [Ioc_ofNat_ofNat]
example : Ioc 1 2 = {2} := by simp only [Ioc_ofNat_ofNat]
example : Ioc 1 3 = {2, 3} := by simp only [Ioc_ofNat_ofNat]

example : Ioo 1 2 = ∅ := by simp only [Ioo_ofNat_ofNat]
example : Ioo 1 3 = {2} := by simp only [Ioo_ofNat_ofNat]
example : Ioo 1 4 = {2, 3} := by simp only [Ioo_ofNat_ofNat]

example : Iic 0 = {0} := by simp only [Iic_ofNat]
example : Iic 1 = {0, 1} := by simp only [Iic_ofNat]
example : Iic 2 = {0, 1, 2} := by simp only [Iic_ofNat]

example : Iio 0 = ∅ := by simp only [Iio_ofNat]
example : Iio 1 = {0} := by simp only [Iio_ofNat]
example : Iio 2 = {0, 1} := by simp only [Iio_ofNat]

/-! ### `ℤ` -/

example : Icc (1 : ℤ) 0 = ∅ := by simp only [Icc_ofNat_ofNat]
example : Icc (1 : ℤ) 1 = {1} := by simp only [Icc_ofNat_ofNat]
example : Icc (1 : ℤ) 2 = {1, 2} := by simp only [Icc_ofNat_ofNat]

example : Ico (1 : ℤ) 1 = ∅ := by simp only [Ico_ofNat_ofNat]
example : Ico (1 : ℤ) 2 = {1} := by simp only [Ico_ofNat_ofNat]
example : Ico (1 : ℤ) 3 = {1, 2} := by simp only [Ico_ofNat_ofNat]

example : Ioc (1 : ℤ) 1 = ∅ := by simp only [Ioc_ofNat_ofNat]
example : Ioc (1 : ℤ) 2 = {2} := by simp only [Ioc_ofNat_ofNat]
example : Ioc (1 : ℤ) 3 = {2, 3} := by simp only [Ioc_ofNat_ofNat]

example : Ioo (1 : ℤ) 2 = ∅ := by simp only [Ioo_ofNat_ofNat]
example : Ioo (1 : ℤ) 3 = {2} := by simp only [Ioo_ofNat_ofNat]
example : Ioo (1 : ℤ) 4 = {2, 3} := by simp only [Ioo_ofNat_ofNat]

end Finset
