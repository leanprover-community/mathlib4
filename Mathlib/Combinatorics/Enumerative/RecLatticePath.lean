/-
Copyright (c) 2025 YiranWang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Yiran
-/
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Monotone lattice paths and a ballot-style subdiagonal condition

This file defines and studies monotone lattice paths.  It introduces:
* `pathCount`, `pathCountFrom` and their closed forms,
* a Dyck/ballot-style subdiagonal condition on words (`SubdiagProp`) and the corresponding set.

## Main statements
* `pathCount_eq_closed : pathCount m n = (m + n).choose m`
* `pathCountFrom_eq_closed`
-/

open Nat
open Finset
open scoped BigOperators

universe u

/--
Number of monotone lattice paths from `(0, 0)` to `(m, n)` using only
right `(1, 0)` and up `(0, 1)` steps.
-/
def pathCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => pathCount (m + 1) n + pathCount m (n + 1)

/--
Closed form for `pathCount`: the number of lattice paths from `(0, 0)` to `(m, n)`
equals `(m + n).choose m`.
-/

theorem pathCount_eq_closed : ∀ m n, pathCount m n = (m + n).choose m := by
  intro m
  induction m with
  | zero =>
    intro n
    simp [pathCount, Nat.choose_zero_right]
  | succ m ih =>
    intro n
    induction n with
    | zero =>
      simp [pathCount]
    | succ n ih' =>
      simp only [pathCount]
      rw [ih', ih]
      have h : (m + 1 + (n + 1)) = (m + n + 2) := by ring
      rw [h]
      rw [Nat.choose_succ_succ, Nat.add_comm]
      congr! 1
      simp
      rw [Nat.add_right_comm]

/-- Diagonal specialization of `pathCount_eq_closed`. -/
lemma pathCount_eq_closed_n_n : ∀ n, pathCount n n = (2 * n).choose n := by
  intro n
  simpa [two_mul] using (pathCount_eq_closed n n)

/-- A step is either horizontal `H` or vertical `V` (encoded as `Bool`). -/
abbrev Step := Bool

/-- Horizontal step. -/
notation "H" => (false : Step)
/-- Vertical step. -/
notation "V" => (true  : Step)

/-- Number of vertical steps in a word. -/
def ups (l : List Step) : ℕ := l.count true

/--
`SubdiagProp n w` means that the word `w : Vector Step (2*n)` contains exactly `n`
vertical steps and, at every prefix, vertical steps never exceed half of the prefix length.
Equivalently, the Dyck/ballot-type subdiagonal condition.
-/
def SubdiagProp (n : ℕ) (w : Vector Step (2 * n)) : Prop :=
  (ups w.toList = n) ∧
  (∀ k : Fin (2 * n + 1), 2 * ups (w.toList.take (k : ℕ)) ≤ (k : ℕ))

/-- The set of length-`2n` words satisfying `SubdiagProp n`. -/
def SubdiagSet (n : ℕ) : Set (Vector Step (2 * n)) := {w | SubdiagProp n w}

/--
Cardinality of the subtype of words of length `2n` that satisfy `SubdiagProp n`.
-/
noncomputable def subdiagCount (n : ℕ) : ℕ :=
  Nat.card {w : Vector Step (2 * n) // SubdiagProp n w}

/-! # Paths from arbitrary start point to end point -/

/--
`pathCountFrom i j m n` is the number of monotone lattice paths from `(i, j)` to `(m, n)`.
If `i ≤ m` and `j ≤ n`, it reduces to `pathCount (m - i) (n - j)`, otherwise it is `0`.
-/
def pathCountFrom (i j m n : ℕ) : ℕ :=
  if _ : i ≤ m ∧ j ≤ n then
    pathCount (m - i) (n - j)
  else
    0

/-- Trivial case: the number of paths from a point to itself is `1`. -/
@[simp] lemma pathCountFrom_same (i j : ℕ) :
    pathCountFrom i j i j = 1 := by
  simp [pathCountFrom, pathCount]

/--
If `i ≤ m` fails, there is no monotone path from `(i, j)` to `(m, n)`.
-/
@[simp] lemma pathCountFrom_inaccess_left {i j m n : ℕ}
    (him : ¬ i ≤ m) :
    pathCountFrom i j m n = 0 := by
  have : ¬ (i ≤ m ∧ j ≤ n) := by
    intro h; exact him h.left
  simp [pathCountFrom, this]

/--
If `j ≤ n` fails, there is no monotone path from `(i, j)` to `(m, n)`.
-/
@[simp] lemma pathCountFrom_inaccess_down {i j m n : ℕ}
    (hjn : ¬ j ≤ n) :
    pathCountFrom i j m n = 0 := by
  have : ¬ (i ≤ m ∧ j ≤ n) := by
    intro h; exact hjn h.right
  simp [pathCountFrom, this]

/--
Closed form for `pathCountFrom`: assuming reachability (`i ≤ m` and `j ≤ n`),
the number of monotone lattice paths from `(i, j)` to `(m, n)` equals
`((m - i) + (n - j)).choose (m - i)`.
-/
theorem pathCountFrom_eq_closed {i j m n : ℕ}
    (hi : i ≤ m) (hj : j ≤ n) :
    pathCountFrom i j m n = ((m - i) + (n - j)).choose (m - i) := by
  have h : i ≤ m ∧ j ≤ n := ⟨hi, hj⟩
  simp [pathCountFrom, h, pathCount_eq_closed]

/--
`pathCountFrom` as a `dite`d closed form: returns the binomial coefficient when
reachable; otherwise `0`.
-/
theorem pathCountFrom_eq_dite (i j m n : ℕ) :
    pathCountFrom i j m n
      = (if _ : i ≤ m ∧ j ≤ n
         then ((m - i) + (n - j)).choose (m - i)
         else 0) := by
  by_cases h : i ≤ m ∧ j ≤ n
  · rcases h with ⟨hi, hj⟩
    simp [pathCountFrom, hi, hj, pathCount_eq_closed]
  · simp [pathCountFrom, h]
