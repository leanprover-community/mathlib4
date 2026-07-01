/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# Computable univariate polynomials (`SparsePoly`)

A computational representation of univariate polynomials over a commutative ring `R` with
`DecidableEq R`. A `SparsePoly R` is stored as a list of `(exponent, coefficient)` pairs in `ℕ × R`
with the exponents in strictly decreasing order and all coefficients nonzero (so the zero polynomial
is the empty list). This invariant makes the representation canonical.

This provides kernel-reducible, `#eval`-able polynomial arithmetic that mirrors Mathlib's
noncomputable `Polynomial R`. It is the computational backend for the reflection tactics
(`poly_decide`, `poly_eval`, `poly_dvd`), which prove statements about `Polynomial R` by reflecting
onto `SparsePoly R`.

## Implementation notes

`DecidableEq R` is required so that zero coefficients can be recognised and dropped, keeping the
list canonical (hence equality of `SparsePoly R` is decidable by structural comparison).

J. Davenport notes that Lean permits the trivial ring (in which `0 = 1`); supporting it here costs
extra case analysis, and one may wish to rethink whether to allow it.

## Provenance

Started by Mario Carneiro at the Hausdorff Institute, June 2024, with design notes by
James Davenport; the multivariate analogue (`MvSparsePoly`) and the reflection tactics were
developed subsequently.
-/

/-- A computable univariate polynomial over `R`, stored as a list of `(exponent, coefficient)`
pairs with exponents in strictly decreasing order and all coefficients nonzero (so the zero
polynomial is `[]`). These invariants make the representation canonical. -/
@[ext] structure SparsePoly (R : Type) [CommRing R] : Type where
  /-- The underlying list of `(exponent, coefficient)` pairs, ordered by strictly decreasing
  exponent with all coefficients nonzero. -/
  coeffs : List (ℕ × R)
  sorted : coeffs.Pairwise (·.1 > ·.1)
  nonzero : ∀ x ∈ coeffs, x.2 ≠ 0

namespace SparsePoly
open Polynomial

variable {R}

instance [CommRing R] [Lean.ToFormat R] : Lean.ToFormat (SparsePoly R) where
  format x :=
    have := x.coeffs.foldl (init := none) fun (f : Option Lean.Format) (i, x) =>
      let monomial := if i = 0 then f!"({x})" else if i = 1 then f!"({x})*X" else f!"({x})*X^{i}"
      match f with
      | none => monomial
      | some f => f ++ " + " ++ monomial
    this.getD f!"0"

variable [CommRing R] [DecidableEq R]
/-- Builds a `SparsePoly R` from a list already sorted by strictly decreasing exponent, dropping
any pairs with zero coefficient to restore the canonical invariant. -/
def ofSortedList
    (coeffs : List (ℕ × R)) (sorted : coeffs.Pairwise (·.1 > ·.1)) :
    SparsePoly R where
  coeffs := coeffs.filter (·.2 ≠ 0)
  sorted := sorted.sublist (List.filter_sublist)
  nonzero := by simp [List.mem_filter]

theorem ofSortedList_of_nonzero {R : Type} [CommRing R] [DecidableEq R]
    (coeffs : List (ℕ × R)) (nonzero : ∀ x ∈ coeffs, x.2 ≠ 0) (sorted) :
    (ofSortedList coeffs sorted).coeffs = coeffs := by
  simp (config := {contextual := true}) [ofSortedList, nonzero]

instance : Zero (SparsePoly R) where
  zero := { coeffs := [], sorted := .nil, nonzero := nofun }

/-- The constant polynomial. `ofSortedList` drops the term when `r = 0`. -/
def C (r : R) : SparsePoly R := ofSortedList [(0, r)] (List.pairwise_singleton _ _)

instance : One (SparsePoly R) where
  one := C 1

/-- `degLt a l` holds when every pair in `l` has exponent strictly less than `a`. -/
def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

/-- Interprets a list of `(exponent, coefficient)` pairs as the Mathlib polynomial
`∑ Polynomial.C a * Polynomial.X ^ i`. -/
noncomputable def toPolyCore : List (ℕ × R) → R[X]
  | [] => 0
  | (i, a) :: x => Polynomial.C a * Polynomial.X^i + toPolyCore x

/-- The Mathlib `Polynomial R` represented by a `SparsePoly R`. -/
noncomputable def toPoly (x : SparsePoly R) : Polynomial R :=
  toPolyCore x.coeffs

/-- Adds two exponent-sorted coefficient lists by merging on exponent, summing coefficients on
matching exponents and dropping any term whose sum is zero. -/
def addCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], yy => yy
  | xx, [] => xx
  | xx@((i, a) :: x), yy@((j, b) :: y) =>
    if i < j then
      (j, b) :: addCore xx y
    else if j < i then
      (i, a) :: addCore x yy
    else
      ( fun c => if c=0 then addCore x y else (i, c) :: addCore x y) (a+b)
    termination_by xx yy => xx.length + yy.length

theorem addCore_degLt {n : ℕ} : ∀ {x y : List (ℕ × R)},
    degLt n x → degLt n y → degLt n (addCore x y)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    have hx_head : i < n := hx (i, a) List.mem_cons_self
    have hx_tail : degLt n x := fun e he => hx e (List.mem_cons_of_mem _ he)
    have hy_head : j < n := hy (j, b) List.mem_cons_self
    have hy_tail : degLt n y := fun e he => hy e (List.mem_cons_of_mem _ he)
    unfold addCore
    split
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hy_head
      · exact addCore_degLt hx hy_tail e he
    · split
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hx_head
        · exact addCore_degLt hx_tail hy e he
      · dsimp only
        split
        · exact addCore_degLt hx_tail hy_tail
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hx_head
          · exact addCore_degLt hx_tail hy_tail e he
termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (ℕ × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1)
  | [], yy, _, hy => by
    unfold addCore
    exact hy
  | (i, a) :: x, [], hx, _ => by
    unfold addCore
    exact hx
  | xx@((i, a) :: x), yy@((j, b) :: y), hx, hy => by
    have ⟨hi, hx'⟩ := List.pairwise_cons.1 hx
    have ⟨hj, hy'⟩ := List.pairwise_cons.1 hy
    unfold addCore
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    · split
      · next ji =>
        constructor
        · apply addCore_degLt
          · exact hi
          · intro
            | _, .head _ => exact ji
            | p, .tail _ hp => exact (hj _ hp).trans ji
        · exact addCore_sorted hx' hy
      · cases (by omega : i = j)
        dsimp only
        split
        · exact addCore_sorted hx' hy'
        · constructor
          · exact addCore_degLt hi hj
          · exact addCore_sorted hx' hy'
termination_by x y => x.length + y.length

instance : Add (SparsePoly R) where
  add x y :=
    let coeffs := addCore x.coeffs y.coeffs
    ofSortedList coeffs (addCore_sorted x.sorted y.sorted)

/-- Collapses adjacent entries with equal exponents in a list by summing their coefficients,
turning a list sorted by nonincreasing exponents into one with distinct exponents. -/
def dedupList : List (ℕ × R) → List (ℕ × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

omit [DecidableEq R] in
lemma dedupList_degLt {n : ℕ} : ∀ (l : List (ℕ × R)),
    degLt n l → degLt n (dedupList l)
  | [] => fun h => by
    unfold dedupList
    exact h
  | [(i, a)] => fun h => by
    unfold dedupList
    exact h
  | (i, a) :: (j, b) :: xs => fun h => by
    unfold dedupList
    split
    · apply dedupList_degLt
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h (i, a) List.mem_cons_self
      · exact h e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h (i, a) List.mem_cons_self
      · have h_tail : degLt n ((j, b) :: xs) := fun x hx => h x (List.mem_cons_of_mem _ hx)
        exact dedupList_degLt ((j, b) :: xs) h_tail e he
termination_by l => l.length

omit [DecidableEq R] in
theorem dedupList_sorted : ∀ (coeffs : List (ℕ × R)),
    coeffs.Pairwise (·.1 ≥ ·.1) →
    (dedupList coeffs).Pairwise (·.1 > ·.1)
  | [] => fun _ => by
    unfold dedupList
    exact List.Pairwise.nil
  | [(i, a)] => fun _ => by
    unfold dedupList
    rw [List.pairwise_cons]
    exact ⟨fun e he => by contradiction, List.Pairwise.nil⟩
  | (i, a) :: (j, b) :: xs => fun h => by
    have h_ij : i ≥ j := (List.pairwise_cons.1 h).1 (j, b) List.mem_cons_self
    have h_tail : ((j, b) :: xs).Pairwise (·.1 ≥ ·.1) := (List.pairwise_cons.1 h).2
    unfold dedupList
    split
    · apply dedupList_sorted
      rw [List.pairwise_cons]
      refine ⟨fun e he => ?_, (List.pairwise_cons.1 h_tail).2⟩
      have h_je : j ≥ e.1 := (List.pairwise_cons.1 h_tail).1 e he
      omega
    · next hneq =>
      have hij_strict : i > j := by omega
      rw [List.pairwise_cons]
      refine ⟨?_, dedupList_sorted ((j, b) :: xs) h_tail⟩
      apply dedupList_degLt
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hij_strict
      · have h_je : j ≥ e.1 := (List.pairwise_cons.1 h_tail).1 e he
        omega
termination_by coeffs => coeffs.length

/-- Builds a `SparsePoly R` from an arbitrary list of `(exponent, coefficient)` pairs by sorting on
exponent, merging duplicate exponents, and dropping zero coefficients. -/
def ofList (coeffs : List (ℕ × R)) : SparsePoly R :=
  let r : ℕ × R → ℕ × R → Bool := fun a b => decide (a.1 ≥ b.1)
  let coeffs' := coeffs.mergeSort r
  have h_trans : ∀ a b c, r a b = true → r b c = true → r a c = true := by
    intro a b c hab hbc
    simp only [r, decide_eq_true_eq] at *
    omega
  have h_total : ∀ a b, (r a b || r b a) = true := by
    intro a b
    simp only [r, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have h_sorted_bool : coeffs'.Pairwise (fun a b => r a b = true) :=
    List.pairwise_mergeSort h_trans h_total coeffs
  have h_sorted : coeffs'.Pairwise (·.1 ≥ ·.1) :=
    List.Pairwise.imp (fun h => of_decide_eq_true h) h_sorted_bool
  ofSortedList (dedupList coeffs')
    (dedupList_sorted coeffs' h_sorted)

/-- The indeterminate `X`, i.e. the monomial `X^1` with coefficient `1`. -/
def X : SparsePoly R := ofSortedList [(1, 1)] (List.pairwise_singleton _ _)

instance : Mul (SparsePoly R) where
  mul x y :=
    ofList do
      let (i, a) ← x.coeffs
      let (j, b) ← y.coeffs
      return (i + j, a * b)

instance : Neg (SparsePoly R) where
  neg x := C (-1) * x

/-- Filtering out zero coefficients doesn't change the underlying polynomial,
since `C 0 * X^i = 0`. -/
theorem toPolyCore_filter_nonzero (l : List (ℕ × R)) :
    toPolyCore (l.filter (·.2 ≠ 0)) = toPolyCore l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    simp only [List.filter_cons]
    split
    · rw [toPolyCore, toPolyCore, ih]
    · unfold toPolyCore
      aesop

theorem toPolyCore_addCore : ∀ (x y : List (ℕ × R)),
    toPolyCore (addCore x y) = toPolyCore x + toPolyCore y
  | [], yy => by simp [addCore, toPolyCore]
  | (i, a) :: x, [] => by simp [addCore, toPolyCore]
  | xx@((i, a) :: x), yy@((j, b) :: y) => by
    unfold addCore
    split
    · dsimp only [toPolyCore]
      rw [toPolyCore_addCore ((i, a) :: x) y]
      dsimp only [toPolyCore]
      ring
    · split
      · dsimp only [toPolyCore]
        rw [toPolyCore_addCore x ((j, b) :: y)]
        dsimp only [toPolyCore]
        ring
      · cases (by omega : i = j)
        dsimp only
        split
        · next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore x y]
          have h_zero : Polynomial.C a * Polynomial.X ^ i +
              Polynomial.C b * Polynomial.X ^ i = 0 := by
            rw [← add_mul, ← map_add, hab, map_zero, zero_mul]
          rw [show Polynomial.C a * Polynomial.X ^ i + toPolyCore x +
            (Polynomial.C b * Polynomial.X ^ i + toPolyCore y) =
            (Polynomial.C a * Polynomial.X ^ i + Polynomial.C b * Polynomial.X ^ i) +
            (toPolyCore x + toPolyCore y) by ring, h_zero, zero_add]
        · dsimp only [toPolyCore]
          rw [toPolyCore_addCore x y, map_add, add_mul]
          ring
termination_by x y => x.length + y.length

/-- `SparsePoly` addition mirrors `Polynomial` addition. -/
theorem toPoly_add (x y : SparsePoly R) :
    toPoly (x + y) = toPoly x + toPoly y := by
  change toPolyCore ((addCore x.coeffs y.coeffs).filter (·.2 ≠ 0)) = _
  rw [toPolyCore_filter_nonzero]
  exact toPolyCore_addCore x.coeffs y.coeffs

omit [CommRing R] [DecidableEq R] in
lemma degLt_of_sorted_cons {i : ℕ} {a : R} {xs : List (ℕ × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

omit [DecidableEq R] in
theorem coeff_toPolyCore_of_degLt {n : ℕ} (xs : List (ℕ × R)) (h : degLt n xs) :
    Polynomial.coeff (toPolyCore xs) n = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [Polynomial.coeff_add]
    have h_deg : i < n := h (i, a) List.mem_cons_self
    have h_ne : i ≠ n := ne_of_lt h_deg
    rw [Polynomial.coeff_C_mul_X_pow]
    have h_tl : degLt n tl := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [ih h_tl, add_zero]
    grind

omit [DecidableEq R] in
theorem coeff_toPolyCore_head {i : ℕ} {a : R} (xs : List (ℕ × R)) (h : degLt i xs) :
    Polynomial.coeff (toPolyCore ((i, a) :: xs)) i = a := by
  dsimp only [toPolyCore]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  rw [coeff_toPolyCore_of_degLt xs h, add_zero]

omit [DecidableEq R] in
theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (ℕ × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff := congrArg (Polynomial.coeff · j) heq
    change (0 : Polynomial R).coeff j = _ at h_coeff
    rw [Polynomial.coeff_zero] at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff := congrArg (Polynomial.coeff · i) heq
    change _ = (0 : Polynomial R).coeff i at h_coeff
    rw [Polynomial.coeff_zero] at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff := congrArg (Polynomial.coeff · j) heq
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      have h_xs_j : degLt j xs := fun e he => lt_trans (h_deg_x e he) hij
      have h_lhs : Polynomial.coeff (toPolyCore ((i, a) :: xs)) j = 0 := by
        dsimp only [toPolyCore]
        rw [Polynomial.coeff_add]
        have hne : i ≠ j := ne_of_lt hij
        rw [Polynomial.coeff_C_mul_X_pow]
        rw [coeff_toPolyCore_of_degLt xs h_xs_j]
        grind
      rw [h_lhs] at h_coeff
      have hb_nz := nz2 (j, b) List.mem_cons_self
      exact False.elim (hb_nz h_coeff.symm)
    · have h_coeff := congrArg (Polynomial.coeff · i) heq
      rw [coeff_toPolyCore_head xs h_deg_x, coeff_toPolyCore_head ys h_deg_y] at h_coeff
      subst h_coeff
      dsimp only [toPolyCore] at heq
      have heq_xs_ys : toPolyCore xs = toPolyCore ys := add_left_cancel heq
      have s1_xs : xs.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s1).2
      have s2_ys : ys.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s2).2
      have nz1_xs : ∀ x ∈ xs, x.2 ≠ 0 := fun e he => nz1 e (List.mem_cons_of_mem _ he)
      have nz2_ys : ∀ x ∈ ys, x.2 ≠ 0 := fun e he => nz2 e (List.mem_cons_of_mem _ he)
      rw [toPolyCore_injective_of_sorted xs ys s1_xs s2_ys nz1_xs nz2_ys heq_xs_ys]
    · have h_coeff := congrArg (Polynomial.coeff · i) heq
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      have h_ys_i : degLt i ys := fun e he => lt_trans (h_deg_y e he) hji
      have h_rhs : Polynomial.coeff (toPolyCore ((j, b) :: ys)) i = 0 := by
        dsimp only [toPolyCore]
        rw [Polynomial.coeff_add]
        have hne : j ≠ i := ne_of_lt hji
        rw [Polynomial.coeff_C_mul_X_pow]
        rw [coeff_toPolyCore_of_degLt ys h_ys_i]
        grind
      rw [h_rhs] at h_coeff
      have ha_nz := nz1 (i, a) List.mem_cons_self
      exact False.elim (ha_nz h_coeff)

omit [DecidableEq R] in
theorem toPoly_injective : Function.Injective (toPoly (R := R)) := by
  intro x y h
  ext1
  exact toPolyCore_injective_of_sorted x.coeffs y.coeffs x.sorted y.sorted x.nonzero y.nonzero h

omit [DecidableEq R] in
/-- `toPoly` of the zero `SparsePoly` is the zero `Polynomial`. -/
theorem toPoly_zero : toPoly (0 : SparsePoly R) = 0 := rfl

/-- `toPoly` of a constant `SparsePoly` is the constant `Polynomial`. -/
theorem toPoly_C (r : R) : toPoly (C r) = Polynomial.C r := by
  unfold C toPoly ofSortedList
  dsimp only
  by_cases hr : r = 0 <;> simp [hr, toPolyCore]

omit [DecidableEq R] in
theorem toPolyCore_append (l1 l2 : List (ℕ × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    calc
      toPolyCore ((i, a) :: tl ++ l2)
          = Polynomial.C a * Polynomial.X ^ i + toPolyCore (tl ++ l2) := by
              simp [List.cons_append, toPolyCore]
      _ = Polynomial.C a * Polynomial.X ^ i + (toPolyCore tl + toPolyCore l2) := by
            rw [ih]
      _ = toPolyCore ((i, a) :: tl) + toPolyCore l2 := by
            simp [toPolyCore, add_assoc]

omit [DecidableEq R] in
theorem toPolyCore_perm {l1 l2 : List (ℕ × R)} (h : List.Perm l1 l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rcases x with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [ih]
  | swap x y l =>
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    dsimp only [toPolyCore]
    ring
  | trans _ _ ih1 ih2 =>
    exact Eq.trans ih1 ih2

omit [DecidableEq R] in
theorem toPolyCore_mergeSort (l : List (ℕ × R)) (r : ℕ × R → ℕ × R → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (List.mergeSort_perm l r)

omit [DecidableEq R] in
theorem toPolyCore_dedupList : ∀ (l : List (ℕ × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by
    simp [dedupList, toPolyCore]
  | [(i, a)] => by
    simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
    unfold dedupList
    split
    · next heq =>
      subst heq
      rw [toPolyCore_dedupList ((i, a + b) :: xs)]
      dsimp only [toPolyCore]
      rw [map_add, add_mul]
      ring
    · dsimp only [toPolyCore]
      rw [toPolyCore_dedupList ((j, b) :: xs)]
      simp [toPolyCore]

theorem toPoly_ofList (l : List (ℕ × R)) :
    toPoly (ofList l) = toPolyCore l := by
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
lemma toPolyCore_mul_y (i : ℕ) (a : R) (y : List (ℕ × R)) :
    toPolyCore (y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
      (Polynomial.C a * Polynomial.X ^ i) * toPolyCore y := by
  induction y with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    change toPolyCore ([(i + j, a * b)] ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih]
    dsimp only [toPolyCore]
    rw [show Polynomial.C (a * b) * Polynomial.X ^ (i + j) =
        Polynomial.C a * Polynomial.X ^ i * (Polynomial.C b * Polynomial.X ^ j) by
      rw [map_mul, pow_add]; ring]
    ring

omit [DecidableEq R] in
lemma toPolyCore_mul_x (x y : List (ℕ × R)) :
    toPolyCore (x.flatMap fun ⟨i, a⟩ => y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
    toPolyCore x * toPolyCore y := by
  induction x with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    change toPolyCore ((y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih, toPolyCore_mul_y]
    dsimp only [toPolyCore]
    ring

theorem toPoly_one : toPoly (1 : SparsePoly R) = 1 := by
  change toPoly (C 1) = 1
  rw [toPoly_C]
  exact map_one (Polynomial.C (R := R))

theorem toPoly_mul (x y : SparsePoly R) : toPoly (x * y) = toPoly x * toPoly y := by
  rw [show x * y = ofList (x.coeffs.flatMap fun ⟨i, a⟩ =>
    y.coeffs.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) from rfl, toPoly_ofList]
  exact toPolyCore_mul_x x.coeffs y.coeffs

theorem toPoly_neg (x : SparsePoly R) : toPoly (-x) = -toPoly x := by
  change toPoly (C (-1) * x) = -toPoly x
  rw [toPoly_mul, toPoly_C]
  simp

instance : CommRing (SparsePoly R) where
  add := (·+·)
  zero := 0
  mul := (·*·)
  one := 1
  neg := (-·)
  sub x y := x + -y
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  natCast n := C (n : R)
  intCast z := C (z : R)

  add_assoc := by
    intro x y z
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, toPoly_add, toPoly_add]
    exact add_assoc (toPoly x) (toPoly y) (toPoly z)
  zero_add := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, zero_add]

  add_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, add_zero]

  add_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, add_comm]

  neg_add_cancel := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_neg, toPoly_zero, neg_add_cancel]

  mul_assoc := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, toPoly_mul, toPoly_mul, mul_assoc]

  one_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, one_mul]

  mul_one := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, mul_one]

  left_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, left_distrib]

  right_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, right_distrib]

  zero_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero, zero_mul]

  mul_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero,  mul_zero]

  mul_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, mul_comm]

  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  natCast_zero := by
    apply toPoly_injective
    rw [toPoly_C, toPoly_zero]
    push_cast
    exact map_zero Polynomial.C

  natCast_succ := by
    intro n
    apply toPoly_injective
    show toPoly (C ((n + 1 : ℕ) : R)) = toPoly (C (n : R) + 1)
    rw [toPoly_C, toPoly_add, toPoly_C, toPoly_one]
    push_cast
    grind

  intCast_ofNat := by
    intro n
    apply toPoly_injective
    change toPoly (C ((Int.ofNat n : ℤ) : R)) = toPoly (C (n : R))
    rw [toPoly_C, toPoly_C]
    aesop

  intCast_negSucc := by
    intro n
    apply toPoly_injective
    change toPoly (C _) = toPoly (- C _)
    rw [toPoly_C, toPoly_neg, toPoly_C]
    push_cast
    grind

/-- The ring homomorphism `R →+* SparsePoly R` sending `r` to the constant polynomial `C r`. -/
def CHom : R →+* SparsePoly R where
  toFun := C
  map_zero' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_zero, map_zero]
  map_one' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_one, map_one]
  map_add' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_add, toPoly_C, map_add]
  map_mul' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_mul, toPoly_C, map_mul]

instance : Algebra R (SparsePoly R) where
  smul := fun a r => C a * r
  algebraMap := CHom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl

/-- A typeclass asserting that division `/` is exact on divisibility: whenever `b ∣ a`, one has
`b * (a / b) = a`. This holds for `ℤ` (Euclidean division) and for fields. -/
class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

/-- The degree of a `SparsePoly R`, i.e. the exponent of its leading (head) term, or `0` for the
zero polynomial. -/
def degree (a : SparsePoly R) : ℕ := (a.coeffs.headD (0, 0)).1

omit [DecidableEq R] in
lemma degree_eq_head (p : SparsePoly R) (i : ℕ) (x : R) (tail : List (ℕ × R))
    (h : p.coeffs = (i, x) :: tail) : p.degree = i := by
  rw [degree, h]
  simp

omit [DecidableEq R] in
lemma natDegree_toPolyCore_lt (i : ℕ) (x : R) (tail : List (ℕ × R))
    (h_sorted : ((i, x) :: tail).Pairwise (·.1 > ·.1)) :
    (toPolyCore tail).natDegree < i ∨ toPolyCore tail = 0 := by
  by_cases h0 : toPolyCore tail = 0
  · exact Or.inr h0
  · refine Or.inl (lt_of_not_ge fun hge => h0 ?_)
    have h_degLt_nd : degLt (toPolyCore tail).natDegree tail :=
      fun p hp => lt_of_lt_of_le ((List.pairwise_cons.1 h_sorted).1 p hp) hge
    exact Polynomial.leadingCoeff_eq_zero.1 (coeff_toPolyCore_of_degLt tail h_degLt_nd)

omit [DecidableEq R] in
lemma degree_eq_natDegree_toPoly (p : SparsePoly R) :
    p.degree = (toPoly p).natDegree := by
  by_cases hnil : p.coeffs = []
  · simp [degree, toPoly, toPolyCore, hnil]
  · rcases List.exists_cons_of_ne_nil hnil with ⟨hd, tl, hcoeffs⟩
    rcases hd with ⟨i, x⟩
    have hs : ((i, x) :: tl).Pairwise (·.1 > ·.1) := by simpa [hcoeffs] using p.sorted
    have hdegTl : degLt i tl := degLt_of_sorted_cons hs
    have hx0 : x ≠ 0 := by
     have := p.nonzero (i, x) (by simp [hcoeffs])
     simpa using this
    have hcoeff_i : (toPoly p).coeff i = x := by
     rw [toPoly, hcoeffs]
     simpa using coeff_toPolyCore_head (i := i) (a := x) tl hdegTl
    have hcoeff_i_ne : (toPoly p).coeff i ≠ 0 := by simpa [hcoeff_i] using hx0
    have hupper : ∀ k > i, (toPoly p).coeff k = 0 := by
     intro k hk
     have hdegTl' : degLt k tl := fun e he => lt_trans (hdegTl e he) hk
     rw [toPoly, hcoeffs, toPolyCore, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
     have hik : i ≠ k := by grind
     simp [coeff_toPolyCore_of_degLt tl hdegTl']
     grind
    have hle : i ≤ (toPoly p).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff_i_ne
    have hge : (toPoly p).natDegree ≤ i := by
     by_contra hgt
     have hi_lt : i < (toPoly p).natDegree := lt_of_not_ge hgt
     have hz : (toPoly p).coeff (toPoly p).natDegree = 0 := by grind
     specialize hupper (toPoly p).natDegree hi_lt
     aesop
    rw [show p.degree = i by simp [degree, hcoeffs], le_antisymm hge hle]

/-- The pseudo-division of `a` annihilates the leading `x*y*X^i` term (when `i > j`). -/
lemma toPoly_pseudo_rem_a (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
    (y • a - x • X^(i-j) * b).degree =
      (Polynomial.C y * toPolyCore as -
        Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs).natDegree := by
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, h1, Polynomial.X]
  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    intro n
    induction n with
    | zero => simp [toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  have hsmul_a : toPoly (y • a) = Polynomial.C y * toPoly a := by
    change toPoly (C y * a) = _; rw [toPoly_mul, toPoly_C]
  have hsmul_X : toPoly (x • (X : SparsePoly R)^(i - j)) =
      Polynomial.C x * Polynomial.X^(i - j) := by
    change toPoly (C x * (X : SparsePoly R)^(i - j)) = _; rw [toPoly_mul, toPoly_C, hpow]
  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
    simp [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
    simp [toPoly, toPolyCore, hb]
  have hcross :
      (Polynomial.C x * Polynomial.X^(i - j)) * (Polynomial.C y * Polynomial.X^j)
        = Polynomial.C y * (Polynomial.C x * Polynomial.X^i) := by
    have hpowX : (Polynomial.X : Polynomial R)^(i - j) * Polynomial.X^j = Polynomial.X^i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [← hpowX]; ring
  have hpoly :
      toPoly (y • a - x • X^(i-j) * b) =
        Polynomial.C y * toPolyCore as - Polynomial.C x * Polynomial.X^(i-j) * toPolyCore bs := by
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_a, hsmul_X, htoa, htob,
      mul_add, mul_add, hcross]
    ring
  rw [degree_eq_natDegree_toPoly _, hpoly]

/-- The pseudo-division of `b` annihilates the leading `x*y*X^j` term (when `¬ i > j`). -/
lemma toPoly_pseudo_rem_b (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬ (i > j)) :
    (x • b - y • X^(j-i) * a).degree =
      (Polynomial.C x * toPolyCore bs -
        Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as).natDegree := by
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, h1, Polynomial.X]
  have hpow : ∀ n : ℕ, toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    intro n
    induction n with
    | zero => simp [toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  have hsmul_b : toPoly (x • b) = Polynomial.C x * toPoly b := by
    change toPoly (C x * b) = _; rw [toPoly_mul, toPoly_C]
  have hsmul_X : toPoly (y • (X : SparsePoly R)^(j - i)) =
      Polynomial.C y * Polynomial.X^(j - i) := by
    change toPoly (C y * (X : SparsePoly R)^(j - i)) = _; rw [toPoly_mul, toPoly_C, hpow]
  have htoa : toPoly a = Polynomial.C x * Polynomial.X^i + toPolyCore as := by
    simp [toPoly, toPolyCore, ha]
  have htob : toPoly b = Polynomial.C y * Polynomial.X^j + toPolyCore bs := by
    simp [toPoly, toPolyCore, hb]
  have hcross :
      (Polynomial.C y * Polynomial.X^(j - i)) * (Polynomial.C x * Polynomial.X^i)
        = Polynomial.C x * (Polynomial.C y * Polynomial.X^j) := by
    have hpowX : (Polynomial.X : Polynomial R)^(j - i) * Polynomial.X^i = Polynomial.X^j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [← hpowX]; ring
  have hpoly :
      toPoly (x • b - y • X^(j-i) * a) =
        Polynomial.C x * toPolyCore bs - Polynomial.C y * Polynomial.X^(j-i) * toPolyCore as := by
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, hsmul_b, hsmul_X, htob, htoa,
      mul_add, mul_add, hcross]
    ring
  rw [degree_eq_natDegree_toPoly _, hpoly]

lemma deg_pseudo_rem_a (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hij : i > j) :
    (y • a - x • X^(i-j) * b).degree < a.degree := by
  rw [degree_eq_head a i x as ha, toPoly_pseudo_rem_a a b i j x y as bs ha hb hij]
  have h_coeff : ∀ k ≥ i, (Polynomial.C y * toPolyCore as -
      Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
    intro k hk
    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted
    have h_as_deg := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg := natDegree_toPolyCore_lt j y bs h_bs_sorted
    have h_as_coeff : (toPolyCore as).coeff k = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_bs_coeff : (toPolyCore bs).coeff (k - (i - j)) = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_term1 : (Polynomial.C y * toPolyCore as).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_as_coeff, mul_zero]
    have h_term2 : (Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs).coeff k = 0 := by
      rw [show Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs
            = (Polynomial.C x * toPolyCore bs) * Polynomial.X ^ (i - j) by ring,
        ← (by omega : (k - (i - j)) + (i - j) = k),
        Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]
    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]
  by_cases h_zero : (Polynomial.C y * toPolyCore as -
      Polynomial.C x * Polynomial.X ^ (i - j) * toPolyCore bs) = 0
  · rw [h_zero, Polynomial.natDegree_zero]; omega
  · exact lt_of_not_ge fun h_ge => h_zero (Polynomial.leadingCoeff_eq_zero.mp (h_coeff _ h_ge))

lemma deg_pseudo_rem_b (a b : SparsePoly R) (i j : ℕ) (x y : R) (as bs : List (ℕ × R))
    (ha : a.coeffs = (i, x) :: as) (hb : b.coeffs = (j, y) :: bs) (hji : ¬(i > j))
    (hj_pos : 0 < j) :
    (x • b - y • X^(j-i) * a).degree < b.degree := by
  rw [degree_eq_head b j y bs hb, toPoly_pseudo_rem_b a b i j x y as bs ha hb hji]
  have h_coeff : ∀ k ≥ j, (Polynomial.C x * toPolyCore bs -
      Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
    intro k hk
    have h_as_sorted : ((i, x) :: as).Pairwise (·.1 > ·.1) := by simpa [ha] using a.sorted
    have h_bs_sorted : ((j, y) :: bs).Pairwise (·.1 > ·.1) := by simpa [hb] using b.sorted
    have h_as_deg := natDegree_toPolyCore_lt i x as h_as_sorted
    have h_bs_deg := natDegree_toPolyCore_lt j y bs h_bs_sorted
    have h_bs_coeff : (toPolyCore bs).coeff k = 0 := by
      rcases h_bs_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_as_coeff : (toPolyCore as).coeff (k - (j - i)) = 0 := by
      rcases h_as_deg with hlt | h0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [h0]; simp
    have h_term1 : (Polynomial.C x * toPolyCore bs).coeff k = 0 := by
      rw [Polynomial.coeff_C_mul, h_bs_coeff, mul_zero]
    have h_term2 : (Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as).coeff k = 0 := by
      rw [show Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as
            = (Polynomial.C y * toPolyCore as) * Polynomial.X ^ (j - i) by ring,
        ← (by omega : (k - (j - i)) + (j - i) = k),
        Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, h_as_coeff, mul_zero]
    rw [Polynomial.coeff_sub, h_term1, h_term2, sub_zero]
  by_cases h_zero : (Polynomial.C x * toPolyCore bs -
      Polynomial.C y * Polynomial.X ^ (j - i) * toPolyCore as) = 0
  · rw [h_zero, Polynomial.natDegree_zero]; exact hj_pos
  · exact lt_of_not_ge fun h_ge => h_zero (Polynomial.leadingCoeff_eq_zero.mp (h_coeff _ h_ge))

/-- A subresultant-style GCD of two polynomials that avoids division: it repeatedly cancels leading
terms via cross-multiplication (`y • a - x • X^(i-j) * b`), producing a GCD up to a scalar/content
factor. -/
def gcdPrim (a b : SparsePoly R) : SparsePoly R :=
  match _ha : a.coeffs with
  | [] => b
  | (i, x) :: _as =>
    match hb : b.coeffs with
    | [] => a
    | (j, y) :: bs =>
      if h_const : i = 0 ∧ j = 0 then
        a
      else if h_gt : i > j then
        gcdPrim (y • a - x • X^(i-j) * b) b
      else
        gcdPrim a (x • b - y • X^(j-i) * a)
termination_by a.degree + b.degree
decreasing_by
  · simp_wf
    have h_drop := deg_pseudo_rem_a a b i j x y _as bs _ha hb h_gt
    aesop
  · simp_wf
    have hj_pos : 0 < j := by omega
    have h_drop := deg_pseudo_rem_b a b i j x y _as bs _ha hb h_gt hj_pos
    aesop

omit [DecidableEq R] in
lemma foldl_gcd_dvd_acc [GCDMonoid R] (l : List (ℕ × R)) (acc : R) :
    l.foldl (fun a x => gcd a x.2) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact (ih (gcd acc hd.2)).trans (gcd_dvd_left _ _)

omit [DecidableEq R] in
lemma foldl_gcd_dvd_mem [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) (acc : R) : l.foldl (fun a x => gcd a x.2) acc ∣ c := by
  induction l generalizing acc with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h_mem
    · exact (foldl_gcd_dvd_acc tl (gcd acc c)).trans (gcd_dvd_right _ _)
    · exact ih h_mem (gcd acc hd.2)

omit [DecidableEq R] in
lemma content_dvd_coeff_final [GCDMonoid R] {l : List (ℕ × R)} {i : ℕ} {c : R}
    (h : (i, c) ∈ l) : l.foldl (init := 0) (fun acc x => gcd acc x.2) ∣ c :=
  foldl_gcd_dvd_mem h 0

/-- The content of a polynomial: the `gcd` of all its coefficients. -/
def content [GCDMonoid R] (a : SparsePoly R) : R :=
  a.coeffs.foldl (init := 0) (gcd · ·.2)

/-- The primitive part of a polynomial: the result of dividing every coefficient by the content,
yielding a polynomial whose coefficients have `gcd` a unit. -/
def primitivePart [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : SparsePoly R) : SparsePoly R where
  coeffs :=
    let b := a.content
    a.coeffs.map fun (i, a) => (i, a / b)
  sorted := by
    have h_sorted := a.sorted
    grind
  nonzero := by
    intro x hx
    simp only [List.mem_map, Prod.exists] at hx
    rcases hx with ⟨i, c, h_mem, rfl⟩
    have hc_nz := a.nonzero (i, c) h_mem
    let b := a.content
    intro h_div_zero
    have h_mul := congr_arg (fun (z : R) => b * z) h_div_zero
    simp only [mul_zero] at h_mul
    have h_dvd : b ∣ c := content_dvd_coeff_final h_mem
    rw [IsExactDiv.mul_div_cancel h_dvd] at h_mul
    exact hc_nz h_mul

/-- The GCD of two polynomials: the GCD of their contents times the primitive part of the
division-free `gcdPrim`. -/
nonrec def gcd [GCDMonoid R]
    [Div R] [IsExactDiv R] (a b : SparsePoly R) : SparsePoly R :=
  gcd a.content b.content • (gcdPrim a b).primitivePart

instance : IsExactDiv ℤ where
  mul_div_cancel := Int.mul_ediv_cancel'

instance {R} [CommGroupWithZero R] : IsExactDiv R where
  mul_div_cancel h := by
    apply mul_div_cancel_of_imp'; rintro rfl
    simpa only [zero_dvd_iff] using h


omit [DecidableEq R] in
/-- Helper: If all elements in the list have exponents strictly
  less than k, the coefficient at k is 0. -/
lemma coeff_toPolyCore_eq_zero_of_forall_lt (l : List (ℕ × R)) (k : ℕ)
    (h : ∀ p ∈ l, p.1 < k) : (toPolyCore l).coeff k = 0 := by
  induction l with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, y⟩
    have h_k_ne_j : k ≠ j := (by aesop : j < k).ne'
    have h_tail_zero : (toPolyCore tl).coeff k = 0 := by
      apply ih
      intro p hp
      exact h _ (by simp [hp])
    unfold toPolyCore
    simp [h_k_ne_j, h_tail_zero]

omit [DecidableEq R] in
lemma degree_eq_poly_degree (a : SparsePoly R) (h : a.coeffs ≠ []) :
    a.degree = (toPoly a).natDegree := by
  rcases h_coeffs : a.coeffs with _ | ⟨⟨i, x⟩, as⟩
  · contradiction
  have h_deg : a.degree = i := by simp [degree, h_coeffs]
  rw [h_deg]
  have h_as_lt : ∀ p ∈ as, p.1 < i := by
    intro p hp
    have h_sorted := a.sorted
    rw [h_coeffs] at h_sorted
    exact List.rel_of_pairwise_cons h_sorted hp
  have h_coeff_i : (toPoly a).coeff i = x := by
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_tail_zero : (toPolyCore as).coeff i = 0 :=
      coeff_toPolyCore_eq_zero_of_forall_lt _ _ h_as_lt
    simp [h_tail_zero]
  have h_nz : (toPoly a).coeff i ≠ 0 := by
    rw [h_coeff_i]
    exact a.nonzero (i, x) (by rw [h_coeffs]; simp)
  have h_zero : ∀ k > i, (toPoly a).coeff k = 0 := by
    intro k hk
    simp only [toPoly, h_coeffs]
    unfold toPolyCore
    have h_tail_zero : (toPolyCore as).coeff k = 0 :=
      coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => (h_as_lt p hp).trans hk
    simp [hk.ne', h_tail_zero]
  symm
  apply le_antisymm
  · by_contra h_gt
    push Not at h_gt
    rw [Polynomial.leadingCoeff_eq_zero.mp (h_zero _ h_gt)] at h_nz
    simp at h_nz
  · by_contra h_lt
    push Not at h_lt
    exact h_nz (Polynomial.coeff_eq_zero_of_natDegree_lt h_lt)

omit [DecidableEq R] in
/-- Core Helper: Pushing scalar multiplication through the list translation -/
lemma toPolyCore_map_smul (c : R) (l : List (ℕ × R)) :
    toPolyCore (l.map fun p => (p.1, c * p.2)) = Polynomial.C c * toPolyCore l := by
  induction l with
  | nil => unfold toPolyCore; simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩
    simp only [List.map_cons]
    unfold toPolyCore
    rw [ih, mul_add, map_mul]
    ring

private def coeffCore : List (ℕ × R) → ℕ → R
  | [], _ => 0
  | (i, a) :: tl, n => if n = i then a else coeffCore tl n

/-- The coefficient of `X^n` in a `SparsePoly R`, found by searching its coefficient list. -/
def coeff (P : SparsePoly R) (n : ℕ) : R :=
  coeffCore P.coeffs n

omit [DecidableEq R] in
/-- Core List Helper: Custom list search matches Mathlib Polynomial evaluation -/
lemma coeffCore_eq_toPolyCore_coeff (l : List (ℕ × R)) (n : ℕ)
    (hsorted : l.Pairwise (·.1 > ·.1)) :
    coeffCore l n = (toPolyCore l).coeff n := by
  induction l generalizing n with
  | nil => unfold coeffCore toPolyCore; simp
  | cons hd tl ih =>
    rcases hd with ⟨i, x⟩
    have hhead : ∀ p ∈ tl, i > p.1 := (List.pairwise_cons.1 hsorted).1
    have htail : tl.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 hsorted).2
    unfold coeffCore toPolyCore
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
    by_cases h_eq : n = i
    · have h_tail_zero : (toPolyCore tl).coeff n = 0 :=
        coeff_toPolyCore_of_degLt tl fun p hp => by grind
      simp [h_eq]
      grind
    · simp [h_eq, ih n htail]

omit [DecidableEq R] in
/-- The Main Bridge Lemma -/
lemma coeff_toPoly (P : SparsePoly R) (n : ℕ) :
    P.coeff n = (toPoly P).coeff n :=
  coeffCore_eq_toPolyCore_coeff P.coeffs n P.sorted

lemma toPoly_smul (c : R) (P : SparsePoly R) :
    toPoly (c • P) = Polynomial.C c * toPoly P := by
  change toPoly (C c * P) = Polynomial.C c * toPoly P
  rw [toPoly_mul, toPoly_C]

/-- How scalar multiplication affects the translated polynomial's coefficients -/
lemma coeff_smul (c : R) (P : SparsePoly R) (n : ℕ) :
    (toPoly (c • P)).coeff n = c * (toPoly P).coeff n := by
  change (toPoly (C c * P)).coeff n = c * (toPoly P).coeff n
  rw [toPoly_mul, toPoly_C, Polynomial.coeff_C_mul]

lemma toPoly_smul_X_pow_mul (c : R) (n : ℕ) (Q : SparsePoly R) :
    toPoly ((c • X^n) * Q) = Polynomial.C c * Polynomial.X^n * toPoly Q := by
  rw [toPoly_mul, toPoly_smul]
  have hX : toPoly (X : SparsePoly R) = Polynomial.X := by
    by_cases h1 : (1 : R) = 0 <;>
      · unfold X toPoly ofSortedList; simp [toPolyCore, Polynomial.X, h1]
  have hpow : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
    induction n with
    | zero => simp [pow_zero, toPoly_one]
    | succ n ih =>
      simpa [pow_succ, ih, hX] using toPoly_mul ((X : SparsePoly R)^n) (X : SparsePoly R)
  rw [hpow]

/-- Bridge: Translates a SparsePoly monomial into a Mathlib Polynomial -/
lemma toPoly_smul_X_pow (c : R) (n : ℕ) :
    toPoly (c • X^n) = Polynomial.C c * Polynomial.X^n := by
  calc
    toPoly (c • X^n) = toPoly ((c • X^n) * (1 : SparsePoly R)) := by simp
    _ = Polynomial.C c * Polynomial.X^n * toPoly (1 : SparsePoly R) :=
      toPoly_smul_X_pow_mul (R := R) c n (1 : SparsePoly R)
    _ = Polynomial.C c * Polynomial.X^n := by simp [toPoly_one]

lemma degree_sub_leading_term_lt [Div R]
    (P Q : SparsePoly R) {i j : ℕ} {x y : R} {as bs : List (ℕ × R)}
    (ha : P.coeffs = (i, x) :: as)
    (hb : Q.coeffs = (j, y) :: bs)
    (h_deg : j ≤ i) (h_div : y * (x / y) = x) (h_pos : 0 < i) :
    degree (P - ((x / y) • X^(i - j)) * Q) < i := by
  by_cases h_empty : (P - ((x / y) • X^(i - j)) * Q).coeffs = []
  · unfold degree
    rw [h_empty]
    grind
  rw [degree_eq_poly_degree _ h_empty]
  by_contra h_ge
  push Not at h_ge
  have h_coeff_zero : ∀ k ≥ i, (toPoly (P - ((x / y) • X^(i - j)) * Q)).coeff k = 0 := by
    intro k hk
    rw [sub_eq_add_neg, toPoly_add, toPoly_neg, toPoly_mul, toPoly_smul_X_pow]
    simp only [Polynomial.coeff_add, Polynomial.coeff_neg]
    have hP_deg : P.degree = i := by simp [degree, ha]
    have hQ_deg : Q.degree = j := by simp [degree, hb]
    have hP_nz : P.coeffs ≠ [] := by rw [ha]; grind
    have hQ_nz : Q.coeffs ≠ [] := by rw [hb]; grind
    rcases eq_or_lt_of_le hk with rfl | h_gt
    · have hP_lead : (toPoly P).coeff i = x := by
        simp only [toPoly, ha]
        unfold toPolyCore
        have h_tail_zero : (toPolyCore as).coeff i = 0 :=
          coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => by
            have hs := P.sorted; rw [ha] at hs; exact List.rel_of_pairwise_cons hs hp
        simp [h_tail_zero]
      have hQ_lead : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff i = x := by
        rw [show Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
              (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) by ring]
        have h_coeff_mul_X_pow :
            (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i =
              (Polynomial.C (x / y) * toPoly Q).coeff j := by
          calc (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff i
              = (Polynomial.C (x / y) * toPoly Q * Polynomial.X ^ (i - j)).coeff (j + (i - j)) := by
                simp [(by omega : j + (i - j) = i)]
            _ = (Polynomial.C (x / y) * toPoly Q).coeff j := by simp
        rw [h_coeff_mul_X_pow]
        have hQ_j : (toPoly Q).coeff j = y := by
          simp only [toPoly, hb]
          unfold toPolyCore
          have h_tail_zero : (toPolyCore bs).coeff j = 0 :=
            coeff_toPolyCore_eq_zero_of_forall_lt _ _ fun p hp => by
              have hs := Q.sorted; rw [hb] at hs; exact List.rel_of_pairwise_cons hs hp
          simp [h_tail_zero]
        grind
      grind
    · have hP_zero : (toPoly P).coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [← degree_eq_poly_degree P hP_nz, hP_deg]; exact h_gt)
      have hQ_zero : (Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q).coeff k = 0 := by
        rw [show Polynomial.C (x / y) * Polynomial.X ^ (i - j) * toPoly Q =
              (Polynomial.C (x / y) * toPoly Q) * Polynomial.X ^ (i - j) by ring,
          ← (by omega : (k - (i - j)) + (i - j) = k),
          Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [← degree_eq_poly_degree Q hQ_nz, hQ_deg]; omega), mul_zero]
      rw [hP_zero, hQ_zero, neg_zero, add_zero]
  have h_poly_zero : toPoly (P - ((x / y) • X^(i - j)) * Q) = 0 :=
    Polynomial.leadingCoeff_eq_zero.mp (h_coeff_zero _ h_ge)
  rw [show (toPoly (P - ((x / y) • X^(i - j)) * Q)).natDegree = 0 by
    rw [h_poly_zero, Polynomial.natDegree_zero]] at h_ge
  exact (not_lt_of_ge h_ge h_pos).elim

/-- Polynomial division with remainder: returns a quotient/remainder pair `(q, r)` with
`b * q + r = a`, using `IsExactDiv`-style division of leading coefficients (bailing out with
quotient `0` when the leading coefficient does not divide exactly). -/
def divRem [Div R] (a b : SparsePoly R) : SparsePoly R × SparsePoly R :=
  match _ha : a.coeffs, _hb : b.coeffs with
  | (i, x) :: _as, (j, y) :: _bs =>
    if _h_lt : i < j then
      (0, a)
    else
      if h_pos : i = 0 then
        let c := (x / y) • X^0
        if y * (x / y) = x then
          (c, a - c * b)
        else
          (0, a)
      else
        let c := (x / y) • X^(i - j)
        if _h_div : y * (x / y) = x then
          let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
          (q' + c, r')
        else
          (0, a)
  | _, _ => (0, a)
termination_by if a.coeffs = [] then 0 else a.degree + 1
decreasing_by
  simp_wf
  have hj_le_i : j ≤ i := by omega
  have h_pos_i : 0 < i := by omega
  have ha_not_empty : a.coeffs ≠ [] := by rw [_ha]; simp
  have h_deg : a.degree = i := by unfold degree; rw [_ha]; rfl
  rw [if_neg ha_not_empty, h_deg]
  by_cases h_empty : (a - ((x / y) • X^(i - j)) * b).coeffs = []
  · aesop
  · have h_lt_i := degree_sub_leading_term_lt a b _ha _hb hj_le_i _h_div h_pos_i
    aesop

instance [Div R] : Div (SparsePoly R) where
  div a b := (divRem a b).1

/-- Unfolding lemma to safely evaluate divRem without projection motive errors -/
lemma divRem_eq [Div R] (a b : SparsePoly R) :
    divRem a b =
      match _ha : a.coeffs, _hb : b.coeffs with
      | (i, x) :: _as, (j, y) :: _bs =>
        if _h_lt : i < j then
          (0, a)
        else
          if _h_pos : i = 0 then
            let c := (x / y) • X^0
            if y * (x / y) = x then
              (c, a - c * b)
            else
              (0, a)
          else
            let c := (x / y) • X^(i - j)
            if _h_div : y * (x / y) = x then
              let (q', r') := divRem (a - ((x / y) • X^(i - j)) * b) b
              (q' + c, r')
            else
              (0, a)
      | _, _ => (0, a) := by
  rw [divRem]

lemma divRem_spec [Div R] (a b : SparsePoly R) :
    b * (divRem a b).1 + (divRem a b).2 = a := by
  induction a using divRem.induct
  case b => exact b
  case case1 a i x as j y bs ha hb h_lt =>
    rw [divRem_eq, ha, hb]
    simp [h_lt]
  case case2 a i x as j y bs ha hb h_nlt h_pos h_div =>
    rw [divRem_eq, hb]
    simp
    aesop
  case case3 a i x as j y bs ha hb h_nlt h_pos h_ndiv =>
    rw [divRem_eq, hb]
    simp
    grind
  case case4 a i x as j y bs ha hb h_nlt h_npos h_div q' r' heq ih =>
    rw [divRem_eq, ha, hb]
    simp only [h_nlt, ↓reduceDIte, h_npos, h_div, Algebra.smul_mul_assoc]
    rw [show ∀ (q r c : SparsePoly R),
      b * (q + c) + r = (b * q + r) + b * c from fun _ _ _ => by grind]
    simp_all only [not_lt, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    grind
  case case5 a i x as j y bs ha hb h_nlt h_npos h_ndiv =>
    rw [divRem_eq, ha, hb]
    simp [h_nlt, h_npos, h_ndiv]
  case case6 =>
    rw [divRem_eq]
    split <;> grind

/-- Degree of multiplication. Requires `[IsDomain R]` so zero-divisors don't wipe out the leading
term. -/
lemma degree_mul [IsDomain R] (a b : SparsePoly R)
    (ha : a.coeffs ≠ []) (hb : b.coeffs ≠ []) : (a * b).degree = a.degree + b.degree := by
  rw [degree_eq_natDegree_toPoly (a * b), degree_eq_natDegree_toPoly a,
    degree_eq_natDegree_toPoly b, toPoly_mul]
  have h_ne : ∀ {c : SparsePoly R}, c.coeffs ≠ [] → toPoly c ≠ 0 := fun {c} hc h =>
    hc (by rw [toPoly_injective (h.trans toPoly_zero.symm)]; rfl)
  exact Polynomial.natDegree_mul (h_ne ha) (h_ne hb)

instance : DecidableEq (SparsePoly R) := fun a b =>
  decidable_of_iff' (a.coeffs = b.coeffs) (SparsePoly.ext_iff ..)

#eval (X * (C X * X + C (X + 2) : SparsePoly (SparsePoly ℤ))) / X

/-- Bridge: the sparse variable `X` translates to the Mathlib variable `X`. -/
theorem toPoly_X_fixed : toPoly (X : SparsePoly R) = Polynomial.X := by
  unfold X toPoly ofSortedList
  dsimp only
  by_cases h1 : (1 : R) = 0
  · simp [h1, toPolyCore]; aesop
  · simp [h1, toPolyCore]

/-- Bridge: powers of `X` translate correctly. -/
theorem toPoly_pow (n : ℕ) : toPoly ((X : SparsePoly R)^n) = Polynomial.X^n := by
  induction n with
  | zero => simp [toPoly_one]
  | succ n ih => simp [pow_succ, toPoly_mul, toPoly_X_fixed, ih]

lemma toPoly_ofPoly (p : Polynomial R) :
    toPoly (p.eval₂ (algebraMap R (SparsePoly R)) X) = p := by
  induction p using Polynomial.induction_on with
  | C r =>
    simp only [eval₂_C]
    exact toPoly_C (R := R) r
  | add =>
    simp only [eval₂_add, toPoly_add]
    grind
  | monomial n r ih =>
    simp only [eval₂_mul, eval₂_C, eval₂_X_pow, toPoly_mul, toPoly_pow]
    rw [← toPoly_C]
    rfl

/-- The `R`-algebra isomorphism between the computable `SparsePoly R` and Mathlib's
`Polynomial R`, given by `toPoly` with inverse `eval₂ (algebraMap R _) X`. -/
noncomputable def toPolyEquiv : SparsePoly R ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap R (SparsePoly R)) X
  right_inv p := toPoly_ofPoly p
  left_inv p := by
    apply toPoly_injective
    rw [toPoly_ofPoly]
  map_add' := toPoly_add
  map_mul' := toPoly_mul
  commutes' r := toPoly_C r

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : SparsePoly R) := by
  simp [toPolyEquiv]

@[simp]
theorem toPoly_X : (X : SparsePoly R).toPoly = Polynomial.X := by
  rw [← toPolyEquiv.apply_symm_apply Polynomial.X, ofPoly_X]; rfl

end SparsePoly
