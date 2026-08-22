/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.Basic

/-!
# `SparsePoly`: construction from unsorted lists and injectivity of `toPoly`

`ofList` builds a canonical `SparsePoly R` from an arbitrary `(exponent, coefficient)` list by
sorting and merging; `X` is the sparse variable. The main result is `toPoly_injective`: the
canonical-form invariant makes the semantics map injective, which is what the reflection tactics
rely on to transport decidable equality.
-/

@[expose] public section

namespace SparsePoly

open Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

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

/-- Bridge: the sparse variable `X` translates to the Mathlib variable `X`. -/
@[simp]
theorem toPoly_X : toPoly (X : SparsePoly R) = Polynomial.X := by
  unfold X toPoly ofSortedList
  dsimp only
  by_cases h1 : (1 : R) = 0
  · simp [h1, toPolyCore]; aesop
  · simp [h1, toPolyCore]

end SparsePoly
