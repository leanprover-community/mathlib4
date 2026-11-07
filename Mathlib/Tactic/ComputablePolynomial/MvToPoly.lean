/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvMul

/-!
# `MvSparsePoly`: the `Finsupp` bridge and injectivity of `toPoly`

The bridge between `MvDegrees` and the `Fin nvars →₀ ℕ` exponents of Mathlib's `MvPolynomial`
(`toFinsupp_inj`, `toFinsupp_add`), the semantics of constants and `1`, and the key
`toPoly_injective`: the canonical-form invariant makes the semantics map injective. Ends with
additivity, `toPoly_add`.
-/

@[expose] public section

variable {nvars : ℕ}

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-! ### The Mathlib `Finsupp` bridge, identity and injectivity -/

open MvPolynomial

/-- `MvDegrees.toFinsupp` is injective. -/
lemma toFinsupp_inj {i j : MvDegrees nvars} :
    MvDegrees.toFinsupp i = MvDegrees.toFinsupp j ↔ i = j := by
  constructor
  · intro h
    have h_arr : i.degrees = j.degrees := by
      apply Array.ext
      · exact i.correct.trans j.correct.symm
      · intro v hv1 hv2
        have hv_fin : v < nvars := by aesop
        exact Finsupp.ext_iff.mp h ⟨v, hv_fin⟩
    have h_tot : i.totalDegree = j.totalDegree := by
      rw [i.totalDegree_eq, j.totalDegree_eq, h_arr]
    cases i
    cases j
    simp_all
  · intro h
    rw [h]

/-- `MvDegrees.toFinsupp` is additive. -/
lemma toFinsupp_add (i j : MvDegrees nvars) :
    MvDegrees.toFinsupp (i + j) =
    MvDegrees.toFinsupp i + MvDegrees.toFinsupp j := by
  ext v
  rw [Finsupp.add_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  dsimp only [HAdd.hAdd, Add.add]
  simp

/-- `MvDegrees.toFinsupp` sends `0` to `0`. -/
lemma toFinsupp_zero :
    MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  have h_zero_def : (0 : MvDegrees nvars).degrees =
    (List.replicate nvars 0).toArray := rfl
  simp only [h_zero_def]
  grind

/-- `toPoly` of a constant polynomial is the constant `MvPolynomial`. -/
theorem toPoly_C (r : R) : toPoly (C r : MvSparsePoly R nvars) =
    MvPolynomial.C r := by
  unfold C toPoly ofSortedList
  dsimp only
  by_cases hr : r = 0
  · subst hr
    unfold toPolyCore
    grind
  · have h_filter : ([(0, r)] : List (MvDegrees nvars × R)).filter (·.2 ≠ 0) = [(0, r)] := by
      simp [hr]
    rw [h_filter]
    change MvPolynomial.monomial (MvDegrees.toFinsupp 0) r +
      toPolyCore [] = MvPolynomial.C r
    unfold toPolyCore
    rw [add_zero]
    have h_zero : MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := toFinsupp_zero
    aesop

/-- `toPoly` of `1` is `1`. -/
lemma toPoly_one : toPoly (1 : MvSparsePoly R nvars) = 1 := by
  change toPoly (C 1 : MvSparsePoly R nvars) = 1
  rw [toPoly_C]
  exact map_one (MvPolynomial.C)

omit [DecidableEq R] in
/-- The coefficient at `n` of a polynomial with all degrees `< n` is zero. -/
theorem coeff_toPolyCore_of_degLt {n : MvDegrees nvars}
     (xs : List (MvDegrees nvars × R)) (h : degLt n xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp n) (toPolyCore xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [MvPolynomial.coeff_add]
    have h_deg : i < n := h (i, a) List.mem_cons_self
    have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp n :=
      fun h_eq => ne_of_lt h_deg (toFinsupp_inj.mp h_eq)
    rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

omit [DecidableEq R] in
/-- The coefficient of the head term at its own exponent `i` is its coefficient. -/
theorem coeff_toPolyCore_head {i : MvDegrees nvars} {a : R}
  (xs : List (MvDegrees nvars × R)) (h : degLt i xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) = a := by
  dsimp only [toPolyCore]
  simp only [MvPolynomial.coeff_add]
  rw [MvPolynomial.coeff_monomial, if_pos rfl, coeff_toPolyCore_of_degLt xs h, add_zero]

omit [CommRing R] [DecidableEq R] in
/-- Extract `degLt` from `Pairwise` sortedness. -/
lemma degLt_of_sorted_cons {i : MvDegrees nvars} {a : R}
  {xs : List (MvDegrees nvars × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

omit [DecidableEq R] in
/-- `toPolyCore` is injective on sorted term lists. -/
theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (MvDegrees nvars × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore []) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp j)
                   (toPolyCore ((j, b) :: ys)) := by
                    rw [heq]
    change 0 = _ at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore ((i, a) :: xs)) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore []) := by rw [heq]
    change _ = 0 at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j)
                     (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      have h_xs_j : degLt j xs := fun e he => lt_trans (h_deg_x e he) hij
      have h_lhs : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((i, a) :: xs)) = 0 := by
        dsimp only [toPolyCore]
        simp only [MvPolynomial.coeff_add]
        have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp j :=
          fun h_eq => (ne_of_lt hij) (toFinsupp_inj.mp h_eq)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
          coeff_toPolyCore_of_degLt xs h_xs_j, zero_add]
      rw [h_lhs] at h_coeff
      have hb_nz := nz2 (j, b) List.mem_cons_self
      exact False.elim (hb_nz h_coeff.symm)
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x, coeff_toPolyCore_head ys h_deg_y] at h_coeff
      subst h_coeff
      dsimp only [toPolyCore] at heq
      have heq_xs_ys : toPolyCore xs = toPolyCore ys := add_left_cancel heq
      have s1_xs : xs.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s1).2
      have s2_ys : ys.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s2).2
      have nz1_xs : ∀ x ∈ xs, x.2 ≠ 0 := fun e he => nz1 e (List.mem_cons_of_mem _ he)
      have nz2_ys : ∀ x ∈ ys, x.2 ≠ 0 := fun e he => nz2 e (List.mem_cons_of_mem _ he)
      rw [toPolyCore_injective_of_sorted xs ys s1_xs s2_ys nz1_xs nz2_ys heq_xs_ys]
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      have h_ys_i : degLt i ys := fun e he => lt_trans (h_deg_y e he) hji
      have h_rhs : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) = 0 := by
        dsimp only [toPolyCore]
        simp only [MvPolynomial.coeff_add]
        have h_finsupp_ne : MvDegrees.toFinsupp j ≠ MvDegrees.toFinsupp i :=
          fun h_eq => (ne_of_lt hji) (toFinsupp_inj.mp h_eq)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
          coeff_toPolyCore_of_degLt ys h_ys_i, zero_add]
      rw [h_rhs] at h_coeff
      have ha_nz := nz1 (i, a) List.mem_cons_self
      exact False.elim (ha_nz h_coeff)

omit [DecidableEq R] in
lemma toPoly_injective : Function.Injective (toPoly (R := R) (nvars := nvars)) := by
  intro x y h
  ext1
  exact toPolyCore_injective_of_sorted x.terms y.terms x.sorted y.sorted x.nonzero y.nonzero h

/-- Filtering out zero coefficients does not change the `MvPolynomial`. -/
theorem toPolyCore_filter_nonzero (l : List (MvDegrees nvars × R)) :
    toPolyCore (l.filter (·.2 ≠ 0)) = toPolyCore l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    simp only [List.filter_cons]
    split
    · next h_nonzero => unfold toPolyCore; rw [ih]
    · next h_zero =>
      have ha0 : a = 0 := by aesop
      unfold toPolyCore
      rw [ha0, map_zero, zero_add]
      aesop

/-- `addCore` mirrors `MvPolynomial` addition. -/
theorem toPolyCore_addCore : ∀ (x y : List (MvDegrees nvars × R)),
    toPolyCore (addCore x y) = toPolyCore x + toPolyCore y
  | [], yy => by simp [addCore, toPolyCore]
  | (i, a) :: x, [] => by simp [addCore, toPolyCore]
  | (i, a) :: x, (j, b) :: y => by
    simp only [addCore]
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_not_ji : ¬(j < i) := fun h_contra => lt_irrefl i (lt_trans hlt h_contra)
      simp only [hlt, ↓reduceIte]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]
      ring
    · subst heq
      simp only [lt_self_iff_false, ↓reduceIte]
      split
      · next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore]
          have h_rearrange : (MvPolynomial.monomial (MvDegrees.toFinsupp i) a + toPolyCore x) +
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) b + toPolyCore y) =
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) a +
                              MvPolynomial.monomial (MvDegrees.toFinsupp i) b) +
                             (toPolyCore x + toPolyCore y) := by ring
          rw [h_rearrange, ← map_add, hab, map_zero, zero_add]
      · next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore, map_add]
          ring
    · have h_not_ij : ¬(i < j) := fun h_contra => lt_irrefl j (lt_trans hgt h_contra)
      simp only [h_not_ij, ↓reduceIte, hgt]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]
      ring
termination_by x y => x.length + y.length

lemma toPoly_add (a b : MvSparsePoly R nvars) : toPoly (a + b) = toPoly a + toPoly b := by
  unfold toPoly
  change toPolyCore ((addCore a.terms b.terms).filter (·.2 ≠ 0)) =
         toPolyCore a.terms + toPolyCore b.terms
  rw [toPolyCore_filter_nonzero]
  exact toPolyCore_addCore a.terms b.terms


end MvSparsePoly
