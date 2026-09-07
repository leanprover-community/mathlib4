/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import HexPolyZ
public import Mathlib.Algebra.Polynomial.Hex.Euclid
public import Mathlib.Algebra.Polynomial.Hex.Squarefree
public import Mathlib.Analysis.Polynomial.Sturm.Basic
public import Mathlib.Analysis.Polynomial.Hex.Basic
public import HexRealRoots.Var
-- `import all` on the executable modules so the non-`@[expose]` bodies of
-- `signVar`, `sturmVarAt`, `evalDyadic`, and `dyadicSign` unfold here, and on
-- `Separation` so `Dyadic.toReal` unfolds.
import all Mathlib.Analysis.Polynomial.Hex.Basic
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

/-!
# Sign variations of executable polynomial chains

Relate evaluation of integer coefficient arrays at dyadic points to evaluation of
Mathlib polynomials over `ℝ`, and identify `Hex.signVar` with `Sturm.signVariations`.
The rational squarefreeness correspondence is shared with the Sturm-chain proofs.
-/

public section

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-- Compatibility alias for the rational cast, now shared by integer-polynomial
companions. -/
abbrev toPolyℚ (p : Hex.ZPoly) := HexPolyZMathlib.toPolyℚ p

theorem size_le_one_iff_natDegree_eq_zero {R : Type*} [Semiring R]
    [DecidableEq R] (g : Hex.DensePoly R) :
    g.size ≤ 1 ↔ (HexPolyMathlib.toPolynomial g).natDegree = 0 :=
  HexPolyZMathlib.size_le_one_iff_natDegree_eq_zero g

theorem toPolynomial_toRatPoly (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) = toPolyℚ f :=
  HexPolyZMathlib.toPolynomial_toRatPoly f

theorem coeff_toPolyℚ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℚ p).coeff n = (p.coeff n : ℚ) :=
  HexPolyZMathlib.coeff_toPolyℚ p n

theorem eval_toPolyℚ (p : Hex.ZPoly) (x : ℚ) :
    (toPolyℚ p).eval x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℚ) * x ^ i :=
  HexPolyZMathlib.eval_toPolyℚ p x

theorem toPolyℚ_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) : toPolyℚ f ≠ 0 :=
  HexPolyZMathlib.toPolyℚ_ne_zero hf

/-- Compatibility alias for the shared rational squarefreeness bridge. -/
theorem squareFreeRat_iff (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat f ↔ Squarefree (toPolyℚ f) :=
  HexPolyZMathlib.squareFreeRat_iff f hf

/-! # Sign-variation correspondence at a dyadic point -/

/-- `Dyadic.toReal` is additive. -/
theorem toReal_add (a b : Dyadic) :
    Dyadic.toReal (a + b) = Dyadic.toReal a + Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_add]; push_cast; ring

/-- `Dyadic.toReal` is multiplicative. -/
theorem toReal_mul (a b : Dyadic) :
    Dyadic.toReal (a * b) = Dyadic.toReal a * Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_mul]; push_cast; ring

/-- `Dyadic.toReal` sends `0` to `0`. -/
@[simp] theorem toReal_zero : Dyadic.toReal 0 = 0 := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_zero]; norm_num

/-- The horner polynomial built from a real coefficient list, lowest degree
first. `hornerPoly (c :: cs) = C c + X * hornerPoly cs`. -/
private noncomputable def hornerPoly (cs : List ℝ) : Polynomial ℝ :=
  cs.foldr (fun c p => Polynomial.C c + Polynomial.X * p) 0

private theorem eval_hornerPoly (r : ℝ) : ∀ cs : List ℝ,
    (hornerPoly cs).eval r = cs.foldr (fun c acc => c + r * acc) 0
  | [] => by simp [hornerPoly]
  | c :: cs => by
      change (Polynomial.C c + Polynomial.X * hornerPoly cs).eval r = _
      rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
        eval_hornerPoly r cs]
      rfl

private theorem coeff_hornerPoly : ∀ (cs : List ℝ) (n : Nat),
    (hornerPoly cs).coeff n = cs.getD n 0
  | [], n => by simp [hornerPoly]
  | c :: cs, n => by
      change (Polynomial.C c + Polynomial.X * hornerPoly cs).coeff n = _
      cases n with
      | zero => simp
      | succ m =>
          rw [Polynomial.coeff_add, Polynomial.coeff_C, ite_eq_right (Nat.succ_ne_zero m),
            Polynomial.coeff_X_mul, coeff_hornerPoly cs m, zero_add, List.getD_cons_succ]

private theorem getD_map_intCast : ∀ (L : List Int) (n : Nat),
    (L.map (Int.cast : ℤ → ℝ)).getD n 0 = ((L.getD n 0 : Int) : ℝ)
  | [], n => by simp
  | a :: L, n => by
      cases n with
      | zero => simp
      | succ m => simpa using getD_map_intCast L m

/-- Pushing `Dyadic.toReal` through the `evalDyadic` Horner fold turns it into the
same fold over the real casts of the coefficients. -/
private theorem toReal_horner_foldr (x : Dyadic) : ∀ cs : List Int,
    Dyadic.toReal (cs.foldr (fun c acc => Dyadic.ofInt c + x * acc) 0)
      = (cs.map (Int.cast : ℤ → ℝ)).foldr (fun c acc => c + Dyadic.toReal x * acc) 0
  | [] => by simp
  | c :: cs => by
      change Dyadic.toReal (Dyadic.ofInt c + x * cs.foldr (fun c acc => Dyadic.ofInt c + x * acc) 0)
          = (c : ℝ) + Dyadic.toReal x *
              (cs.map (Int.cast : ℤ → ℝ)).foldr (fun c acc => c + Dyadic.toReal x * acc) 0
      rw [toReal_add, toReal_mul, HexRealRootsMathlib.toReal_ofInt, toReal_horner_foldr x cs]

/-- **Evaluation correspondence.** The exact dyadic Horner evaluation of an
integer polynomial, cast to `ℝ`, agrees with the Mathlib evaluation of its real
cast at the real value of the dyadic point. -/
theorem toReal_evalDyadic (q : Hex.ZPoly) (x : Dyadic) :
    Dyadic.toReal (q.evalDyadic x) = (toPolyℝ q).eval (Dyadic.toReal x) := by
  have hcoeffs : hornerPoly (q.toArray.toList.map (Int.cast : ℤ → ℝ)) = toPolyℝ q := by
    ext n
    rw [coeff_hornerPoly, getD_map_intCast, coeff_toPolyℝ]
    congr 1
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
    have h := Hex.DensePoly.toArray_getD q n
    rw [Array.getD_eq_getD_getElem?] at h
    exact h
  unfold Hex.ZPoly.evalDyadic
  rw [← Array.foldr_toList, toReal_horner_foldr, ← eval_hornerPoly, hcoeffs]

/-- **Sign correspondence.** The exact integer sign of a dyadic value has, as a
real number, the same `SignType.sign` as the real value of the dyadic. -/
theorem sign_dyadicSign (d : Dyadic) :
    SignType.sign ((Hex.dyadicSign d : ℝ)) = SignType.sign (Dyadic.toReal d) := by
  cases d with
  | zero => simp [Hex.dyadicSign]
  | ofOdd n k hn =>
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      have h2 : (0 : ℝ) < 2 ^ (-k) := by positivity
      have htr : Dyadic.toReal (Dyadic.ofOdd n k hn) = (n : ℝ) * 2 ^ (-k) := by
        unfold Dyadic.toReal
        rw [Dyadic.toRat_ofOdd_eq_mul_two_pow]; push_cast; ring
      rw [htr, Hex.dyadicSign]
      by_cases hlt : n < 0
      · rw [ite_eq_left hlt]
        rw [show ((-1 : Int) : ℝ) = -1 by norm_num,
          sign_neg (mul_neg_of_neg_of_pos (by exact_mod_cast hlt) h2), sign_neg (by norm_num)]
      · have hpos : 0 < n := lt_of_le_of_ne (by omega) (Ne.symm hn0)
        rw [ite_eq_right hlt]
        rw [show ((1 : Int) : ℝ) = 1 by norm_num,
          sign_pos (mul_pos (by exact_mod_cast hpos) h2), sign_pos (by norm_num)]

/-- Exact dyadic Horner evaluation has zero sign exactly at a real root. -/
theorem evalSign_zero_iff (p : Hex.ZPoly) (x : Dyadic) :
    Hex.dyadicSign (p.evalDyadic x) = 0 ↔
      (toPolyℝ p).IsRoot (Dyadic.toReal x) := by
  have hs : SignType.sign ((Hex.dyadicSign (p.evalDyadic x) : ℝ)) =
      SignType.sign (Dyadic.toReal (p.evalDyadic x)) := sign_dyadicSign _
  constructor
  · intro h
    rw [h] at hs
    simp only [Int.cast_zero, sign_zero] at hs
    have h0 : Dyadic.toReal (p.evalDyadic x) = 0 := sign_eq_zero_iff.mp hs.symm
    rw [toReal_evalDyadic] at h0
    exact h0
  · intro h
    have h0 : Dyadic.toReal (p.evalDyadic x) = 0 := by
      rw [toReal_evalDyadic]
      exact h
    rw [h0] at hs
    simp only [sign_zero] at hs
    have hz : ((Hex.dyadicSign (p.evalDyadic x) : Int) : ℝ) = 0 :=
      sign_eq_zero_iff.mp hs
    exact_mod_cast hz

/-- Filtering the real casts by nonzero commutes with filtering the integers by
nonzero: casting to `ℝ` neither creates nor destroys zero entries. -/
private theorem filter_map_ne_zero (l : List Int) :
    (l.map (Int.cast : ℤ → ℝ)).filter (fun v => decide (v ≠ 0))
      = (l.filter (· != 0)).map (Int.cast : ℤ → ℝ) := by
  have hp : ((fun v => decide (v ≠ 0)) ∘ (Int.cast : ℤ → ℝ)) = (· != 0) := by
    funext i
    by_cases h : i = 0 <;> simp [Function.comp_apply, h]
  rw [List.filter_map, hp]

/-- Two nonzero leading entries: `signVar` peels one sign-change decision and
recurses. Phrased through the public `Hex.signVar` (the internal `go` recursor is
module-private), using that a nonzero head survives the zero-filter. -/
private theorem signVar_cons_cons {a b : Int} (rest : List Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    Hex.signVar (a :: b :: rest)
      = (if a * b < 0 then 1 else 0) + Hex.signVar (b :: rest) := by
  have fa : (a :: b :: rest).filter (· != 0) = a :: b :: rest.filter (· != 0) := by
    rw [List.filter_cons, ite_eq_left (by simpa using ha),
      List.filter_cons, ite_eq_left (by simpa using hb)]
  have fb : (b :: rest).filter (· != 0) = b :: rest.filter (· != 0) := by
    rw [List.filter_cons, ite_eq_left (by simpa using hb)]
  unfold Hex.signVar
  rw [fa, fb]
  rfl

/-- On a zero-free integer list, the executable count matches the abstract real
count of the casts. Structural recursion peeling two elements; each retained
entry is nonzero, so the executable and real sign tests agree pairwise. -/
private theorem signVar_zeroFree : ∀ m : List Int, (∀ x ∈ m, x ≠ 0) →
    Hex.signVar m = Sturm.countSignChanges (m.map (Int.cast : ℤ → ℝ))
  | [], _ => rfl
  | [a], ha => by
      have ha0 : a ≠ 0 := ha a (by simp)
      unfold Hex.signVar
      rw [List.filter_cons, ite_eq_left (by simpa using ha0), List.filter_nil]
      rfl
  | a :: b :: rest, hne => by
      have ha : a ≠ 0 := hne a (by simp)
      have hb : b ≠ 0 := hne b (by simp)
      have hbne : ∀ x ∈ b :: rest, x ≠ 0 := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      rw [signVar_cons_cons rest ha hb, signVar_zeroFree (b :: rest) hbne,
        List.map_cons, List.map_cons, List.map_cons, Sturm.countSignChanges_cons_cons]
      congr 1
      have hcast : (a : ℝ) * (b : ℝ) = ((a * b : Int) : ℝ) := by push_cast; ring
      rw [hcast]
      by_cases h : a * b < 0
      · rw [ite_eq_left h, ite_eq_left (by exact_mod_cast h)]
      · rw [ite_eq_right h, ite_eq_right (by exact_mod_cast h)]

/-- `signVar` reads only the zero-filtered list, so it is unchanged by
pre-filtering out zeros. -/
private theorem signVar_filter (l : List Int) :
    Hex.signVar l = Hex.signVar (l.filter (· != 0)) := by
  unfold Hex.signVar
  rw [List.filter_filter]
  simp only [Bool.and_self]

/-- **Sign-variation count correspondence.** The executable integer
sign-variation count of a list equals the abstract real sign-variation count of
the list cast to `ℝ`. -/
theorem signVar_eq (l : List Int) :
    Hex.signVar l = Sturm.signVariations (l.map (Int.cast : ℤ → ℝ)) := by
  rw [Sturm.signVariations, filter_map_ne_zero, signVar_filter]
  exact signVar_zeroFree (l.filter (· != 0))
    (fun x hx => by simpa using (List.mem_filter.mp hx).2)

/-- **Sign-variation correspondence.** The executable Sturm sign-variation count
of a chain at a dyadic point equals the abstract `Sturm.sturmVar` of the mapped
real chain at the real value of the point. Positive scaling of chain elements is
irrelevant: `sturmVar` reads only signs, which the exact dyadic evaluation and
the Mathlib evaluation agree on. -/
theorem sturmVarAt_eq (chain : Array Hex.ZPoly) (x : Dyadic) :
    Hex.sturmVarAt chain x
      = Sturm.sturmVar (chain.toList.map toPolyℝ) (Dyadic.toReal x) := by
  rw [Hex.sturmVarAt, signVar_eq, Sturm.sturmVar]
  apply Sturm.signVariations_congr
  simp only [List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q _
  rw [Function.comp_apply, Function.comp_apply, sign_dyadicSign, toReal_evalDyadic]

end

end HexRealRootsMathlib
