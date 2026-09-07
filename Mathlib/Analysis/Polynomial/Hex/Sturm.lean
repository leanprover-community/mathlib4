/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import HexPolyZ
public import Mathlib.Algebra.Polynomial.Hex.Euclid
public import Mathlib.Algebra.Polynomial.Hex.Squarefree
public import Mathlib.Analysis.Polynomial.Sturm.Basic
public import Mathlib.Analysis.Polynomial.Hex.SignVariations
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
# Root counts for executable Sturm chains

The executable signed pseudo-remainder sequence satisfies the axioms of a Sturm
chain over `Polynomial ℝ`. Consequently, the executable interval and whole-line
root counts agree with the corresponding Mathlib root counts.
-/

public section

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-! # `spem` correspondence: the sign-managed pseudo-remainder over `ℝ`

The executable `spem f g` is a **positive integer multiple** of the field
remainder `f mod g`. We prove the underlying Euclidean-division relation over
`ℝ`: there is a positive real `c` and a quotient `Q` with
`C c * toPolyℝ f = Q * toPolyℝ g + toPolyℝ (spem f g)`, together with the
degree drop that makes `toPolyℝ (spem f g)` the genuine remainder. This is the
identity the chain-axiom proofs consume: at a zero `x` of `g`, the relation
collapses to `c * f(x) = (spem f g)(x)`, fixing the sign of the next chain
element against the previous one. -/

/-- `toPolynomial` turns the executable scalar multiply into `C`-multiplication. -/
theorem toPolynomial_scale {R : Type*} [CommRing R] [DecidableEq R]
    (c : R) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p)
      = Polynomial.C c * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, HexPolyMathlib.coeff_toPolynomial]

/-- `toPolynomial` turns the executable `x^k` shift into `X^k`-multiplication. -/
theorem toPolynomial_shift {R : Type*} [CommRing R] [DecidableEq R]
    (k : Nat) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.shift k p)
      = Polynomial.X ^ k * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_shift, mul_comm,
    Polynomial.coeff_mul_X_pow']
  by_cases h : k ≤ n
  · rw [ite_eq_right (by omega), ite_eq_left h, HexPolyMathlib.coeff_toPolynomial]
  · rw [ite_eq_left (by omega), ite_eq_right h]; rfl

/-- The real cast of a scalar multiple. -/
theorem toPolyℝ_scale (c : Int) (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.scale c p) = Polynomial.C (c : ℝ) * toPolyℝ p := by
  ext n
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, coeff_toPolyℝ]
  push_cast; ring

/-- The real cast is additive. -/
theorem toPolyℝ_add (p q : Hex.ZPoly) :
    toPolyℝ (p + q) = toPolyℝ p + toPolyℝ q := by
  change (HexPolyMathlib.toPolynomial (p + q)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_add, Polynomial.map_add]

/-- The real cast of an `x^k` shift. -/
theorem toPolyℝ_shift (k : Nat) (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.shift k p) = Polynomial.X ^ k * toPolyℝ p := by
  ext n
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_shift, mul_comm, Polynomial.coeff_mul_X_pow']
  by_cases h : k ≤ n
  · rw [ite_eq_right (show ¬ n < k by omega), ite_eq_left h, coeff_toPolyℝ]
  · rw [ite_eq_left (show n < k by omega), ite_eq_right h]; exact Int.cast_zero

/-- The real cast of a difference. -/
theorem toPolyℝ_sub (p q : Hex.ZPoly) :
    toPolyℝ (p - q) = toPolyℝ p - toPolyℝ q := by
  change (HexPolyMathlib.toPolynomial (p - q)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_sub, Polynomial.map_sub]

/-- The real cast preserves the leading coefficient. -/
theorem leadingCoeff_toPolyℝ (p : Hex.ZPoly) :
    (toPolyℝ p).leadingCoeff = (p.leadingCoeff : ℝ) := by
  rw [toPolyℝ, Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective_int (Int.castRingHom ℝ)), HexPolyMathlib.leadingCoeff_toPolynomial]
  simp

/-- **The `spemStep` identity over `ℝ`.** One reduction step is `|lc g|` times
the remainder minus a scaled shift of `g`, so its cast splits as a `C`-multiple
of `toPolyℝ r` minus a `C`-multiple of `X^k · toPolyℝ g`. -/
private theorem toPolyℝ_spemStep (g r : Hex.ZPoly) :
    toPolyℝ (Hex.ZPoly.spemStep g r) =
      Polynomial.C ((if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff : Int) : ℝ)
          * toPolyℝ r
        - Polynomial.C ((if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff : Int) : ℝ)
          * (Polynomial.X ^ ((r.degree?).getD 0 - (g.degree?).getD 0) * toPolyℝ g) := by
  have hstep : Hex.ZPoly.spemStep g r =
      Hex.DensePoly.scale (if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff) r
        - Hex.DensePoly.scale (if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff)
            (Hex.DensePoly.shift ((r.degree?).getD 0 - (g.degree?).getD 0) g) := rfl
  rw [hstep, toPolyℝ_sub, toPolyℝ_scale, toPolyℝ_scale, toPolyℝ_shift]

/-- **The `spemAux` division relation over `ℝ`.** For a divisor `g` with nonzero
leading coefficient, the reduction loop produces a positive `C`-multiple of the
input `r` differing from a polynomial multiple of `g`: there is `c > 0` and a
quotient `Q` with `C c · toPolyℝ r = Q · toPolyℝ g + toPolyℝ (spemAux g fuel r)`.
Induction on the structural fuel; each `spemStep` peels one `|lc g|` factor. -/
private theorem spemAux_relate (g : Hex.ZPoly) (hg : g.leadingCoeff ≠ 0) :
    ∀ (fuel : ℕ) (r : Hex.ZPoly),
      ∃ (c : ℝ) (Q : Polynomial ℝ), 0 < c ∧
        Polynomial.C c * toPolyℝ r
          = Q * toPolyℝ g + toPolyℝ (Hex.ZPoly.spemAux g fuel r) := by
  have habs : (0:ℝ) <
      ((if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff : Int) : ℝ) := by
    have : (0:Int) < (if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff) := by
      split_ifs with h <;> omega
    exact_mod_cast this
  intro fuel
  induction fuel with
  | zero =>
      intro r
      exact ⟨1, 0, one_pos, by
        rw [show Hex.ZPoly.spemAux g 0 r = r from rfl]; simp⟩
  | succ fuel ih =>
      intro r
      have hunf : Hex.ZPoly.spemAux g (fuel + 1) r =
          (if r.isZero then r
           else if (r.degree?).getD 0 < (g.degree?).getD 0 then r
           else Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r)) := rfl
      by_cases h0 : r.isZero
      · exact ⟨1, 0, one_pos, by rw [hunf, ite_eq_left h0]; simp⟩
      · by_cases h1 : (r.degree?).getD 0 < (g.degree?).getD 0
        · exact ⟨1, 0, one_pos, by rw [hunf, ite_eq_right h0, ite_eq_left h1]; simp⟩
        · obtain ⟨c', Q', hc', hrel'⟩ := ih (Hex.ZPoly.spemStep g r)
          refine ⟨c' * ((if g.leadingCoeff < 0 then -g.leadingCoeff
                    else g.leadingCoeff : Int) : ℝ),
              Polynomial.C c' * Polynomial.C ((if g.leadingCoeff < 0 then -r.leadingCoeff
                    else r.leadingCoeff : Int) : ℝ)
                * Polynomial.X ^ ((r.degree?).getD 0 - (g.degree?).getD 0) + Q',
              mul_pos hc' habs, ?_⟩
          rw [hunf, ite_eq_right h0, ite_eq_right h1, Polynomial.C_mul]
          have key : toPolyℝ (Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r))
              = Polynomial.C c' * toPolyℝ (Hex.ZPoly.spemStep g r) - Q' * toPolyℝ g := by
            rw [hrel']; ring
          rw [key, toPolyℝ_spemStep]
          ring

/-- **The `spem` correspondence.** For a nonconstant divisor `g` (positive
degree, hence nonzero leading coefficient), the executable sign-managed
pseudo-remainder `spem f g` is a positive real multiple of the field remainder
of `f` by `g`: there is `c > 0` and a quotient `Q` with
`C c · toPolyℝ f = Q · toPolyℝ g + toPolyℝ (spem f g)`. Evaluating at a zero `x`
of `g` collapses this to `c · f(x) = (spem f g)(x)`, the sign-transfer identity
the chain axioms consume. -/
theorem toPolyℝ_spem (f g : Hex.ZPoly) (hg : g.leadingCoeff ≠ 0)
    (hdeg : 1 ≤ (g.degree?).getD 0) :
    ∃ (c : ℝ) (Q : Polynomial ℝ), 0 < c ∧
      Polynomial.C c * toPolyℝ f = Q * toPolyℝ g + toPolyℝ (Hex.ZPoly.spem f g) := by
  obtain ⟨m, hm⟩ : ∃ m, g.degree? = some m := by
    cases h : g.degree? with
    | none => rw [h] at hdeg; simp at hdeg
    | some m => exact ⟨m, rfl⟩
  have hm1 : m ≠ 0 := by rw [hm] at hdeg; simp only [Option.getD_some] at hdeg; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hspem : Hex.ZPoly.spem f g = Hex.ZPoly.spemAux g f.size f := by
    unfold Hex.ZPoly.spem; rw [hm]; rfl
  rw [hspem]
  exact spemAux_relate g hg f.size f

/-! # Cast and executable-layer helpers for the chain axioms -/

/-- The real cast of a negation. -/
theorem toPolyℝ_neg (p : Hex.ZPoly) : toPolyℝ (-p) = -(toPolyℝ p) := by
  change (HexPolyMathlib.toPolynomial (-p)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_neg, Polynomial.map_neg]

/-- The real cast is multiplicative. -/
theorem toPolyℝ_mul (p q : Hex.ZPoly) :
    toPolyℝ (p * q) = toPolyℝ p * toPolyℝ q := by
  change (HexPolyZMathlib.toPolynomial (p * q)).map (Int.castRingHom ℝ) = _
  rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul]

/-- The real cast of the zero polynomial. -/
@[simp] theorem toPolyℝ_zero : toPolyℝ 0 = 0 := by
  change (HexPolyMathlib.toPolynomial 0).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]

/-- The real cast is zero exactly when the executable polynomial is. -/
theorem toPolyℝ_eq_zero_iff {p : Hex.ZPoly} : toPolyℝ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h2 : HexPolyMathlib.toPolynomial p = 0 :=
      (Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℝ))).mp h
    have := congrArg HexPolyMathlib.ofPolynomial h2
    simpa using this
  · rintro rfl; exact toPolyℝ_zero

/-- A polynomial whose stored size is zero is the zero polynomial. -/
private theorem eq_zero_of_size_eq_zero {p : Hex.ZPoly} (h : p.size = 0) : p = 0 := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_zero]
  exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)

/-- The Boolean zero test decides equality with the zero polynomial. -/
private theorem isZero_iff_eq_zero {p : Hex.ZPoly} : p.isZero = true ↔ p = 0 := by
  rw [Hex.DensePoly.isZero_eq_true_iff]
  exact ⟨fun h => eq_zero_of_size_eq_zero h, fun h => by subst h; rfl⟩

/-- A nonzero executable polynomial has a `some` degree, namely `size - 1`. -/
private theorem degree?_of_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    p.degree? = some (p.size - 1) := by
  refine Hex.DensePoly.degree?_eq_some_of_pos_size p ?_
  rcases Nat.eq_zero_or_pos p.size with h | h
  · exact absurd (eq_zero_of_size_eq_zero h) hp
  · exact h

/-- The leading coefficient of a nonzero executable polynomial is nonzero. -/
private theorem leadingCoeff_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    p.leadingCoeff ≠ 0 := by
  refine Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size p ?_
  rcases Nat.eq_zero_or_pos p.size with h | h
  · exact absurd (eq_zero_of_size_eq_zero h) hp
  · exact h

/-- The real value of the content of a nonzero polynomial is positive: the
executable content is a nonnegative integer, nonzero for nonzero input. -/
theorem content_real_pos {p : Hex.ZPoly} (hp : p ≠ 0) :
    (0 : ℝ) < ((Hex.ZPoly.content p : Int) : ℝ) := by
  have hne : Hex.ZPoly.content p ≠ 0 := HexPolyZMathlib.content_ne_zero p hp
  have hnonneg : (0 : Int) ≤ Hex.ZPoly.content p := Int.natCast_nonneg _
  exact_mod_cast lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Gauss decomposition of the real cast: a polynomial is its (positive integer)
content times its primitive part. -/
theorem toPolyℝ_eq_C_content_mul_primitivePart (p : Hex.ZPoly) :
    toPolyℝ p = Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ)
      * toPolyℝ (Hex.ZPoly.primitivePart p) := by
  change (toPolynomial p).map (Int.castRingHom ℝ) = _
  rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart p, Polynomial.map_mul,
    Polynomial.map_C]
  rfl

/-- The primitive part of a nonzero polynomial is nonzero. -/
theorem primitivePart_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    Hex.ZPoly.primitivePart p ≠ 0 := by
  intro h
  apply hp
  rw [← toPolyℝ_eq_zero_iff, toPolyℝ_eq_C_content_mul_primitivePart p, h, toPolyℝ_zero,
    mul_zero]

/-- The real cast commutes with the derivative. -/
theorem toPolyℝ_derivative (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.derivative p) = Polynomial.derivative (toPolyℝ p) := by
  change (HexPolyMathlib.toPolynomial (Hex.DensePoly.derivative p)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_map]

/-- `spem` by a nonzero constant is zero (the junk-value convention). -/
private theorem spem_of_degree_zero (f : Hex.ZPoly) {g : Hex.ZPoly} (hg : g ≠ 0)
    (hdeg : (g.degree?).getD 0 = 0) : Hex.ZPoly.spem f g = 0 := by
  have hsome := degree?_of_ne_zero hg
  have hz : g.size - 1 = 0 := by rw [hsome] at hdeg; simpa using hdeg
  have hg0 : g.degree? = some 0 := by rw [hsome, hz]
  unfold Hex.ZPoly.spem
  rw [hg0]
  rfl

/-! # Degree control: the reduction loop terminates before its fuel runs out -/

/-- One `spemStep` strictly drops the degree (or reaches zero): the sign
management makes the two leading terms cancel exactly. Proved over `ℝ` via
`Polynomial.degree_sub_lt_left` and transferred back through `natDegree_toPolyℝ`. -/
private theorem spemStep_degree_lt {g r : Hex.ZPoly} (hg : g ≠ 0) (hr : r ≠ 0)
    (hge : (g.degree?).getD 0 ≤ (r.degree?).getD 0) :
    Hex.ZPoly.spemStep g r = 0 ∨
      ((Hex.ZPoly.spemStep g r).degree?).getD 0 < (r.degree?).getD 0 := by
  by_cases hz : Hex.ZPoly.spemStep g r = 0
  · exact Or.inl hz
  refine Or.inr ?_
  set a : Int := if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff with ha
  set b : Int := if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff with hb
  set k : ℕ := (r.degree?).getD 0 - (g.degree?).getD 0 with hk
  have hlcg : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hg
  have hlcr : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hr
  have ha0 : (a : ℝ) ≠ 0 := by
    have : a ≠ 0 := by rw [ha]; split_ifs with h <;> omega
    exact_mod_cast this
  have hb0 : (b : ℝ) ≠ 0 := by
    have : b ≠ 0 := by rw [hb]; split_ifs with h <;> omega
    exact_mod_cast this
  have hPr0 : toPolyℝ r ≠ 0 := fun h => hr (toPolyℝ_eq_zero_iff.mp h)
  have hPg0 : toPolyℝ g ≠ 0 := fun h => hg (toPolyℝ_eq_zero_iff.mp h)
  set A := Polynomial.C (a : ℝ) * toPolyℝ r with hA
  set B := Polynomial.C (b : ℝ) * (Polynomial.X ^ k * toPolyℝ g) with hB
  have hstep : toPolyℝ (Hex.ZPoly.spemStep g r) = A - B := toPolyℝ_spemStep g r
  have hdegA : A.degree = (toPolyℝ r).degree := by
    rw [hA, Polynomial.degree_mul, Polynomial.degree_C ha0, zero_add]
  have hdegB : B.degree = (toPolyℝ r).degree := by
    rw [hB, Polynomial.degree_mul, Polynomial.degree_C hb0, zero_add, Polynomial.degree_mul,
      Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hPg0,
      Polynomial.degree_eq_natDegree hPr0, natDegree_toPolyℝ, natDegree_toPolyℝ]
    have hkg : k + (g.degree?).getD 0 = (r.degree?).getD 0 := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) hkg
  have hlcA : A.leadingCoeff = (a : ℝ) * (r.leadingCoeff : ℝ) := by
    rw [hA, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, leadingCoeff_toPolyℝ]
  have hlcB : B.leadingCoeff = (b : ℝ) * (g.leadingCoeff : ℝ) := by
    rw [hB, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_pow, one_mul,
      leadingCoeff_toPolyℝ]
  have hlceq : A.leadingCoeff = B.leadingCoeff := by
    rw [hlcA, hlcB, ha, hb]
    split_ifs with h <;> (push_cast; ring)
  have hA0 : A ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hPr0
  have hlt : (toPolyℝ (Hex.ZPoly.spemStep g r)).degree < (toPolyℝ r).degree := by
    rw [hstep, ← hdegA]
    exact Polynomial.degree_sub_lt_left (hdegA.trans hdegB.symm) hA0 hlceq
  have hstep0 : toPolyℝ (Hex.ZPoly.spemStep g r) ≠ 0 :=
    fun h => hz (toPolyℝ_eq_zero_iff.mp h)
  have hnat := Polynomial.natDegree_lt_natDegree hstep0 hlt
  rwa [natDegree_toPolyℝ, natDegree_toPolyℝ] at hnat

/-- `spemAux` with sufficient fuel lands strictly below the divisor's degree
(or at zero): the fuel bound `deg r < fuel + deg g` regenerates at each step
because the degree strictly drops. -/
private theorem spemAux_degree {g : Hex.ZPoly} (hg : g ≠ 0)
    (hg1 : 1 ≤ (g.degree?).getD 0) :
    ∀ (fuel : ℕ) (r : Hex.ZPoly), (r.degree?).getD 0 < fuel + (g.degree?).getD 0 →
      Hex.ZPoly.spemAux g fuel r = 0 ∨
        ((Hex.ZPoly.spemAux g fuel r).degree?).getD 0 < (g.degree?).getD 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro r hbound
      right
      rw [show Hex.ZPoly.spemAux g 0 r = r from rfl]
      omega
  | succ fuel ih =>
      intro r hbound
      have hunf : Hex.ZPoly.spemAux g (fuel + 1) r =
          (if r.isZero then r
           else if (r.degree?).getD 0 < (g.degree?).getD 0 then r
           else Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r)) := rfl
      by_cases h0 : r.isZero
      · left; rw [hunf, ite_eq_left h0]; exact isZero_iff_eq_zero.mp h0
      · by_cases h1 : (r.degree?).getD 0 < (g.degree?).getD 0
        · right; rw [hunf, ite_eq_right h0, ite_eq_left h1]; exact h1
        · rw [hunf, ite_eq_right h0, ite_eq_right h1]
          have hr : r ≠ 0 := fun h => h0 (isZero_iff_eq_zero.mpr h)
          have hge : (g.degree?).getD 0 ≤ (r.degree?).getD 0 := not_lt.mp h1
          rcases spemStep_degree_lt hg hr hge with hz | hlt
          · apply ih
            rw [hz]
            simp only [Hex.DensePoly.degree?_zero_getD]
            omega
          · apply ih
            omega

/-- The top-level `spem` lands strictly below the divisor's degree (or at zero)
for a nonconstant divisor: the built-in fuel `f.size` always suffices. -/
private theorem spem_degree {f g : Hex.ZPoly} (hg : g ≠ 0)
    (hg1 : 1 ≤ (g.degree?).getD 0) :
    Hex.ZPoly.spem f g = 0 ∨
      ((Hex.ZPoly.spem f g).degree?).getD 0 < (g.degree?).getD 0 := by
  obtain ⟨m, hm⟩ : ∃ m, g.degree? = some m := ⟨g.size - 1, degree?_of_ne_zero hg⟩
  have hm1 : m ≠ 0 := by rw [hm] at hg1; simp only [Option.getD_some] at hg1; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hspem : Hex.ZPoly.spem f g = Hex.ZPoly.spemAux g f.size f := by
    unfold Hex.ZPoly.spem; rw [hm]; rfl
  rw [hspem]
  apply spemAux_degree hg hg1
  by_cases hf : f = 0
  · subst hf
    simp only [Hex.DensePoly.degree?_zero_getD]
    omega
  · rw [degree?_of_ne_zero hf]
    simp only [Option.getD_some]
    have hpos : 0 < f.size := by
      rcases Nat.eq_zero_or_pos f.size with h | h
      · exact absurd (eq_zero_of_size_eq_zero h) hf
      · exact h
    omega

/-! # Squarefreeness and root transfers to `ℝ` -/

/-- **Squarefree-to-separable transfer.** If the rational cast `toPolyℚ p` is
squarefree, its real cast `toPolyℝ p` is separable. Over the perfect field `ℚ`,
squarefree means separable, and separability is preserved by the field
extension `ℚ → ℝ`. -/
theorem separable_toPolyℝ (p : Hex.ZPoly) (hsq : Squarefree (toPolyℚ p)) :
    (toPolyℝ p).Separable := by
  have hsep : (toPolyℚ p).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext_int _ _
  have hmap : toPolyℝ p = (toPolyℚ p).map (algebraMap ℚ ℝ) := by
    change (toPolynomial p).map (Int.castRingHom ℝ)
      = ((toPolynomial p).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)
    rw [Polynomial.map_map, hcomp]
  rw [hmap]; exact hsep.map

/-- The real cast of a nonzero `p` is the positive-content multiple of the cast
of its primitive part, so the two share exactly the same real roots. -/
theorem roots_toPolyℝ_eq_primitivePart (p : Hex.ZPoly) (hp : p ≠ 0) :
    (toPolyℝ p).roots = (toPolyℝ (Hex.ZPoly.primitivePart p)).roots := by
  rw [toPolyℝ_eq_C_content_mul_primitivePart p,
    Polynomial.roots_C_mul _ (ne_of_gt (content_real_pos hp))]

/-! # Structure of the executable chain -/

/-- The tail the chain-extension loop appends past its two seeds: pure-list
mirror of `sturmChainAux` (which threads an `Array` accumulator). -/
private def chainList : ℕ → Hex.ZPoly → Hex.ZPoly → List Hex.ZPoly
  | 0, _, _ => []
  | fuel + 1, prev, cur =>
      if (Hex.ZPoly.spem prev cur).isZero then []
      else -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))
        :: chainList fuel cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))

/-- The chain-extension loop only appends: its result is the accumulator
followed by the pure-list tail `chainList`. -/
private theorem sturmChainAux_toList (fuel : ℕ) (prev cur : Hex.ZPoly)
    (acc : Array Hex.ZPoly) :
    (Hex.ZPoly.sturmChainAux fuel prev cur acc).toList
      = acc.toList ++ chainList fuel prev cur := by
  induction fuel generalizing prev cur acc with
  | zero =>
      rw [show Hex.ZPoly.sturmChainAux 0 prev cur acc = acc from rfl, chainList,
        List.append_nil]
  | succ fuel ih =>
      have hunf : Hex.ZPoly.sturmChainAux (fuel + 1) prev cur acc =
          (if (Hex.ZPoly.spem prev cur).isZero then acc
           else Hex.ZPoly.sturmChainAux fuel cur
                  (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
                  (acc.push (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))))) := rfl
      rw [hunf, chainList]
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [ite_eq_left h, ite_eq_left h, List.append_nil]
      · rw [ite_eq_right h, ite_eq_right h, ih, Array.toList_push, List.append_assoc,
          List.cons_append, List.nil_append]

/-- For a positive-degree `p`, the executable Sturm chain is
`primitivePart p :: primitivePart p' :: chainList …`. -/
private theorem sturmChain_toList (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    (Hex.ZPoly.sturmChain p).toList =
      Hex.ZPoly.primitivePart p
        :: Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)
        :: chainList p.size (Hex.ZPoly.primitivePart p)
             (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)) := by
  obtain ⟨m, hm⟩ : ∃ m, p.degree? = some m := by
    cases h : p.degree? with
    | none => rw [h] at hp; simp at hp
    | some m => exact ⟨m, rfl⟩
  have hm1 : m ≠ 0 := by rw [hm] at hp; simp only [Option.getD_some] at hp; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hchain : Hex.ZPoly.sturmChain p =
      Hex.ZPoly.sturmChainAux p.size (Hex.ZPoly.primitivePart p)
        (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))
        #[Hex.ZPoly.primitivePart p,
          Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)] := by
    unfold Hex.ZPoly.sturmChain; rw [hm]; rfl
  rw [hchain, sturmChainAux_toList]
  rfl

/-- **Head of the mapped chain.** For a positive-degree `p`, the real-cast Sturm
chain has head `toPolyℝ (primitivePart p)`, matching the `IsSturmChain.head`
field (stated at the primitive part, per the design note: the executable chain's
first element is `primitivePart p`, not `p`, since the content is stripped). -/
theorem sturmChain_map_head? (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    ((Hex.ZPoly.sturmChain p).toList.map toPolyℝ).head?
      = some (toPolyℝ (Hex.ZPoly.primitivePart p)) := by
  rw [sturmChain_toList p hp]; rfl

/-- **Nonemptiness of the mapped chain** for a positive-degree `p`. -/
theorem sturmChain_map_ne_nil (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    (Hex.ZPoly.sturmChain p).toList.map toPolyℝ ≠ [] := by
  rw [sturmChain_toList p hp]; simp

/-! # The per-step chain relation -/

/-- **One chain step over `ℝ`.** When the loop pushes a new element past the
pair `(prev, cur)` (that is, `spem prev cur ≠ 0`), the three consecutive
elements satisfy `C c · prev = Q · cur − C k · next` with `c, k > 0`, where
`next = −primitivePart (spem prev cur)` is exactly the pushed element. At a
zero `x` of `cur` this collapses to `c · prev(x) = −k · next(x)`: the flanking
neighbours of a vanishing interior element have opposite signs. -/
private theorem chain_step {prev cur : Hex.ZPoly} (hcur : cur ≠ 0)
    (hr : Hex.ZPoly.spem prev cur ≠ 0) :
    ∃ (c k : ℝ) (Q : Polynomial ℝ), 0 < c ∧ 0 < k ∧
      Polynomial.C c * toPolyℝ prev
        = Q * toPolyℝ cur - Polynomial.C k
            * toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))) := by
  have hdeg1 : 1 ≤ (cur.degree?).getD 0 := by
    by_contra h
    exact hr (spem_of_degree_zero prev hcur (by omega))
  obtain ⟨c, Q, hc, hrel⟩ := toPolyℝ_spem prev cur (leadingCoeff_ne_zero hcur) hdeg1
  set r := Hex.ZPoly.spem prev cur with hrdef
  refine ⟨c, ((Hex.ZPoly.content r : Int) : ℝ), Q, hc, content_real_pos hr, ?_⟩
  rw [hrel, toPolyℝ_neg, toPolyℝ_eq_C_content_mul_primitivePart r]
  ring

/-- **Coprimality propagates down the chain.** The three-term relation
`C c · a = Q · b − C k · c'` transports `IsCoprime a b` to `IsCoprime b c'`:
any Bezout combination for `(a, b)` rewrites into one for `(b, c')`. -/
private theorem coprime_step {a b c' : Polynomial ℝ} {c₀ k : ℝ} {Q : Polynomial ℝ}
    (hc₀ : c₀ ≠ 0)
    (hrel : Polynomial.C c₀ * a = Q * b - Polynomial.C k * c')
    (h : IsCoprime a b) : IsCoprime b c' := by
  obtain ⟨u, v, huv⟩ := h
  have hCc : Polynomial.C c₀⁻¹ * Polynomial.C c₀ = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hc₀, Polynomial.C_1]
  refine ⟨u * Polynomial.C c₀⁻¹ * Q + v, -(u * Polynomial.C c₀⁻¹ * Polynomial.C k), ?_⟩
  calc (u * Polynomial.C c₀⁻¹ * Q + v) * b
        + -(u * Polynomial.C c₀⁻¹ * Polynomial.C k) * c'
      = u * Polynomial.C c₀⁻¹ * (Q * b - Polynomial.C k * c') + v * b := by ring
    _ = u * Polynomial.C c₀⁻¹ * (Polynomial.C c₀ * a) + v * b := by rw [← hrel]
    _ = u * ((Polynomial.C c₀⁻¹ * Polynomial.C c₀) * a) + v * b := by ring
    _ = u * a + v * b := by rw [hCc, one_mul]
    _ = 1 := huv

/-- The negated primitive part of a nonzero polynomial is nonzero. -/
private theorem neg_primitivePart_ne_zero {r : Hex.ZPoly} (hr : r ≠ 0) :
    -(Hex.ZPoly.primitivePart r) ≠ 0 := by
  intro hh
  have h2 : toPolyℝ (-(Hex.ZPoly.primitivePart r)) = 0 := by rw [hh, toPolyℝ_zero]
  rw [toPolyℝ_neg, neg_eq_zero, toPolyℝ_eq_zero_iff] at h2
  exact primitivePart_ne_zero hr h2

/-- A nonzero `spem prev cur` forces `cur` to be nonconstant (a constant
divisor returns the junk value `0`). -/
private theorem one_le_degree_of_spem_ne_zero {prev cur : Hex.ZPoly} (hcur : cur ≠ 0)
    (hr : Hex.ZPoly.spem prev cur ≠ 0) : 1 ≤ (cur.degree?).getD 0 := by
  by_contra hh
  exact hr (spem_of_degree_zero prev hcur (by omega))

/-! # The chain-tail inductions: the four analytic `IsSturmChain` fields -/

/-- Every element of the extended chain is nonzero: the loop pushes only
negated primitive parts of nonzero pseudo-remainders. -/
private theorem chainList_nonzero :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), prev ≠ 0 → cur ≠ 0 →
      ∀ q ∈ prev :: cur :: chainList fuel prev cur, q ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur hprev hcur q hq
      rw [chainList] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hprev
      · exact hcur
  | succ fuel ih =>
      intro prev cur hprev hcur q hq
      rw [chainList] at hq
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [ite_eq_left h] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hprev
        · exact hcur
      · rw [ite_eq_right h] at hq
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hprev
        · exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))) hcur
            (neg_primitivePart_ne_zero hr) q hq'

/-- **The three-term chain relation, indexed.** Any three consecutive elements
`a, b, c` of the extended chain satisfy `C c₀ · a = Q · b − C k · c` over `ℝ`
with `c₀, k > 0`. -/
private theorem chainList_triples :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      ∀ (i : ℕ) (a b c : Hex.ZPoly),
        (prev :: cur :: chainList fuel prev cur)[i]? = some a →
        (prev :: cur :: chainList fuel prev cur)[i + 1]? = some b →
        (prev :: cur :: chainList fuel prev cur)[i + 2]? = some c →
        ∃ (c₀ k : ℝ) (Q : Polynomial ℝ), 0 < c₀ ∧ 0 < k ∧
          Polynomial.C c₀ * toPolyℝ a = Q * toPolyℝ b - Polynomial.C k * toPolyℝ c := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur _ i a b c _ _ hc
      rw [chainList, List.getElem?_cons_succ, List.getElem?_cons_succ] at hc
      simp at hc
  | succ fuel ih =>
      intro prev cur hcur i a b c ha hb hc
      rw [chainList] at ha hb hc
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [ite_eq_left h, List.getElem?_cons_succ, List.getElem?_cons_succ] at hc
        simp at hc
      · rw [ite_eq_right h] at ha hb hc
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            obtain rfl : -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)) = c := by
              simpa using hc
            exact chain_step hcur hr
        | succ j =>
            rw [List.getElem?_cons_succ] at ha hb hc
            exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
              (neg_primitivePart_ne_zero hr) j a b c ha hb hc

/-- **Pairwise coprimality along the chain.** If the two seeds are coprime
over `ℝ`, every pair of consecutive chain elements is: the three-term relation
transports Bezout witnesses down the chain. -/
private theorem chainList_pairs_coprime :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      IsCoprime (toPolyℝ prev) (toPolyℝ cur) →
      ∀ (i : ℕ) (a b : Hex.ZPoly),
        (prev :: cur :: chainList fuel prev cur)[i]? = some a →
        (prev :: cur :: chainList fuel prev cur)[i + 1]? = some b →
        IsCoprime (toPolyℝ a) (toPolyℝ b) := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur _ hco i a b ha hb
      rw [chainList] at ha hb
      cases i with
      | zero =>
          obtain rfl : prev = a := by simpa using ha
          obtain rfl : cur = b := by simpa using hb
          exact hco
      | succ j =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at hb
          simp at hb
  | succ fuel ih =>
      intro prev cur hcur hco i a b ha hb
      rw [chainList] at ha hb
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [ite_eq_left h] at ha hb
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            exact hco
        | succ j =>
            rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at hb
            simp at hb
      · rw [ite_eq_right h] at ha hb
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        obtain ⟨c₀, k, Q, hc₀, _, hrel⟩ := chain_step hcur hr
        have hco' : IsCoprime (toPolyℝ cur)
            (toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))) :=
          coprime_step (ne_of_gt hc₀) hrel hco
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            exact hco
        | succ j =>
            rw [List.getElem?_cons_succ] at ha hb
            exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
              (neg_primitivePart_ne_zero hr) hco' j a b ha hb

/-- **The terminal element is a unit.** With coprime seeds and sufficient fuel
(the degree of `cur` is below the remaining fuel, so the loop stops on a zero
pseudo-remainder, never by truncation), the last chain element is a unit of
`ℝ[X]`: at the stop, it divides its predecessor, and it is coprime to it. -/
private theorem chainList_last_unit :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      (cur.degree?).getD 0 < fuel →
      IsCoprime (toPolyℝ prev) (toPolyℝ cur) →
      ∀ z, (prev :: cur :: chainList fuel prev cur).getLast? = some z →
        IsUnit (toPolyℝ z) := by
  intro fuel
  induction fuel with
  | zero => intro prev cur _ hfuel _ z _; omega
  | succ fuel ih =>
      intro prev cur hcur hfuel hco z hz
      rw [chainList] at hz
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [ite_eq_left h, List.getLast?_cons_cons] at hz
        obtain rfl : cur = z := by simpa using hz
        have hr0 : Hex.ZPoly.spem prev cur = 0 := isZero_iff_eq_zero.mp h
        have hne : toPolyℝ cur ≠ 0 := fun hh => hcur (toPolyℝ_eq_zero_iff.mp hh)
        by_cases hdeg : (cur.degree?).getD 0 = 0
        · -- A nonzero constant is a unit of `ℝ[X]`.
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hne,
            natDegree_toPolyℝ, hdeg]
          rfl
        · -- Nonconstant: the terminal division relation plus coprimality.
          have hdeg1 : 1 ≤ (cur.degree?).getD 0 := by omega
          obtain ⟨c, Q, hc, hrel⟩ :=
            toPolyℝ_spem prev cur (leadingCoeff_ne_zero hcur) hdeg1
          rw [hr0, toPolyℝ_zero, add_zero] at hrel
          have hdvd : toPolyℝ cur ∣ toPolyℝ prev := by
            refine ⟨Polynomial.C c⁻¹ * Q, ?_⟩
            calc toPolyℝ prev
                = Polynomial.C c⁻¹ * (Polynomial.C c * toPolyℝ prev) := by
                  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (ne_of_gt hc),
                    Polynomial.C_1, one_mul]
              _ = Polynomial.C c⁻¹ * (Q * toPolyℝ cur) := by rw [hrel]
              _ = toPolyℝ cur * (Polynomial.C c⁻¹ * Q) := by ring
          exact hco.isUnit_of_dvd' hdvd dvd_rfl
      · rw [ite_eq_right h, List.getLast?_cons_cons] at hz
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        obtain ⟨c₀, k, Q, hc₀, _, hrel⟩ := chain_step hcur hr
        have hco' : IsCoprime (toPolyℝ cur)
            (toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))) :=
          coprime_step (ne_of_gt hc₀) hrel hco
        -- Degree bookkeeping: the pushed element's degree strictly drops.
        have hppdeg : ((Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)).degree?).getD 0
            = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          have h2 := congrArg Polynomial.natDegree
            (toPolyℝ_eq_C_content_mul_primitivePart (Hex.ZPoly.spem prev cur))
          rw [Polynomial.natDegree_C_mul (ne_of_gt (content_real_pos hr)),
            natDegree_toPolyℝ, natDegree_toPolyℝ] at h2
          omega
        have hnextdeg :
            (((-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))).degree?).getD 0)
              = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          rw [← natDegree_toPolyℝ, toPolyℝ_neg, Polynomial.natDegree_neg,
            natDegree_toPolyℝ, hppdeg]
        have hdeg1 : 1 ≤ (cur.degree?).getD 0 := one_le_degree_of_spem_ne_zero hcur hr
        have hdr : ((Hex.ZPoly.spem prev cur).degree?).getD 0 < (cur.degree?).getD 0 := by
          rcases spem_degree hcur hdeg1 with h0 | hlt
          · exact absurd h0 hr
          · exact hlt
        exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
          (neg_primitivePart_ne_zero hr) (by omega) hco' z hz

/-! # Converse: a terminal-constant chain forces coprime seeds -/

/-- **Reverse of `coprime_step`.** The three-term relation
`C c₀ · a = Q · b − C k · c'` (with `k ≠ 0`) transports `IsCoprime b c'` *back* to
`IsCoprime a b`: solving the relation for `c'` and substituting into a Bezout
combination for `(b, c')` yields one for `(a, b)`. -/
theorem coprime_step_rev {a b c' : Polynomial ℝ} {c₀ k : ℝ} {Q : Polynomial ℝ}
    (hk : k ≠ 0)
    (hrel : Polynomial.C c₀ * a = Q * b - Polynomial.C k * c')
    (h : IsCoprime b c') : IsCoprime a b := by
  obtain ⟨u, v, huv⟩ := h
  have hCk : Polynomial.C k⁻¹ * Polynomial.C k = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hk, Polynomial.C_1]
  have hc' : c' = Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a) := by
    have hkc' : Polynomial.C k * c' = Q * b - Polynomial.C c₀ * a := by rw [hrel]; ring
    calc c' = Polynomial.C k⁻¹ * (Polynomial.C k * c') := by rw [← mul_assoc, hCk, one_mul]
      _ = Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a) := by rw [hkc']
  refine ⟨-(v * Polynomial.C k⁻¹ * Polynomial.C c₀), u + v * Polynomial.C k⁻¹ * Q, ?_⟩
  calc -(v * Polynomial.C k⁻¹ * Polynomial.C c₀) * a
        + (u + v * Polynomial.C k⁻¹ * Q) * b
      = u * b + v * (Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a)) := by ring
    _ = u * b + v * c' := by rw [← hc']
    _ = 1 := huv

/-- **A terminal-constant chain has coprime seeds.** If the last element of
`prev :: cur :: chainList fuel prev cur` is a unit of `ℝ[X]` (its real cast), then
the seed pair `(prev, cur)` is coprime: a unit is coprime to its predecessor, and
`coprime_step_rev` walks that coprimality back to the front. The converse of
`chainList_last_unit`. -/
private theorem chainList_seeds_coprime :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      (cur.degree?).getD 0 < fuel →
      (∀ z, (prev :: cur :: chainList fuel prev cur).getLast? = some z →
        IsUnit (toPolyℝ z)) →
      IsCoprime (toPolyℝ prev) (toPolyℝ cur) := by
  intro fuel
  induction fuel with
  | zero => intro prev cur _ hfuel _; omega
  | succ fuel ih =>
      intro prev cur hcur hfuel hunit
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · -- The loop stops: the chain is `[prev, cur]`, so `cur` is the terminal unit.
        have hz : (prev :: cur :: chainList (fuel + 1) prev cur).getLast? = some cur := by
          rw [chainList, ite_eq_left h]; rfl
        obtain ⟨w, hw⟩ := hunit cur hz
        exact ⟨0, ↑w⁻¹, by rw [← hw]; simp⟩
      · have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        obtain ⟨c₀, k, Q, hc₀, hk, hrel⟩ := chain_step hcur hr
        have hnext_ne : -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)) ≠ 0 :=
          neg_primitivePart_ne_zero hr
        have hdeg1 : 1 ≤ (cur.degree?).getD 0 := one_le_degree_of_spem_ne_zero hcur hr
        have hppdeg : ((Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)).degree?).getD 0
            = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          have h2 := congrArg Polynomial.natDegree
            (toPolyℝ_eq_C_content_mul_primitivePart (Hex.ZPoly.spem prev cur))
          rw [Polynomial.natDegree_C_mul (ne_of_gt (content_real_pos hr)),
            natDegree_toPolyℝ, natDegree_toPolyℝ] at h2
          omega
        have hnextdeg :
            (((-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))).degree?).getD 0)
              = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          rw [← natDegree_toPolyℝ, toPolyℝ_neg, Polynomial.natDegree_neg,
            natDegree_toPolyℝ, hppdeg]
        have hdr : ((Hex.ZPoly.spem prev cur).degree?).getD 0 < (cur.degree?).getD 0 := by
          rcases spem_degree hcur hdeg1 with h0 | hlt
          · exact absurd h0 hr
          · exact hlt
        have hunit' : ∀ z, (cur :: -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))
              :: chainList fuel cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))).getLast?
              = some z → IsUnit (toPolyℝ z) := by
          intro z hz
          apply hunit z
          rw [chainList, ite_eq_right h, List.getLast?_cons_cons]
          exact hz
        have hco_tail : IsCoprime (toPolyℝ cur)
            (toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))) :=
          ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
            hnext_ne (by omega) hunit'
        exact coprime_step_rev (ne_of_gt hk) hrel hco_tail

/-! # Sign flanks at a simple zero -/

/-- A real polynomial vanishing at `r` with positive derivative there is
negative on a punctured left neighbourhood of `r` and positive on a punctured
right neighbourhood: the difference quotient tends to the positive derivative,
so it is eventually positive, and the sign of `f x = slope · (x − r)` follows
the sign of `x − r`. -/
private theorem eventually_flank_of_deriv_pos {f : Polynomial ℝ} {r : ℝ}
    (h0 : f.eval r = 0) (hd : 0 < f.derivative.eval r) :
    (∀ᶠ x in nhdsWithin r (Set.Iio r), f.eval x < 0) ∧
      (∀ᶠ x in nhdsWithin r (Set.Ioi r), 0 < f.eval x) := by
  have hder : HasDerivAt (fun y => f.eval y) (f.derivative.eval r) r :=
    f.hasDerivAt r
  have hslope : Filter.Tendsto (slope (fun y => f.eval y) r) (nhdsWithin r {r}ᶜ)
      (nhds (f.derivative.eval r)) := hasDerivAt_iff_tendsto_slope.mp hder
  have hpos : ∀ᶠ x in nhdsWithin r {r}ᶜ, slope (fun y => f.eval y) r x ∈ Set.Ioi 0 :=
    hslope (Ioi_mem_nhds hd)
  constructor
  · have hmono : nhdsWithin r (Set.Iio r) ≤ nhdsWithin r {r}ᶜ :=
      nhdsWithin_mono r (fun x hx => ne_of_lt hx)
    filter_upwards [hpos.filter_mono hmono, self_mem_nhdsWithin] with x hx hxr
    have hx' : 0 < (f.eval x - f.eval r) / (x - r) := by
      have := Set.mem_Ioi.mp hx
      rwa [slope_def_field] at this
    rw [h0, sub_zero] at hx'
    have hxr' : x - r < 0 := sub_neg.mpr (Set.mem_Iio.mp hxr)
    have h2 : f.eval x = f.eval x / (x - r) * (x - r) :=
      (div_mul_cancel₀ _ (ne_of_lt hxr')).symm
    rw [h2]
    exact mul_neg_of_pos_of_neg hx' hxr'
  · have hmono : nhdsWithin r (Set.Ioi r) ≤ nhdsWithin r {r}ᶜ :=
      nhdsWithin_mono r (fun x hx => (ne_of_lt (Set.mem_Ioi.mp hx)).symm)
    filter_upwards [hpos.filter_mono hmono, self_mem_nhdsWithin] with x hx hxr
    have hx' : 0 < (f.eval x - f.eval r) / (x - r) := by
      have := Set.mem_Ioi.mp hx
      rwa [slope_def_field] at this
    rw [h0, sub_zero] at hx'
    have hxr' : 0 < x - r := sub_pos.mpr (Set.mem_Ioi.mp hxr)
    have h2 : f.eval x = f.eval x / (x - r) * (x - r) :=
      (div_mul_cancel₀ _ (ne_of_gt hxr')).symm
    rw [h2]
    exact mul_pos hx' hxr'

/-- **The head-pair flank.** If `s₀` vanishes at `r`, `s₁` does not, and
`s₀' = C γ · s₁` with `γ > 0` (the executable seeds: the primitive parts of
`p` and `p'`), then `s₀ · s₁` is negative just left of `r` and positive just
right: its derivative at `r` is `γ · s₁(r)² > 0`. -/
theorem flank_of_key {s₀ s₁ : Polynomial ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hkey : Polynomial.derivative s₀ = Polynomial.C γ * s₁)
    {r : ℝ} (h0 : s₀.eval r = 0) (h1 : s₁.eval r ≠ 0) :
    (∀ᶠ x in nhdsWithin r (Set.Iio r), (s₀ * s₁).eval x < 0) ∧
      (∀ᶠ x in nhdsWithin r (Set.Ioi r), 0 < (s₀ * s₁).eval x) := by
  apply eventually_flank_of_deriv_pos
  · rw [Polynomial.eval_mul, h0, zero_mul]
  · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, h0, zero_mul, add_zero, hkey, Polynomial.eval_mul,
      Polynomial.eval_C, mul_assoc]
    exact mul_pos hγ (mul_self_pos.mpr h1)

/-! # Assembly: the executable chain is a Sturm chain -/

/-- Coprime polynomials never vanish together. -/
theorem eval_ne_zero_of_isCoprime {a b : Polynomial ℝ} (h : IsCoprime a b)
    {x : ℝ} (ha : a.eval x = 0) : b.eval x ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h
  intro hb
  have h2 := congrArg (Polynomial.eval x) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, ha, hb,
    mul_zero, mul_zero, add_zero, Polynomial.eval_one] at h2
  exact zero_ne_one h2

/-- Unpack an indexed read of the mapped chain into a read of the executable
chain. -/
private theorem getElem?_map_toPolyℝ {l : List Hex.ZPoly} {i : ℕ} {a : Polynomial ℝ}
    (h : (l.map toPolyℝ)[i]? = some a) : ∃ z, l[i]? = some z ∧ toPolyℝ z = a := by
  rw [List.getElem?_map] at h
  cases hz : l[i]? with
  | none => rw [hz] at h; simp at h
  | some z => rw [hz] at h; exact ⟨z, rfl, by simpa using h⟩

/-- Unpack the last element of the mapped chain. -/
private theorem getLast?_map_toPolyℝ {l : List Hex.ZPoly} {a : Polynomial ℝ}
    (h : (l.map toPolyℝ).getLast? = some a) :
    ∃ z, l.getLast? = some z ∧ toPolyℝ z = a := by
  rw [List.getLast?_eq_head?_reverse, ← List.map_reverse, List.head?_map] at h
  cases hz : l.reverse.head? with
  | none => rw [hz] at h; simp at h
  | some z =>
      rw [hz] at h
      exact ⟨z, by rw [List.getLast?_eq_head?_reverse, hz], by simpa using h⟩

/-- **The generic chain assembly.** Nonzero coprime seeds `s₀, s₁` with
`s₀' = C γ · s₁` (`γ > 0`) and enough fuel generate a Sturm chain for `s₀`. -/
private theorem isSturmChain_of_seeds (s₀ s₁ : Hex.ZPoly) (fuel : ℕ)
    (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0)
    (hfuel : (s₁.degree?).getD 0 < fuel)
    (hcop : IsCoprime (toPolyℝ s₀) (toPolyℝ s₁))
    (γ : ℝ) (hγ : 0 < γ)
    (hkey : Polynomial.derivative (toPolyℝ s₀) = Polynomial.C γ * toPolyℝ s₁) :
    Sturm.IsSturmChain (toPolyℝ s₀) ((s₀ :: s₁ :: chainList fuel s₀ s₁).map toPolyℝ) := by
  refine { nonempty := by simp, head := rfl, root_flank := ?_, nonzero_mem := ?_,
           consec_coprime := ?_, interior_alternates := ?_, last_no_root := ?_ }
  · -- root_flank
    intro r hr
    have hs₁r : (toPolyℝ s₁).eval r ≠ 0 := eval_ne_zero_of_isCoprime hcop hr
    obtain ⟨hL, hR⟩ := flank_of_key hγ hkey hr hs₁r
    exact ⟨toPolyℝ s₁, rfl, hs₁r, hL, hR⟩
  · -- nonzero_mem
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact fun hh => chainList_nonzero fuel s₀ s₁ hs₀ hs₁ z hz (toPolyℝ_eq_zero_iff.mp hh)
  · -- consec_coprime
    intro i x a b ha hb hax
    obtain ⟨za, hza, rfl⟩ := getElem?_map_toPolyℝ ha
    obtain ⟨zb, hzb, rfl⟩ := getElem?_map_toPolyℝ hb
    exact eval_ne_zero_of_isCoprime
      (chainList_pairs_coprime fuel s₀ s₁ hs₁ hcop i za zb hza hzb) hax
  · -- interior_alternates
    intro i x a b c ha hb hc hbx
    obtain ⟨za, hza, rfl⟩ := getElem?_map_toPolyℝ ha
    obtain ⟨zb, hzb, rfl⟩ := getElem?_map_toPolyℝ hb
    obtain ⟨zc, hzc, rfl⟩ := getElem?_map_toPolyℝ hc
    obtain ⟨c₀, k, Q, hc₀, hk, hrel⟩ :=
      chainList_triples fuel s₀ s₁ hs₁ i za zb zc hza hzb hzc
    have heval := congrArg (Polynomial.eval x) hrel
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, hbx, mul_zero, zero_sub] at heval
    have hax : (toPolyℝ za).eval x ≠ 0 :=
      eval_ne_zero_of_isCoprime
        (chainList_pairs_coprime fuel s₀ s₁ hs₁ hcop i za zb hza hzb).symm hbx
    have hcx : (toPolyℝ zc).eval x ≠ 0 := by
      intro hh
      rw [hh, mul_zero, neg_zero, mul_eq_zero] at heval
      rcases heval with h1 | h1
      · exact (ne_of_gt hc₀) h1
      · exact hax h1
    refine ⟨hax, hcx, ?_⟩
    have h2 : c₀ * ((toPolyℝ za).eval x * (toPolyℝ zc).eval x)
        = -(k * ((toPolyℝ zc).eval x * (toPolyℝ zc).eval x)) := by
      linear_combination (toPolyℝ zc).eval x * heval
    nlinarith [h2, hc₀, hk, mul_self_pos.mpr hcx]
  · -- last_no_root
    intro q hq x
    obtain ⟨z, hz, rfl⟩ := getLast?_map_toPolyℝ hq
    have hunit := chainList_last_unit fuel s₀ s₁ hs₁ hfuel hcop z hz
    obtain ⟨u, hu, hCu⟩ := Polynomial.isUnit_iff.mp hunit
    rw [← hCu, Polynomial.eval_C]
    exact hu.ne_zero

/-- **The executable Sturm chain is a Sturm chain.** For a positive-degree,
rationally squarefree `p`, the real cast of `Hex.ZPoly.sturmChain p` satisfies
all the `Sturm.IsSturmChain` sign axioms for `toPolyℝ (primitivePart p)`.

Stated at the primitive part: the executable chain's head is `primitivePart p`
(the content is stripped), so an `IsSturmChain (toPolyℝ p) …` conclusion would
have the wrong head; `p` and its primitive part have the same real roots
(`roots_toPolyℝ_eq_primitivePart`), so the counting consequences are
unaffected. -/
theorem sturmChain_isSturmChain (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0)
    (hsq : Hex.ZPoly.SquareFreeRat p) :
    Sturm.IsSturmChain (toPolyℝ (Hex.ZPoly.primitivePart p))
      ((Hex.ZPoly.sturmChain p).toList.map toPolyℝ) := by
  -- Nonvanishing of `p` and `p'`.
  have hp0 : p ≠ 0 := by
    intro hh
    rw [hh] at hp
    simp only [Hex.DensePoly.degree?_zero_getD] at hp
    omega
  have hnd : (toPolyℝ p).natDegree = (p.degree?).getD 0 := natDegree_toPolyℝ p
  have hd0 : Hex.DensePoly.derivative p ≠ 0 := by
    intro hh
    have h2 : Polynomial.derivative (toPolyℝ p) = 0 := by
      rw [← toPolyℝ_derivative, hh, toPolyℝ_zero]
    have h3 := Polynomial.derivative_eq_zero.mp h2
    omega
  have hs₀0 : Hex.ZPoly.primitivePart p ≠ 0 := primitivePart_ne_zero hp0
  have hs₁0 : Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p) ≠ 0 :=
    primitivePart_ne_zero hd0
  -- Content decompositions.
  have hc₀ : (0:ℝ) < ((Hex.ZPoly.content p : Int) : ℝ) := content_real_pos hp0
  have hc₁ : (0:ℝ) < ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ) :=
    content_real_pos hd0
  have hdecomp₀ := toPolyℝ_eq_C_content_mul_primitivePart p
  have hdecomp₁ := toPolyℝ_eq_C_content_mul_primitivePart (Hex.DensePoly.derivative p)
  -- Seed coprimality from squarefreeness.
  have hsep : (toPolyℝ p).Separable := separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hsq)
  have hcop_p : IsCoprime (toPolyℝ p) (Polynomial.derivative (toPolyℝ p)) :=
    Polynomial.separable_def _ |>.mp hsep
  have hcop : IsCoprime (toPolyℝ (Hex.ZPoly.primitivePart p))
      (toPolyℝ (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))) := by
    have h1 : toPolyℝ (Hex.ZPoly.primitivePart p) ∣ toPolyℝ p :=
      ⟨Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ), by rw [hdecomp₀]; ring⟩
    have h2 : toPolyℝ (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))
        ∣ Polynomial.derivative (toPolyℝ p) := by
      rw [← toPolyℝ_derivative]
      exact ⟨Polynomial.C ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ),
        by rw [hdecomp₁]; ring⟩
    exact (hcop_p.of_isCoprime_of_dvd_left h1).of_isCoprime_of_dvd_right h2
  -- The derivative key: `s₀' = C γ · s₁` with positive `γ`.
  have hkey : Polynomial.derivative (toPolyℝ (Hex.ZPoly.primitivePart p))
      = Polynomial.C (((Hex.ZPoly.content p : Int) : ℝ)⁻¹
            * ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ))
          * toPolyℝ (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)) := by
    have h1 := congrArg Polynomial.derivative hdecomp₀
    rw [Polynomial.derivative_C_mul, ← toPolyℝ_derivative, hdecomp₁] at h1
    -- h1 : C c₁ * P s₁ = C c₀ * derivative (P s₀)
    have h2 := congrArg (fun t => Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ)⁻¹ * t) h1
    rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul,
      inv_mul_cancel₀ (ne_of_gt hc₀), Polynomial.C_1, one_mul] at h2
    exact h2.symm
  have hγ : (0:ℝ) < ((Hex.ZPoly.content p : Int) : ℝ)⁻¹
      * ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ) :=
    mul_pos (inv_pos.mpr hc₀) hc₁
  -- Fuel: `deg s₁ < p.size`.
  have hfuel : ((Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)).degree?).getD 0
      < p.size := by
    have hdp : ((Hex.DensePoly.derivative p).degree?).getD 0 < (p.degree?).getD 0 := by
      rw [← natDegree_toPolyℝ, ← natDegree_toPolyℝ, toPolyℝ_derivative]
      exact Polynomial.natDegree_derivative_lt (by omega)
    have hpp : ((Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)).degree?).getD 0
        = ((Hex.DensePoly.derivative p).degree?).getD 0 := by
      have h3 := congrArg Polynomial.natDegree hdecomp₁
      rw [Polynomial.natDegree_C_mul (ne_of_gt hc₁), natDegree_toPolyℝ,
        natDegree_toPolyℝ] at h3
      omega
    have h4 : p.degree? = some (p.size - 1) := degree?_of_ne_zero hp0
    rw [h4] at hdp
    simp only [Option.getD_some] at hdp
    omega
  rw [sturmChain_toList p hp]
  exact isSturmChain_of_seeds _ _ _ hs₀0 hs₁0 hfuel hcop _ hγ hkey

/-- **The Sturm squarefree certificate is sound.** If the executable
`Hex.ZPoly.hasSquarefreeSturmChain p` is `true` — `p` has positive degree and the
terminal element of its Sturm chain is a nonzero constant — then `p` is squarefree
over `ℚ`. This is the converse packaging of `sturmChain_isSturmChain`: it lets a
concrete `SquareFreeRat p` be discharged by `by decide` on the executable chain,
sidestepping the non-kernel-reducible rational gcd inside `SquareFreeRat` itself. -/
theorem squareFreeRat_of_hasSquarefreeSturmChain (p : Hex.ZPoly)
    (h : Hex.ZPoly.hasSquarefreeSturmChain p = true) : Hex.ZPoly.SquareFreeRat p := by
  unfold Hex.ZPoly.hasSquarefreeSturmChain at h
  cases hlast : (Hex.ZPoly.sturmChain p).toList.getLast? with
  | none => rw [hlast] at h; simp at h
  | some z =>
    rw [hlast] at h
    have hzsize : z.size = 1 := by simpa using h
    -- The chain is nonempty, so `p` has positive degree.
    have hne : Hex.ZPoly.sturmChain p ≠ #[] := by
      intro he; rw [he] at hlast; simp at hlast
    have hp : 1 ≤ (p.degree?).getD 0 := by
      rcases hd : p.degree? with _ | m
      · exact absurd (by simp only [Hex.ZPoly.sturmChain, hd]) hne
      · rcases m with _ | m'
        · exact absurd (by simp only [Hex.ZPoly.sturmChain, hd]) hne
        · simp
    have hp0 : p ≠ 0 := by
      intro hh; rw [hh] at hp; simp only [Hex.DensePoly.degree?_zero_getD] at hp; omega
    have hnd : (toPolyℝ p).natDegree = (p.degree?).getD 0 := natDegree_toPolyℝ p
    have hd0 : Hex.DensePoly.derivative p ≠ 0 := by
      intro hh
      have h2 : Polynomial.derivative (toPolyℝ p) = 0 := by
        rw [← toPolyℝ_derivative, hh, toPolyℝ_zero]
      have h3 := Polynomial.derivative_eq_zero.mp h2
      omega
    have hs₁0 : Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p) ≠ 0 :=
      primitivePart_ne_zero hd0
    -- The terminal element is a nonzero constant, hence a unit of `ℝ[X]`.
    have hzne : z ≠ 0 := by rintro rfl; simp at hzsize
    have hzdeg : (z.degree?).getD 0 = 0 := by
      rw [degree?_of_ne_zero hzne]; simp [hzsize]
    have hzunit : IsUnit (toPolyℝ z) := by
      have hne' : toPolyℝ z ≠ 0 := fun hh => hzne (toPolyℝ_eq_zero_iff.mp hh)
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hne',
        natDegree_toPolyℝ, hzdeg]; rfl
    -- Seed coprimality by walking the terminal unit back to the front.
    rw [sturmChain_toList p hp] at hlast
    have hfuel : ((Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)).degree?).getD 0
        < p.size := by
      have hc₁ : (0:ℝ) < ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ) :=
        content_real_pos hd0
      have hdecomp₁ := toPolyℝ_eq_C_content_mul_primitivePart (Hex.DensePoly.derivative p)
      have hdp : ((Hex.DensePoly.derivative p).degree?).getD 0 < (p.degree?).getD 0 := by
        rw [← natDegree_toPolyℝ, ← natDegree_toPolyℝ, toPolyℝ_derivative]
        exact Polynomial.natDegree_derivative_lt (by omega)
      have hpp : ((Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)).degree?).getD 0
          = ((Hex.DensePoly.derivative p).degree?).getD 0 := by
        have h3 := congrArg Polynomial.natDegree hdecomp₁
        rw [Polynomial.natDegree_C_mul (ne_of_gt hc₁), natDegree_toPolyℝ,
          natDegree_toPolyℝ] at h3
        omega
      have h4 : p.degree? = some (p.size - 1) := degree?_of_ne_zero hp0
      rw [h4] at hdp
      simp only [Option.getD_some] at hdp
      omega
    have hcop_seeds : IsCoprime (toPolyℝ (Hex.ZPoly.primitivePart p))
        (toPolyℝ (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))) :=
      chainList_seeds_coprime p.size _ _ hs₁0 hfuel (by
        intro z' hz'
        rw [hlast] at hz'
        obtain rfl := Option.some.inj hz'
        exact hzunit)
    -- Lift seed coprimality to `p` and its derivative by unit (content) scaling.
    have hcop_p : IsCoprime (toPolyℝ p) (Polynomial.derivative (toPolyℝ p)) := by
      have hd₀ := toPolyℝ_eq_C_content_mul_primitivePart p
      have hd₁ : Polynomial.derivative (toPolyℝ p)
          = Polynomial.C ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ)
              * toPolyℝ (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)) := by
        rw [← toPolyℝ_derivative]
        exact toPolyℝ_eq_C_content_mul_primitivePart (Hex.DensePoly.derivative p)
      have hu0 : IsUnit (Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ)) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr (ne_of_gt (content_real_pos hp0)))
      have hu1 :
          IsUnit (Polynomial.C ((Hex.ZPoly.content (Hex.DensePoly.derivative p) : Int) : ℝ)) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr (ne_of_gt (content_real_pos hd0)))
      rw [hd₁, hd₀]
      exact (isCoprime_mul_unit_left_left hu0 _ _).mpr
        ((isCoprime_mul_unit_left_right hu1 _ _).mpr hcop_seeds)
    -- Separability over `ℝ`, reflected to `ℚ`, gives squarefreeness.
    have hsep_ℝ : (toPolyℝ p).Separable := (Polynomial.separable_def (toPolyℝ p)).mpr hcop_p
    have hmap : toPolyℝ p = (toPolyℚ p).map (algebraMap ℚ ℝ) := by
      rw [toPolyℝ, toPolyℚ, Polynomial.map_map]; congr 1
    have hsep_ℚ : (toPolyℚ p).Separable := (separable_map (algebraMap ℚ ℝ)).mp (hmap ▸ hsep_ℝ)
    exact (squareFreeRat_iff p hp0).mpr hsep_ℚ.squarefree

/-! # Consequences: the executable counts equal Mathlib root counts -/

/-- The real cast of the primitive part inherits squarefreeness. -/
private theorem squarefree_toPolyℝ_primitivePart (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hsq : Hex.ZPoly.SquareFreeRat p) :
    Squarefree (toPolyℝ (Hex.ZPoly.primitivePart p)) := by
  have hsep : (toPolyℝ p).Separable :=
    separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hsq)
  exact Squarefree.squarefree_of_dvd
    ⟨Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ),
      by rw [toPolyℝ_eq_C_content_mul_primitivePart p]; ring⟩ hsep.squarefree

/-- Dyadic order transfers to the real values. -/
theorem toReal_lt_toReal {a b : Dyadic} (h : a < b) :
    Dyadic.toReal a < Dyadic.toReal b := by
  have h2 : a.toRat < b.toRat := Dyadic.toRat_lt_toRat_iff.mpr h
  unfold Dyadic.toReal
  exact_mod_cast h2

/-- Nonstrict dyadic order transfers to the real values. -/
theorem toReal_le_toReal {a b : Dyadic} (h : a ≤ b) :
    Dyadic.toReal a ≤ Dyadic.toReal b := by
  have h2 : a.toRat ≤ b.toRat := Dyadic.toRat_le_toRat_iff.mpr h
  unfold Dyadic.toReal
  exact_mod_cast h2

/-- Dyadic order coincides with the order of the real values. -/
theorem toReal_lt_toReal_iff {a b : Dyadic} :
    Dyadic.toReal a < Dyadic.toReal b ↔ a < b := by
  unfold Dyadic.toReal
  rw [Rat.cast_lt, Dyadic.toRat_lt_toRat_iff]

/-- The real value of an interval's exact dyadic midpoint. -/
theorem toReal_midpoint (I : Hex.DyadicInterval) :
    Dyadic.toReal I.midpoint =
      (Dyadic.toReal I.lower + Dyadic.toReal I.upper) / 2 := by
  unfold Hex.DyadicInterval.midpoint
  rw [toReal_shiftRight, toReal_add]
  norm_num
  ring

/-- The midpoint is strictly above the lower endpoint. -/
theorem lower_lt_midpoint (I : Hex.DyadicInterval) : I.lower < I.midpoint := by
  rw [← toReal_lt_toReal_iff, toReal_midpoint]
  have := toReal_lt_toReal I.lt
  linarith

/-- The midpoint is strictly below the upper endpoint. -/
theorem midpoint_lt_upper (I : Hex.DyadicInterval) : I.midpoint < I.upper := by
  rw [← toReal_lt_toReal_iff, toReal_midpoint]
  have := toReal_lt_toReal I.lt
  linarith

/-- **Sturm count correspondence.** For positive-degree, rationally squarefree
`p`, the executable `Hex.sturmCount p I` equals the number of real roots of
`toPolyℝ p` in the half-open interval `(I.lower, I.upper]`. -/
theorem sturmCount_eq_card_roots (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0)
    (hsq : Hex.ZPoly.SquareFreeRat p) (I : Hex.DyadicInterval) :
    Hex.sturmCount p I
      = ((toPolyℝ p).roots.filter
          (fun r => Dyadic.toReal I.lower < r ∧ r ≤ Dyadic.toReal I.upper)).card := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hp
    simp only [Hex.DensePoly.degree?_zero_getD] at hp
    omega
  have hchain := sturmChain_isSturmChain p hp hsq
  have hs₀0 : toPolyℝ (Hex.ZPoly.primitivePart p) ≠ 0 :=
    fun hh => primitivePart_ne_zero hp0 (toPolyℝ_eq_zero_iff.mp hh)
  have hsf := squarefree_toPolyℝ_primitivePart p hp0 hsq
  have hab : Dyadic.toReal I.lower < Dyadic.toReal I.upper := toReal_lt_toReal I.lt
  have hkey := Sturm.sturm_half_open hs₀0 hsf hchain hab
  change (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) I.lower : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) I.upper = _
  rw [sturmVarAt_eq, sturmVarAt_eq, roots_toPolyℝ_eq_primitivePart p hp0]
  exact hkey

/-- Casting an integer's sign to `ℝ` preserves `SignType.sign`. -/
private theorem sign_intCast_sign (n : Int) :
    SignType.sign ((n.sign : ℝ)) = SignType.sign ((n : ℝ)) := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]
    have h2 : (n : ℝ) < 0 := by exact_mod_cast h
    rw [show ((-1 : Int) : ℝ) = -1 by norm_num, sign_neg (by norm_num), sign_neg h2]
  · subst h; simp
  · rw [Int.sign_eq_one_of_pos h]
    have h2 : (0:ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [show ((1 : Int) : ℝ) = 1 by norm_num, sign_pos (by norm_num), sign_pos h2]

/-- The executable `+∞` variation count matches the abstract one: both read
the signs of the leading coefficients. -/
theorem sturmVarPosInf_eq (chain : Array Hex.ZPoly) :
    Hex.sturmVarPosInf chain = Sturm.sturmVarPosInf (chain.toList.map toPolyℝ) := by
  rw [Hex.sturmVarPosInf, signVar_eq, Sturm.sturmVarPosInf]
  apply Sturm.signVariations_congr
  simp only [List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q _
  simp only [Function.comp_apply]
  rw [leadingCoeff_toPolyℝ]
  exact sign_intCast_sign _

/-- The executable `−∞` variation count matches the abstract one: both read
`sign(lc) · (−1)^degree`. -/
theorem sturmVarNegInf_eq (chain : Array Hex.ZPoly) :
    Hex.sturmVarNegInf chain = Sturm.sturmVarNegInf (chain.toList.map toPolyℝ) := by
  rw [Hex.sturmVarNegInf, signVar_eq, Sturm.sturmVarNegInf]
  apply Sturm.signVariations_congr
  simp only [List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q _
  simp only [Function.comp_apply]
  rw [leadingCoeff_toPolyℝ, natDegree_toPolyℝ]
  by_cases hpar : (Hex.DensePoly.degree? q).getD 0 % 2 = 1
  · rw [ite_eq_left hpar, (Nat.odd_iff.mpr hpar).neg_one_pow, mul_neg_one, mul_neg_one]
    have h2 : ((-(Hex.DensePoly.leadingCoeff q).sign : Int) : ℝ)
        = -(((Hex.DensePoly.leadingCoeff q).sign : Int) : ℝ) := by push_cast; ring
    rw [h2, Left.sign_neg, Left.sign_neg, sign_intCast_sign]
  · rw [ite_eq_right hpar, (Nat.even_iff.mpr (by omega)).neg_one_pow, mul_one, mul_one]
    exact sign_intCast_sign _

/-- **Root count correspondence.** For positive-degree, rationally squarefree
`p`, the executable `Hex.rootCount p` equals the total number of real roots
of `toPolyℝ p`. -/
theorem rootCount_eq_card_roots (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0)
    (hsq : Hex.ZPoly.SquareFreeRat p) :
    Hex.rootCount p = ((toPolyℝ p).roots).card := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hp
    simp only [Hex.DensePoly.degree?_zero_getD] at hp
    omega
  have hchain := sturmChain_isSturmChain p hp hsq
  have hs₀0 : toPolyℝ (Hex.ZPoly.primitivePart p) ≠ 0 :=
    fun hh => primitivePart_ne_zero hp0 (toPolyℝ_eq_zero_iff.mp hh)
  have hsf := squarefree_toPolyℝ_primitivePart p hp0 hsq
  have hkey := Sturm.sturm_line hs₀0 hsf hchain
  rw [← roots_toPolyℝ_eq_primitivePart p hp0] at hkey
  change Hex.sturmVarNegInf (Hex.ZPoly.sturmChain p)
      - Hex.sturmVarPosInf (Hex.ZPoly.sturmChain p) = _
  rw [sturmVarNegInf_eq, sturmVarPosInf_eq]
  omega

end

end HexRealRootsMathlib
