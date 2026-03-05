/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.Reduce
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Pseudo-Division

This file defines **pseudo-division** of multivariate polynomials,
a fundamental operation in the Characteristic Set Method.

## Main Definitions

* `MvPolynomial.pseudoOf`:
  Pseudo-division of `g` by `f` with respect to a variable `i` (over commutative rings).
* `MvPolynomial.pseudo`:
  General pseudo-division that handles constants and zero (over fields).
* `MvPolynomial.setPseudo`:
  Successive pseudo-division by all polynomials in a triangular set.
* `MvPolynomial.setPseudoRem`:
  Computes only the remainder (more efficient when quotients are not needed).
* `MvPolynomial.isRemainder`:
  A predicate stating that `r` is a valid remainder of `g` by `f`,
  meaning `r` is reduced w.r.t. `f` and `init(f)^s * g = q * f + r` for some `s, q`.
* `MvPolynomial.isSetRemainder`:
  A predicate stating that `r` is a valid remainder of `g` by a triangular set `S`,
  meaning `r` is reduced w.r.t. `S` and satisfies the extended division equation.

## Main results

* `pseudoOf_equation`: `init(f) ^ s * g = q * f + r` where `deg(r) < deg(f)`
* `pseudoOf_remainder_reducedTo`: The remainder is reduced w.r.t. the divisor
* `pseudo_remainder_isRemainder`: The remainder satisfies the `isRemainder` predicate
* `setPseudo_remainder_isSetRemainder`: The remainder satisfies the `isSetRemainder` predicate
* `setPseudo_remainder_eq_zero_of_mem`: Elements of `S` have zero remainder when divided by `S`

## References
* [Wen-Tsun Wu, *Mathematics Mechanization*][wen2000mathematics]

-/

@[expose] public section

namespace MvPolynomial

/-- The result of a pseudo-division of `g` by `f`,
satisfying the equation `init(f) ^ s * g = q * f + r`. -/
structure PseudoResult (α : Type*) where
  /-- The power `s`. -/
  exponent : ℕ
  /-- The quotient `q`. -/
  quotient : α
  /-- The remainder `r`. -/
  remainder : α

/-- The result of pseudo-dividing `g` by a sequence of polynomials (a triangulated set)
satisfying the equation `(∏ i, (S i).initial ^ es[i]) * g = (∑ i, qs[i] * S i) + r`. -/
structure SetPseudoResult (α : Type*) where
  /-- The powers of the initials `es`. -/
  exponents : List ℕ
  /-- The quotients `qs`. -/
  quotients : List α
  /-- The remainder `r`. -/
  remainder : α

section CommRing

variable {R σ : Type*} [CommRing R] (i : σ) (g f : MvPolynomial σ R)

/-- The recursive algorithm of pseudo-division -/
noncomputable def pseudoOf.go (I : MvPolynomial σ R) (n fuel : ℕ) (s : ℕ)
    (q r : MvPolynomial σ R) : PseudoResult (MvPolynomial σ R) :=
  if fuel = 0 then ⟨s, q, r⟩
  else if r.degreeOf i < n then ⟨s, q, r⟩
  else
    letI d := r.degreeOf i
    letI Ic_r := r.initialOf i
    letI x_power := X i ^ (d - n)
    let term := Ic_r * x_power
    let q' := I * q + term
    let r' := I * r - term * f
    go I n (fuel - 1) (s + 1) q' r'

/-- Pseudo-division of `g` by `f` regarding the variable `i`.
This algorithm computes `q` and `r` such that `initᵢ(f) ^ s * g = q * f + r`,
where `degᵢ(r) < degᵢ(f)`.
It uses a `fuel` parameter to guarantee termination. -/
noncomputable def pseudoOf : PseudoResult (MvPolynomial σ R) :=
  let I := f.initialOf i
  let n := f.degreeOf i
  pseudoOf.go i f I n (g.degreeOf i + 1 - n) 0 0 g

@[simp] theorem zero_pseudoOf : (0 : MvPolynomial σ R).pseudoOf i f = ⟨1 - f.degreeOf i, 0, 0⟩ := by
  rewrite [pseudoOf, degreeOf_zero, zero_add]
  by_cases fd : f.degreeOf i = 0
  · simp [fd, tsub_zero, pseudoOf.go]
  have : 1 - f.degreeOf i = 0 := Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero fd)
  simp only [this, pseudoOf.go, ↓reduceIte]

@[simp] theorem pseudoOf_self : f.pseudoOf i f = ⟨1, f.initialOf i, 0⟩ := by
  simp [pseudoOf, pseudoOf.go]

lemma pseudoOfGo_next {i : σ} (f I : MvPolynomial σ R) {n : ℕ} (fuel s : ℕ) (q : MvPolynomial σ R)
    {r : MvPolynomial σ R} (hn : n ≤ r.degreeOf i) :
    let term := r.initialOf i * X i ^ (r.degreeOf i - n);
    pseudoOf.go i f I n (fuel + 1) s q r =
      pseudoOf.go i f I n fuel (s + 1) (I * q + term) (I * r - term * f) := by
  rewrite [pseudoOf.go]; simp [hn]

lemma pseudoOfGo_equation (I : MvPolynomial σ R) (n : ℕ) : ∀ (fuel s : ℕ) (q r : MvPolynomial σ R),
    I ^ s * g = q * f + r → letI result := pseudoOf.go i f I n fuel s q r;
    I ^ result.exponent * g = result.quotient * f + result.remainder := fun fuel ↦ by
  induction fuel with
  | zero => simp only [pseudoOf.go, ↓reduceIte, imp_self, implies_true]
  | succ fuel ih =>
    intro s q r eq
    by_cases dlt : r.degreeOf i < n
    · simp only [pseudoOf.go, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, dlt, eq]
    letI d := r.degreeOf i
    letI Ic_r := r.initialOf i
    letI x_power := (X i : MvPolynomial σ R) ^ (d - n)
    let term := Ic_r * x_power
    let q' := I * q + term
    let r' := I * r - term * f
    have := pseudoOfGo_next f I fuel s q (le_of_not_gt dlt)
    have heq' : I ^ (s + 1) * g = q' * f + r' := by
      unfold q' r'
      have : (I * q + term) * f + (I * r - term * f) = I * (q * f + r) + (term - term) * f :=
        by ring
      nth_rewrite 1 [this, ← eq]
      ring
    rw [this, ih (s + 1) q' r' heq']

/-- The fundamental equation of pseudo-division: `initᵢ(f) ^ s * g = q * f + r` -/
theorem pseudoOf_equation : f.initialOf i ^ (g.pseudoOf i f).exponent * g
    = (g.pseudoOf i f).quotient * f + (g.pseudoOf i f).remainder :=
  g.pseudoOfGo_equation _ _ _ _ _ _ _ _ (by ring)

lemma degreeOf_pseudoOfGo_remainder_le_of_degreeOf_eq_zero {i j : σ} {f I : MvPolynomial σ R}
    (n : ℕ) (hi : i ≠ j) (hj : f.degreeOf j = 0) (hI : I = f.initialOf i) : ∀ (fuel s) (q r),
    (pseudoOf.go i f I n fuel s q r).remainder.degreeOf j ≤ r.degreeOf j := fun fuel ↦ by
  induction fuel with
  | zero => simp only [pseudoOf.go, ↓reduceIte, le_refl, implies_true]
  | succ fuel ih =>
    intro s q r
    by_cases dlt : r.degreeOf i < n
    · simp only [pseudoOf.go, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, dlt, le_refl]
    letI d := r.degreeOf i
    letI Ic_r := r.initialOf i
    letI x_power := (X i : MvPolynomial σ R) ^ (d - n)
    let term := Ic_r * x_power
    let q' := I * q + term
    let r' := I * r - term * f
    apply le_trans (pseudoOfGo_next f I fuel s q (le_of_not_gt dlt) ▸ ih (s + 1) q' r')
    apply le_trans (degreeOf_sub_le ..)
    apply max_le <;> apply le_trans (degreeOf_mul_le ..)
    · have Id : I.degreeOf j = 0 := Nat.eq_zero_of_le_zero <| hj ▸ hI ▸ degreeOf_initialOf_le i j f
      simp only [Id, zero_add, le_refl]
    simp only [hj, add_zero, term]
    apply le_trans (degreeOf_mul_le ..)
    rewrite [degreeOf_X_pow_of_ne _ hi.symm, add_zero]
    exact degreeOf_initialOf_le i j r

theorem degreeOf_pseudoOf_remainder_le_of_degreeOf_eq_zero {i j : σ} (g : MvPolynomial σ R)
    {f : MvPolynomial σ R} (hi : i ≠ j) (hj : f.degreeOf j = 0) :
    (g.pseudoOf i f).remainder.degreeOf j ≤ g.degreeOf j :=
  degreeOf_pseudoOfGo_remainder_le_of_degreeOf_eq_zero _ hi hj rfl ..

theorem dvd_pseudoOf_remainder_of_dvd (i : σ) {g f : MvPolynomial σ R} (h : f ∣ g) :
    f ∣ (g.pseudoOf i f).remainder := by
  rcases h with ⟨c, hc⟩
  have heq := g.pseudoOf_equation i f
  set res := g.pseudoOf i f
  rw [hc, mul_comm, mul_assoc, mul_comm _ f] at heq
  exact (dvd_add_right ⟨_, rfl⟩).mp (heq ▸ (⟨_, rfl⟩ : f ∣ f * (c * _ ^ _)))

theorem pseudoOf_remainder_eq_of_degreeOf_eq_zero {i : σ} {g f : MvPolynomial σ R}
    (h1 : g.degreeOf i = 0) (h2 : f.degreeOf i ≠ 0) : (g.pseudoOf i f).remainder = g := by
  rewrite [pseudoOf, h1, zero_add]
  have h2 : 1 - f.degreeOf i = 0 := Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero h2)
  simp only [h2, pseudoOf.go, ↓reduceIte]

variable [NoZeroDivisors R]

lemma degreeOf_pseudoOfGo_remainder_lt_of_degreeOf_ne_zero {i : σ} {f I : MvPolynomial σ R}
    {n : ℕ} (hI : I = f.initialOf i) (hn : n ≠ 0) (hnd : n = f.degreeOf i) :
    ∀ (fuel s : ℕ) (q r : MvPolynomial σ R), fuel ≥ r.degreeOf i + 1 - n →
    (pseudoOf.go i f I n fuel s q r).remainder.degreeOf i < f.degreeOf i := fun fuel ↦ by
  induction fuel with
  | zero =>
    intro s q r h
    simpa [pseudoOf.go] using hnd ▸ tsub_nonpos.mp h
  | succ fuel ih =>
    intro s q r h
    by_cases dlt : r.degreeOf i < n
    · have : degreeOf i r + 1 - n ≤ 0 := Nat.sub_le_iff_le_add'.mpr dlt
      have := ih s q r <| le_trans this (Nat.le_add_left 0 fuel)
      simpa [pseudoOf.go, dlt] using this
    letI d := r.degreeOf i
    letI Ic_r := r.initialOf i
    letI x_power := (X i : MvPolynomial σ R) ^ (d - n)
    let term := Ic_r * x_power
    let q' := I * q + term
    let r' := I * r - term * f
    suffices fuel ≥ r'.degreeOf i + 1 - n by
      unfold pseudoOf.go
      simpa [dlt] using (ih (s + 1) q' r') this
    have hle : r'.degreeOf i ≤ r.degreeOf i - 1 := by
      unfold r' term x_power Ic_r d
      have Id : I.degreeOf i = 0 := by rw [hI, degreeOf_initialOf_self]
      have : (I * r).degreeOf i - 1 ≤ r.degreeOf i - 1 := by
        apply Nat.sub_le_sub_right
        rewrite [← zero_add (r.degreeOf i), ← Id]
        exact degreeOf_mul_le ..
      refine le_trans ?_ this
      apply degreeOf_sub_lt_of_initialOf_eq
      repeat1' rewrite [mul_assoc, mul_comm _ f, ← mul_assoc]
      · rewrite [initialOf_mul_X_self_pow, initialOf_mul_eq, initialOf_mul_eq, hI]
        rw [initialOf_initialOf_self, initialOf_initialOf_self, mul_comm]
      have f_ne : f ≠ 0 := ne_zero_of_degreeOf_ne_zero (hnd ▸ hn)
      have I_ne : I ≠ 0 := hI ▸ initialOf_ne_zero i f_ne
      have r_ne : r ≠ 0 := by
        contrapose! dlt
        rewrite [dlt, hnd, degreeOf_zero]
        exact Nat.zero_lt_of_ne_zero (hnd ▸ hn)
      have Ir_ne : Ic_r ≠ 0 := initialOf_ne_zero i r_ne
      rewrite [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ (mul_ne_zero_iff.mpr ⟨Ir_ne ,f_ne⟩)]
      rewrite [degreeOf_mul_eq I_ne r_ne, degreeOf_mul_eq Ir_ne f_ne, hI, ← hnd]
      simpa [Ic_r] using (Nat.add_sub_of_le <| Nat.le_of_not_lt dlt).symm
    simp only [ge_iff_le, tsub_le_iff_right] at h ⊢
    by_cases hr : r.degreeOf i = 0
    · rewrite [hr] at hle
      have : r'.degreeOf i = 0 := Nat.eq_zero_of_le_zero hle
      simp only [hr, this, zero_add] at h ⊢
      by_contra con
      have : fuel + n = 0 := Nat.eq_zero_of_not_pos con
      absurd Nat.eq_zero_of_add_eq_zero_left this
      exact hn
    have hr : r.degreeOf i > 0 := Nat.zero_lt_of_ne_zero hr
    rewrite [add_assoc, add_comm 1 n, ← add_assoc] at h
    have h := Nat.le_of_add_le_add_right h
    by_cases hr' : r'.degreeOf i = r.degreeOf i - 1
    · rewrite [hr', Nat.sub_add_cancel hr]
      exact h
    have hr' := Nat.add_lt_of_lt_sub <| lt_of_le_of_ne hle hr'
    exact le_of_lt <| lt_of_lt_of_le hr' h

theorem degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero {i : σ} (g : MvPolynomial σ R)
    {f : MvPolynomial σ R} (hi : f.degreeOf i ≠ 0) :
    (g.pseudoOf i f).remainder.degreeOf i < f.degreeOf i :=
  degreeOf_pseudoOfGo_remainder_lt_of_degreeOf_ne_zero rfl hi rfl _ _ _ _ (le_refl _)

theorem pseudoOf_remainder_eq_zero_of_dvd {i : σ} {g f : MvPolynomial σ R} (h1 : f ∣ g)
    (h2 : f.degreeOf i ≠ 0) : (g.pseudoOf i f).remainder = 0 := by
  have ⟨c, hc⟩ : f ∣ (g.pseudoOf i f).remainder := dvd_pseudoOf_remainder_of_dvd i h1
  set r := (g.pseudoOf i f).remainder
  by_contra con
  absurd degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero g h2
  have : r.degreeOf i = f.degreeOf i + c.degreeOf i :=
    hc ▸ degreeOf_mul_eq (left_ne_zero_of_mul (hc ▸ con)) (right_ne_zero_of_mul (hc ▸ con))
  rewrite [not_lt, this]
  exact Nat.le_add_right _ _

variable [DecidableEq R] [LinearOrder σ]

theorem pseudoOf_remainder_reducedTo {c : σ} (g : MvPolynomial σ R) {f : MvPolynomial σ R}
    (hc : f.mainVariable = c) : (g.pseudoOf c f).remainder.reducedTo f := by
  have : f.degreeOf c ≠ 0 := degreeOf_mainVariable_ne_zero hc
  by_cases r_zero : (g.pseudoOf c f).remainder = 0
  · simp only [r_zero, reducedTo, ↓reduceIte]
  apply (reducedTo_iff hc r_zero).mpr
  exact degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero g this

/-- A remainder `r` of `g` by `f` is a polynomial which is reduced with respect to `f` and
suffices `f.initial ^ s * g = q * f + r` for some `s : ℕ` and `q : MvPolynomial σ R`. -/
def isRemainder (r g f : MvPolynomial σ R) : Prop :=
  r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r

omit [NoZeroDivisors R] in
theorem isRemainder_def (r g f : MvPolynomial σ R) : r.isRemainder g f ↔
    r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r := Iff.rfl

/-- A remainder `r` of `g` by `S` is a polynomial which is reduced with respect to `S` and
suffices `(∏ i, (S i).initial ^ es[i]) * g = (∑ i, qs[i] * S i) + r`
for some `es : List ℕ` and `qs : List (MvPolynomial σ R)`. -/
def isSetRemainder (r g : MvPolynomial σ R) (S : TriangulatedSet σ R) : Prop := r.reducedToSet S ∧
  ∃ (es : List ℕ) (qs : List (MvPolynomial σ R)), (es.length = S.length ∧ qs.length = S.length) ∧
    (∏ i : Fin es.length, (S i).initial ^ es[i]) * g = (∑ i : Fin qs.length, qs[i] * S i) + r

omit [NoZeroDivisors R] in
theorem isSetRemainder_def (r g : MvPolynomial σ R) (S : TriangulatedSet σ R) :
    r.isSetRemainder g S ↔ r.reducedToSet S ∧ ∃ (es : List ℕ) (qs : List (MvPolynomial σ R)),
      (es.length = S.length ∧ qs.length = S.length) ∧
      (∏ i : Fin es.length, (S i).initial ^ es[i]) * g = (∑ i : Fin qs.length, qs[i] * S i) + r
  := Iff.rfl

end CommRing

section Field

variable {R σ : Type*} [Field R] [DecidableEq R] [LinearOrder σ] (g f : MvPolynomial σ R)

/-- General pseudo-division of `g` by `f`.
If `f` is constant, it performs standard division.
If `f` is non-constant, it performs pseudo-division with respect to `mainVariable(f)`. -/
noncomputable def pseudo : PseudoResult (MvPolynomial σ R) :=
  if f = 0 then ⟨0, 0, g⟩
  else
    match f.mainVariable with
    | ⊥ => ⟨0, (f.coeff 0)⁻¹ • g, 0⟩
    | some c => g.pseudoOf c f

@[simp] theorem pseudo_zero {g : MvPolynomial σ R} : g.pseudo 0 = ⟨0, 0, g⟩ := by
  rw [pseudo, if_pos]; rfl

@[simp] theorem pseudo_C {g : MvPolynomial σ R} {r : R} (hr : r ≠ 0) :
    g.pseudo (C r) = ⟨0, r⁻¹ • g, 0⟩ := by
  have : (C r : MvPolynomial σ R) ≠ 0 := C_ne_zero.mpr hr
  simp only [pseudo, this, reduceIte, mainVariable_C, coeff_C]

@[simp] theorem zero_pseudo : (0 : MvPolynomial σ R).pseudo f = ⟨0, 0, 0⟩ := by
  simp only [pseudo, smul_zero, zero_pseudoOf, ite_eq_left_iff]
  intro _
  match hc : f.mainVariable with
  | ⊥ => simp only
  | some c =>
    simp only [PseudoResult.mk.injEq, and_self, and_true]
    rw [Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero <| degreeOf_mainVariable_ne_zero hc)]

@[simp] theorem pseudo_remainder_self : (f.pseudo f).remainder = 0 := by
  simp only [pseudo, pseudoOf_self]
  split_ifs with h
  · rw [h]
  split <;> simp only

theorem pseudo_of_mainVariable_isSome {c : σ} {f : MvPolynomial σ R} :
    f.mainVariable = c → g.pseudo f = g.pseudoOf c f := fun h ↦ by
  simp only [pseudo, ne_zero_of_mainVariable_ne_bot (h ▸ WithBot.coe_ne_bot), h, reduceIte]

theorem pseudo_equation :
    f.initial ^ (g.pseudo f).exponent * g = (g.pseudo f).quotient * f + (g.pseudo f).remainder := by
  unfold pseudo
  split_ifs with f_zero
  · rw [pow_zero, one_mul, zero_mul, zero_add]
  match hc : f.mainVariable with
  | ⊥ =>
    have ⟨r, hr⟩ : ∃ r, f = C r := mainVariable_eq_bot_iff_eq_C.mp hc
    simp only [pow_zero, one_mul, Algebra.smul_mul_assoc, add_zero]
    simp only [hr, coeff_C, reduceIte] at f_zero ⊢
    have : r ≠ 0 := C_ne_zero.mp f_zero
    rw [mul_comm, ← smul_eq_C_mul, ← mul_smul, inv_mul_cancel₀ this, one_smul]
  | some c => simp only [initial_of_mainVariable_isSome' hc]; exact g.pseudoOf_equation c f

theorem degreeOf_pseudo_remainder_le_of_degreeOf_eq_zero {i : σ} {f : MvPolynomial σ R}
    (h : f.degreeOf i = 0) : (g.pseudo f).remainder.degreeOf i ≤ g.degreeOf i := by
  unfold pseudo
  split_ifs with f_zero
  · exact Nat.le_refl _
  match hc : f.mainVariable with
  | ⊥ => simp only [degreeOf_zero, zero_le]
  | some c =>
    have : c ≠ i := by contrapose! h; exact degreeOf_mainVariable_ne_zero <| h ▸ hc
    exact degreeOf_pseudoOf_remainder_le_of_degreeOf_eq_zero g this h

theorem pseudo_remainder_reducedTo (h : f ≠ 0) : (g.pseudo f).remainder.reducedTo f := by
  rewrite [pseudo, if_neg h]
  match h : f.mainVariable with
  | ⊥ => simp only; trivial
  | some c => exact g.pseudoOf_remainder_reducedTo h

theorem pseudo_remainder_isRemainder (h : f ≠ 0) : (g.pseudo f).remainder.isRemainder g f :=
  ⟨g.pseudo_remainder_reducedTo f h, _, _, g.pseudo_equation f⟩

theorem isRemainder_of_eq_pseudo_remainder {r g f : MvPolynomial σ R} (h : f ≠ 0) :
    (g.pseudo f).remainder = r → r.isRemainder g f := fun hr ↦
  hr ▸ g.pseudo_remainder_isRemainder f h

theorem pseudo_remainder_eq_zero_of_dvd {g f : MvPolynomial σ R} (h : f ∣ g) :
    (g.pseudo f).remainder = 0 := by
  unfold pseudo
  split <;> expose_names
  · simpa [h_1] using h
  match hc : f.mainVariable with
  | ⊥ => simp only
  | some c => exact pseudoOf_remainder_eq_zero_of_dvd h <| degreeOf_mainVariable_ne_zero hc

theorem pseudo_remainder_eq_of_degreeOf_eq_zero {g f : MvPolynomial σ R} {c : σ}
    (h1 : f.mainVariable = some c) (h2 : g.degreeOf c = 0) : (g.pseudo f).remainder = g := by
  unfold pseudo
  split <;> expose_names
  · simp only
  simp only [h1]
  exact pseudoOf_remainder_eq_of_degreeOf_eq_zero h2 <| degreeOf_mainVariable_ne_zero h1

open TriangulatedSet List

variable (S : TriangulatedSet σ R)

/-- The recursive algorithm of successive pseudo-division by a triangulated set -/
noncomputable def setPseudo.go (f : ℕ → MvPolynomial σ R) (fuel : ℕ) (es : List ℕ)
    (qs : List (MvPolynomial σ R)) (r : MvPolynomial σ R) : SetPseudoResult (MvPolynomial σ R) :=
  if fuel = 0 then ⟨es, qs, r⟩
  else
    let p := r.pseudo (f (fuel - 1))
    let es' := p.exponent :: es
    let qs' := p.quotient :: qs.map (· * (f (fuel - 1)).initial ^ p.exponent)
    let r' := p.remainder
    go f (fuel - 1) es' qs' r'

/-- Pseudo-divides `g` successively by elements of `S`.
Typically, this involves dividing by `Sₗ₋₁`, then `Sₗ₋₂`, ..., down to `S₀`. -/
noncomputable def setPseudo : SetPseudoResult (MvPolynomial σ R) :=
  setPseudo.go S S.length [] [] g

lemma length_setPseudoGo (f : ℕ → MvPolynomial σ R) (fuel : ℕ) : ∀ (es : List ℕ) (qs) (r),
    (setPseudo.go f fuel es qs r).exponents.length = es.length + fuel ∧
    (setPseudo.go f fuel es qs r).quotients.length = qs.length + fuel := by
  induction fuel with
  | zero => simp only [setPseudo.go, ↓reduceIte, add_zero, and_self, implies_true]
  | succ fuel ih =>
    intro eq qs r
    unfold setPseudo.go
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    simp only [(ih ..).1, (ih ..).2, length_cons, length_map]
    exact ⟨by ring, by ring⟩

theorem length_setPseudo_exponents : (g.setPseudo S).exponents.length = S.length := by
  rw [setPseudo, (length_setPseudoGo ..).1, length_nil, zero_add]

theorem length_setPseudo_quotients : (g.setPseudo S).quotients.length = S.length := by
  rw [setPseudo, (length_setPseudoGo ..).2, length_nil, zero_add]

lemma setPseudoGo_equation (f : ℕ → MvPolynomial σ R) (fuel : ℕ) : ∀ (es : List ℕ) (qs) (r),
    es.foldrIdx (fun i e I ↦ (f i).initial ^ e * I) 1 fuel * g =
      qs.foldrIdx (fun i q Q ↦ q * f i + Q) 0 fuel + r →
    letI result := setPseudo.go f fuel es qs r;
    result.exponents.foldrIdx (fun i e I ↦ (f i).initial ^ e * I) 1 * g =
      result.quotients.foldrIdx (fun i q Q ↦ q * f i + Q) 0 + result.remainder := by
  induction fuel with
  | zero => simp only [setPseudo.go, ↓reduceIte, imp_self, implies_true]
  | succ fuel ih =>
    intro es qs r heq
    let p := r.pseudo (f fuel)
    let es' := p.exponent :: es
    let qs' := p.quotient :: qs.map (· * (f fuel).initial ^ p.exponent)
    let r' := p.remainder
    have hp : (f fuel).initial ^ p.exponent * r = p.quotient * f fuel + p.remainder :=
      r.pseudo_equation (f fuel)
    have : setPseudo.go f (fuel + 1) es qs r = setPseudo.go f fuel es' qs' r' := by
      rewrite [setPseudo.go]; simp; rfl
    have heq' : es'.foldrIdx (fun i e I ↦ (f i).initial ^ e * I) 1 fuel * g =
        qs'.foldrIdx (fun i q Q ↦ q * f i + Q) 0 fuel + r' := by
      unfold es' qs' r'
      simp only [foldrIdx]
      have (n : ℕ) (r : MvPolynomial σ R) (qs : List (MvPolynomial σ R)) :
          r * qs.foldrIdx (fun i q Q ↦ q * f i + Q) 0 n
            = (qs.map (fun q ↦ q * r)).foldrIdx (fun i q Q ↦ q * f i + Q) 0 n := by
        induction qs generalizing n with
        | nil => simp only [foldrIdx, mul_zero, map_nil]
        | cons q qs hq =>
          simp only [foldrIdx, map_cons, foldrIdx_cons]
          rw [mul_add, hq (n + 1), mul_comm q r, mul_assoc]
      rewrite [mul_assoc, heq, mul_add, hp, ← this]
      ring
    rw [this, ih es' qs' r' heq']

theorem setPseudo_equation' : letI result := g.setPseudo S
    result.exponents.foldrIdx (fun i e I ↦ (S i).initial ^ e * I) 1 * g
      = result.quotients.foldrIdx (fun i q Q ↦ q * S i + Q) 0 + result.remainder :=
  g.setPseudoGo_equation _ _ _ _ _ (by simp only [foldrIdx, one_mul, zero_add])

theorem setPseudo_equation : letI result := g.setPseudo S
    (∏ i : Fin result.exponents.length, (S i).initial ^ result.exponents[i]) * g
    = (∑ i : Fin result.quotients.length, result.quotients[i] * S i) + result.remainder := by
  have hes (es : List ℕ) (S : ℕ → MvPolynomial σ R) : es.foldrIdx (fun i e I ↦ (S i) ^ e * I) 1
      = (∏ i ∈ Finset.range es.length, (S i) ^ es.getD i 0) := by
    induction es generalizing S with
    | nil => simp
    | cons e es ih =>
      simp only [foldrIdx, zero_add, length_cons]
      rewrite [foldrIdx_start, ih, add_comm _ 1, Finset.prod_range_add, Finset.prod_range_one]
      simp [add_comm]
  have hqs (qs : List (MvPolynomial σ R)) (S : ℕ → MvPolynomial σ R) :
      qs.foldrIdx (fun i q Q ↦ q * S i + Q) 0
        = (∑ i ∈ Finset.range qs.length, qs.getD i 0 * S i) := by
    induction qs generalizing S with
    | nil => simp
    | cons q qs ih =>
      simp only [foldrIdx, zero_add, length_cons]
      rewrite [foldrIdx_start, ih, add_comm _ 1, Finset.sum_range_add, Finset.sum_range_one]
      simp [add_comm]
  simpa [hes, hqs, Finset.prod_range, Finset.sum_range] using g.setPseudo_equation' S

/-- The remainder of pseudo-dividing `g` by the set `S`.
This is computationally simpler than `setPseudo` if only the remainder is needed. -/
noncomputable def setPseudoRem : MvPolynomial σ R :=
  S.toList.foldr (fun p r ↦ (r.pseudo p).remainder) g

theorem zero_setPseudoRem (l : List (MvPolynomial σ R)) :
    l.foldr (fun p r : MvPolynomial σ R ↦ (r.pseudo p).remainder) 0 = 0 := by
  induction l with
  | nil => simp only [foldr_nil]
  | cons a l ih => simp only [foldr_cons, ih, zero_pseudo]

lemma setPseudoGo_drop_succ_remainder_eq {k n : ℕ} (hn : n < k) (hk : k ≤ S.length) : ∀ es qs r,
    (setPseudo.go (S.drop (k - (n + 1))) (n + 1) es qs r).remainder =
    ((setPseudo.go (S.drop (k - n)) n es qs r).remainder.pseudo (S (k - (n + 1)))).remainder := by
  induction n generalizing k with
  | zero => simp [setPseudo.go]
  | succ n ih =>
    intro es qs r
    have ih := ih (Nat.lt_sub_of_add_lt hn) (le_trans (Nat.sub_le k 1) hk)
    rewrite [Nat.Simproc.sub_add_eq_comm k (n + 1) 1, setPseudo.go]
    nth_rewrite 2 [setPseudo.go]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, ↓reduceIte,
      add_tsub_cancel_right, drop_apply, ih]
    have : n + 1 + (k - 1 - (n + 1)) = n + (k - (n + 1)) := by
      have : n + 1 ≤ k - 1 := Nat.le_sub_one_of_lt hn
      rw [← Nat.add_sub_assoc this, Nat.succ_add_eq_add_succ, Nat.succ_eq_add_one,
        Nat.sub_add_cancel <| Nat.one_le_of_lt hn, Nat.add_sub_assoc <| Nat.le_of_succ_le hn]
    rw [this, Nat.Simproc.sub_add_eq_comm]

theorem setPseudo_remainder_eq_setPseudoRem : (g.setPseudo S).remainder = g.setPseudoRem S := by
  unfold setPseudo setPseudoRem
  induction h : S.length generalizing S with
  | zero => simp [setPseudo.go, List.eq_nil_of_length_eq_zero (h ▸ length_toList S)]
  | succ n ih =>
    have := setPseudoGo_drop_succ_remainder_eq S (lt_add_one n) (h ▸ le_refl _) ([]) ([]) g
    simp only [tsub_self, TriangulatedSet.drop_zero, add_tsub_cancel_left] at this
    rewrite [this, ih _ (by simp [h, add_tsub_cancel_right]), toList_drop_comm, drop_one]
    have h : S.toList ≠ [] := length_pos_iff.mp (length_toList S ▸ h ▸ Nat.zero_lt_succ n)
    rw [← cons_head_tail h, foldr_cons, cons_head_tail, head_eq_getElem_zero, toList_getElem]

lemma setPseudoRem_reducedTo (l : List (MvPolynomial σ R)) (hl1 : ∀ ⦃p⦄, p ∈ l → p ≠ 0)
    (hl2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) : ∀ g p : MvPolynomial σ R, p ∈ l →
    (l.foldr (fun p r ↦ (r.pseudo p).remainder) g).reducedTo p := by
  induction l with
  | nil => simp only [not_mem_nil, foldr_nil, IsEmpty.forall_iff, implies_true]
  | cons a l ih =>
    intro g p hp
    rw [foldr_cons]
    rcases eq_or_mem_of_mem_cons hp with hp | hp
    · exact hp.symm ▸ pseudo_remainder_reducedTo _ a (hl1 mem_cons_self)
    have ih := ih (fun p hp ↦ hl1 <| mem_cons_of_mem _ hp) (pairwise_cons.mp hl2).2 g p hp
    set r' := l.foldr (fun p r ↦ (r.pseudo p).remainder) g
    rw [reducedTo] at ih ⊢
    split_ifs with hr'
    have r'_ne_zero : r' ≠ 0 := fun h ↦ by absurd hr'; simp only [h, zero_pseudo]
    rewrite [if_neg r'_ne_zero] at ih
    split at ih <;> expose_names
    · exact ih
    suffices (r'.pseudo a).remainder.degreeOf c ≤ r'.degreeOf c by exact lt_of_le_of_lt this ih
    apply degreeOf_pseudo_remainder_le_of_degreeOf_eq_zero
    apply degreeOf_eq_zero_of_mainVariable_lt
    apply heq ▸ (pairwise_cons.mp hl2).1 p hp

theorem setPseudo_remainder_reducedToSet : (g.setPseudo S).remainder.reducedToSet S := by
  rewrite [reducedToSet_iff, setPseudo_remainder_eq_setPseudoRem, setPseudoRem]
  intro i hi
  apply setPseudoRem_reducedTo _ toList_non_zero toList_pairwise
  exact mem_toList_iff.mpr <| apply_mem hi

theorem setPseudo_remainder_isSetRemainder : (g.setPseudo S).remainder.isSetRemainder g S :=
  ⟨g.setPseudo_remainder_reducedToSet S, _, _,
    ⟨g.length_setPseudo_exponents S, g.length_setPseudo_quotients S⟩, g.setPseudo_equation S⟩

theorem isSetRemainder_of_eq_setPseudo_remainder {r g : MvPolynomial σ R}
    {S : TriangulatedSet σ R} : (g.setPseudo S).remainder = r → r.isSetRemainder g S := fun h ↦
  h ▸ g.setPseudo_remainder_isSetRemainder S

lemma setPseudoRem_eq_self_of_mainVariable_lt (l : List (MvPolynomial σ R))
    (hl1 : ∀ ⦃p⦄, p ∈ l → p ≠ 0) (hl2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) :
    ∀ ⦃g : MvPolynomial σ R⦄, (∀ p ∈ l, g.mainVariable < p.mainVariable) →
    l.foldr (fun p r ↦ (r.pseudo p).remainder) g = g := by
  induction l with
  | nil => simp only [foldr_nil, implies_true]
  | cons a l ih =>
    intro g hg
    simp only [mem_cons, forall_eq_or_imp] at hg
    rcases WithBot.ne_bot_iff_exists.mp <| LT.lt.ne_bot hg.1 with ⟨c, hc⟩
    have ih := ih (fun p hp ↦ hl1 <| mem_cons_of_mem _ hp) (pairwise_cons.mp hl2).2 hg.2
    rw [foldr_cons, ih, pseudo_remainder_eq_of_degreeOf_eq_zero hc.symm]
    exact degreeOf_eq_zero_of_mainVariable_lt (hc ▸ hg.1)

theorem setPseudo_remainder_eq_zero_of_mem {p : MvPolynomial σ R} (hp : p ∈ S) :
    (p.setPseudo S).remainder = 0 := by
  rcases hp with ⟨n, hn1, hn2⟩
  rw [setPseudo_remainder_eq_setPseudoRem, setPseudoRem]
  let l1 := S.toList.drop (n + 1)
  let l2 := S.toList.take n
  have hmin : min n S.length = n := Nat.min_eq_left (le_of_lt hn1)
  have : S.toList = l2 ++ [p] ++ l1 := by
    have : (l2 ++ [p]).length = n + 1 := by simpa [l2] using (le_of_lt hn1)
    simp only [l1, ← this]
    refine prefix_append_drop <| prefix_iff_eq_take.mpr ?_
    have := S.length_toList ▸ hn1
    simp [l2, hmin, take_add_one, hn2 ▸ toList_getElem this ▸ getElem?_eq_getElem this]
  simp only [this, append_assoc, cons_append, nil_append, foldr_append, foldr_cons]
  suffices ((l1.foldr (fun p r ↦ (r.pseudo p).remainder) p).pseudo p).remainder = 0 by
    rw [this, zero_setPseudoRem]
  simp only [← toList_drop_comm, l1]
  refine pseudo_remainder_eq_zero_of_dvd (dvd_of_eq <| Eq.symm ?_)
  refine setPseudoRem_eq_self_of_mainVariable_lt _ toList_non_zero toList_pairwise (fun q hq ↦ ?_)
  rcases mem_toList_iff.mp hq with ⟨i, hi1, hi2⟩
  rewrite [← hn2, ← hi2, drop_apply]
  refine mainVariable_lt_of_index_lt ?_ (Nat.lt_add_left i (lt_add_one n))
  exact Nat.add_lt_of_lt_sub hi1

end Field
end MvPolynomial
