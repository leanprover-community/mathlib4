/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.Reduced
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
* `MvPolynomial.isRemainder`:
  A predicate stating that `r` is a valid remainder of `g` by `f`,
  meaning `r` is reduced w.r.t. `f` and `init(f)^s * g = q * f + r` for some `s, q`.

## Main results

* `pseudoOf_equation`: `init(f) ^ s * g = q * f + r` where `deg(r) < deg(f)`
* `pseudoOf_remainder_reducedTo`: The remainder is reduced w.r.t. the divisor
* `pseudo_remainder_isRemainder`: The remainder satisfies the `isRemainder` predicate

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]
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

/-- The result of pseudo-dividing `g` by a sequence of polynomials (a triangular set)
satisfying the equation `(∏ i, (S i).initial ^ es[i]) * g = (∑ i, qs[i] * S i) + r`. -/
structure SetPseudoResult (α : Type*) where
  /-- The powers of the initials `es`. -/
  exponents : List ℕ
  /-- The quotients `qs`. -/
  quotients : List α
  /-- The remainder `r`. -/
  remainder : α

section CommRing

variable {R σ : Type*} [CommRing R]

/-- The recursive algorithm of pseudo-division -/
noncomputable def pseudoOf.go [NoZeroDivisors R] (i : σ) (f : MvPolynomial σ R) (s : ℕ)
    (q r : MvPolynomial σ R) (h : f.degreeOf i ≠ 0) : PseudoResult (MvPolynomial σ R) :=
  if r.degreeOf i < f.degreeOf i then ⟨s, q, r⟩
  else
    letI d := r.degreeOf i
    letI Ic_r := r.initialOf i
    letI x_power := X i ^ (d - f.degreeOf i)
    let term := Ic_r * x_power
    let I := f.initialOf i
    let q' := I * q + term
    let r' := I * r - term * f
    go i f (s + 1) q' r' h
  termination_by r.degreeOf i
  decreasing_by
    expose_names
    suffices r'.degreeOf i ≤ r.degreeOf i - 1 by
      change r'.degreeOf i < r.degreeOf i
      refine (Nat.le_sub_one_iff_lt ?_).mp this
      exact lt_of_lt_of_le (Nat.ne_zero_iff_zero_lt.mp h) (Nat.not_lt.mp h_1)
    unfold r'
    have Id : I.degreeOf i = 0 := by rw [degreeOf_initialOf_self]
    have : (I * r).degreeOf i - 1 ≤ r.degreeOf i - 1 := by
      apply Nat.sub_le_sub_right
      rw [← zero_add (r.degreeOf i), ← Id]
      exact degreeOf_mul_le ..
    refine le_trans ?_ this
    apply degreeOf_sub_lt_of_initialOf_eq
    repeat1' rw [mul_assoc, mul_comm _ f, ← mul_assoc]
    · rw [initialOf_mul_X_self_pow, initialOf_mul_eq, initialOf_mul_eq]
      rw [initialOf_initialOf_self, initialOf_initialOf_self, mul_comm]
    have f_ne : f ≠ 0 := ne_zero_of_degreeOf_ne_zero h
    have I_ne : I ≠ 0 := initialOf_ne_zero i f_ne
    have r_ne : r ≠ 0 := by
      contrapose! h_1
      rw [h_1, degreeOf_zero]
      exact Nat.zero_lt_of_ne_zero h
    have Ir_ne : r.initialOf i ≠ 0 := initialOf_ne_zero i r_ne
    rw [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ (mul_ne_zero_iff.mpr ⟨Ir_ne ,f_ne⟩)]
    rw [degreeOf_mul_eq I_ne r_ne, degreeOf_mul_eq Ir_ne f_ne]
    simpa [I] using (Nat.add_sub_of_le <| Nat.le_of_not_lt h_1).symm

/-- Pseudo-division of `g` by `f` regarding the variable `i`.
This algorithm computes `q` and `r` such that `initᵢ(f) ^ s * g = q * f + r`,
where `degᵢ(r) < degᵢ(f)`.
Termination is guaranteed by `pseudoOf.go` which recurses on the degree of the remainder. -/
noncomputable def pseudoOf [NoZeroDivisors R] (i : σ) (g f : MvPolynomial σ R)
    : PseudoResult (MvPolynomial σ R) :=
  if h : f.degreeOf i = 0 then ⟨1, g, 0⟩
  else pseudoOf.go i f 0 0 g h

variable [NoZeroDivisors R] (i : σ) (g f : MvPolynomial σ R)

theorem zero_pseudoOf : (0 : MvPolynomial σ R).pseudoOf i f = ⟨1 - f.degreeOf i, 0, 0⟩ := by
  rw [pseudoOf]
  split_ifs with h
  · rw [h]
  rw [pseudoOf.go, degreeOf_zero, zero_add]
  have : 1 - f.degreeOf i = 0 := Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero h)
  simp only [Nat.pos_of_ne_zero h, this, ↓reduceIte]

theorem pseudoOf_self : f.pseudoOf i f = ⟨1, f.initialOf i, 0⟩ := by
  rw [pseudoOf]
  split_ifs with h
  · rw [initialOf_eq_of_degreeOf_eq_zero h]
  simp [pseudoOf.go, Nat.pos_of_ne_zero h]

lemma pseudoOfGo_next (h : f.degreeOf i ≠ 0) (s : ℕ) (q : MvPolynomial σ R) {r : MvPolynomial σ R}
    (hn : f.degreeOf i ≤ r.degreeOf i) :
    let term := r.initialOf i * X i ^ (r.degreeOf i - f.degreeOf i);
    pseudoOf.go i f s q r h =
      pseudoOf.go i f  (s + 1) (f.initialOf i * q + term) (f.initialOf i * r - term * f) h := by
  rw [pseudoOf.go]; simp [hn]

lemma pseudoOfGo_equation (h : f.degreeOf i ≠ 0) (s : ℕ) (q r : MvPolynomial σ R) :
    f.initialOf i ^ s * g = q * f + r → letI result := pseudoOf.go i f s q r h;
    f.initialOf i ^ result.exponent * g = result.quotient * f + result.remainder := by
  induction s, q, r using pseudoOf.go.induct i f h with
  | case1 s q r dlt => rw [pseudoOf.go]; simp only [dlt, ↓reduceIte, imp_self]
  | case2 s q r dlt term I q' r' ih =>
    intro heq
    suffices I ^ (s + 1) * g = q' * f + r' by
      rw [pseudoOfGo_next i f h s q (le_of_not_gt dlt), ih this]
    unfold q' r'
    have : (I * q + term) * f + (I * r - term * f) = I * (q * f + r) + (term - term) * f :=
      by ring
    nth_rw 1 [this, ← heq]
    ring

/-- The fundamental equation of pseudo-division: `initᵢ(f) ^ s * g = q * f + r` -/
theorem pseudoOf_equation : f.initialOf i ^ (g.pseudoOf i f).exponent * g
    = (g.pseudoOf i f).quotient * f + (g.pseudoOf i f).remainder := by
  rw [pseudoOf]
  split_ifs with h
  · rw [pow_one, add_zero, initialOf_eq_of_degreeOf_eq_zero h, mul_comm]
  exact g.pseudoOfGo_equation _ _ _ _ _ _ (by ring)

lemma degreeOf_pseudoOfGo_remainder_le_of_degreeOf_eq_zero {i j : σ} {f : MvPolynomial σ R}
    (h : f.degreeOf i ≠ 0) (hi : i ≠ j) (hj : f.degreeOf j = 0) (s : ℕ) (q r : MvPolynomial σ R) :
    (pseudoOf.go i f s q r h).remainder.degreeOf j ≤ r.degreeOf j := by
  induction s, q, r using pseudoOf.go.induct i f h with
  | case1 s q r h => rw [pseudoOf.go]; simp only [h, ↓reduceIte, Std.le_refl]
  | case2 s q r dlt term I q' r' ih =>
    apply le_trans (pseudoOfGo_next i f h s q (le_of_not_gt dlt) ▸ ih)
    apply le_trans (degreeOf_sub_le ..)
    apply max_le <;> apply le_trans (degreeOf_mul_le ..)
    · have Id : I.degreeOf j = 0 := Nat.eq_zero_of_le_zero <| hj ▸ degreeOf_initialOf_le i j f
      simp only [Id, zero_add, le_refl]
    simp only [hj, add_zero, term]
    apply le_trans (degreeOf_mul_le ..)
    rw [degreeOf_X_pow_of_ne _ hi.symm, add_zero]
    exact degreeOf_initialOf_le i j r

theorem degreeOf_pseudoOf_remainder_le_of_degreeOf_eq_zero {i j : σ} (g : MvPolynomial σ R)
    {f : MvPolynomial σ R} (hi : i ≠ j) (hj : f.degreeOf j = 0) :
    (g.pseudoOf i f).remainder.degreeOf j ≤ g.degreeOf j := by
  rw [pseudoOf]
  split_ifs with h
  · exact (@degreeOf_zero R _ _ _) ▸ Nat.zero_le _
  exact degreeOf_pseudoOfGo_remainder_le_of_degreeOf_eq_zero h hi hj ..

theorem dvd_pseudoOf_remainder_of_dvd (i : σ) {g f : MvPolynomial σ R} (h : f ∣ g) :
    f ∣ (g.pseudoOf i f).remainder := by
  rcases h with ⟨c, hc⟩
  have heq := g.pseudoOf_equation i f
  set res := g.pseudoOf i f
  rw [hc, mul_comm, mul_assoc, mul_comm _ f] at heq
  exact (dvd_add_right ⟨_, rfl⟩).mp (heq ▸ (⟨_, rfl⟩ : f ∣ f * (c * _ ^ _)))

theorem pseudoOf_remainder_eq_of_degreeOf_eq_zero {i : σ} {g f : MvPolynomial σ R}
    (h1 : g.degreeOf i = 0) (h2 : f.degreeOf i ≠ 0) : (g.pseudoOf i f).remainder = g := by
  have : g.pseudoOf i f = pseudoOf.go i f 0 0 g h2 := by simp only [pseudoOf, h2, ↓reduceDIte]
  rw [this, pseudoOf.go, h1, if_pos (Nat.ne_zero_iff_zero_lt.mp h2)]

theorem degreeOf_pseudoOfGo_remainder_lt_of_degreeOf_ne_zero {i : σ} {f : MvPolynomial σ R}
    (h : f.degreeOf i ≠ 0) (s : ℕ) (q r : MvPolynomial σ R) :
    (pseudoOf.go i f s q r h).remainder.degreeOf i < f.degreeOf i := by
  induction s, q, r using pseudoOf.go.induct i f h with
  | case1 s q r h => rw [pseudoOf.go]; simp only [h, ↓reduceIte]
  | case2 s q r dlt term I q' r' ih =>
    refine lt_of_eq_of_lt ?_ ih
    rw [pseudoOfGo_next _ _ h _ _ (Nat.not_lt.mp dlt)]

theorem degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero {i : σ} (g : MvPolynomial σ R)
    {f : MvPolynomial σ R} (h : f.degreeOf i ≠ 0) :
    (g.pseudoOf i f).remainder.degreeOf i < f.degreeOf i := by
  simp only [pseudoOf, h, ↓reduceDIte]
  exact degreeOf_pseudoOfGo_remainder_lt_of_degreeOf_ne_zero h 0 0 g

theorem pseudoOf_remainder_eq_zero_of_dvd {i : σ} {g f : MvPolynomial σ R} (h1 : f ∣ g)
    (h2 : f.degreeOf i ≠ 0) : (g.pseudoOf i f).remainder = 0 := by
  have ⟨c, hc⟩ : f ∣ (g.pseudoOf i f).remainder := dvd_pseudoOf_remainder_of_dvd i h1
  set r := (g.pseudoOf i f).remainder
  by_contra con
  absurd degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero g h2
  have : r.degreeOf i = f.degreeOf i + c.degreeOf i :=
    hc ▸ degreeOf_mul_eq (left_ne_zero_of_mul (hc ▸ con)) (right_ne_zero_of_mul (hc ▸ con))
  rw [not_lt, this]
  exact Nat.le_add_right _ _

variable [DecidableEq R] [LinearOrder σ]

theorem pseudoOf_remainder_reducedTo {c : σ} (g : MvPolynomial σ R) {f : MvPolynomial σ R}
    (hc : f.vars.max = c) : (g.pseudoOf c f).remainder.reducedTo f := by
  have : f.degreeOf c ≠ 0 := degreeOf_max_vars_ne_zero hc
  by_cases r_zero : (g.pseudoOf c f).remainder = 0
  · simp only [r_zero, reducedTo, ↓reduceIte]
  apply (reducedTo_iff hc r_zero).mpr
  exact degreeOf_pseudoOf_remainder_lt_of_degreeOf_ne_zero g this

/-- A remainder `r` of `g` by `f` is a polynomial which is reduced with respect to `f` and
suffices `f.initial ^ s * g = q * f + r` for some `s : ℕ` and `q : MvPolynomial σ R`. -/
def IsRemainder (r g f : MvPolynomial σ R) : Prop :=
  r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r

omit [NoZeroDivisors R] in
theorem isRemainder_def (r g f : MvPolynomial σ R) : r.IsRemainder g f ↔
    r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r := Iff.rfl

end CommRing

section Field

variable {R σ : Type*} [Field R] [DecidableEq R] [LinearOrder σ] (g f : MvPolynomial σ R)

/-- General pseudo-division of `g` by `f`.
If `f` is constant, it performs standard division.
If `f` is non-constant, it performs pseudo-division with respect to `max_vars(f)`. -/
noncomputable def pseudo : PseudoResult (MvPolynomial σ R) :=
  if f = 0 then ⟨0, 0, g⟩
  else
    match f.vars.max with
    | ⊥ => ⟨0, (f.coeff 0)⁻¹ • g, 0⟩
    | some c => g.pseudoOf c f

@[simp] theorem pseudo_zero {g : MvPolynomial σ R} : g.pseudo 0 = ⟨0, 0, g⟩ := by
  rw [pseudo, if_pos]; rfl

@[simp] theorem pseudo_C {g : MvPolynomial σ R} {r : R} (hr : r ≠ 0) :
    g.pseudo (C r) = ⟨0, r⁻¹ • g, 0⟩ := by
  have : (C r : MvPolynomial σ R) ≠ 0 := C_ne_zero.mpr hr
  simp only [pseudo, this, ↓reduceIte, vars_C, Finset.max_empty, coeff_C]

@[simp] theorem zero_pseudo : (0 : MvPolynomial σ R).pseudo f = ⟨0, 0, 0⟩ := by
  simp only [pseudo, smul_zero, zero_pseudoOf, ite_eq_left_iff]
  intro _
  match hc : f.vars.max with
  | ⊥ => simp only
  | some c =>
    simp only [PseudoResult.mk.injEq, and_self, and_true]
    rw [Nat.sub_eq_zero_of_le (Nat.pos_of_ne_zero <| degreeOf_max_vars_ne_zero hc)]

@[simp] theorem pseudo_remainder_self : (f.pseudo f).remainder = 0 := by
  simp only [pseudo, pseudoOf_self]
  split_ifs with h
  · rw [h]
  split <;> simp only

theorem pseudo_of_max_vars_isSome {c : σ} {f : MvPolynomial σ R} :
    f.vars.max = c → g.pseudo f = g.pseudoOf c f := fun h ↦ by
  have : f ≠ 0 := fun hf ↦ absurd (h ▸ WithBot.coe_ne_bot) (by simp [hf])
  simp only [pseudo, this, h, reduceIte]

theorem pseudo_equation :
    f.initial ^ (g.pseudo f).exponent * g = (g.pseudo f).quotient * f + (g.pseudo f).remainder := by
  unfold pseudo
  split_ifs with f_zero
  · rw [pow_zero, one_mul, zero_mul, zero_add]
  match hc : f.vars.max with
  | ⊥ =>
    have hf_C : f = C (f.coeff 0) := vars_eq_empty_iff_eq_C.mp <| Finset.max_eq_bot.mp hc
    simp only [pow_zero, one_mul, Algebra.smul_mul_assoc, add_zero]
    nth_rw 2 [hf_C]
    have : f.coeff 0 ≠ 0 := C_ne_zero.mp <| hf_C ▸ f_zero
    rw [mul_comm, ← smul_eq_C_mul, ← mul_smul, inv_mul_cancel₀ this, one_smul]
  | some c => simp only [initial_of_max_vars_isSome' hc]; exact g.pseudoOf_equation c f

theorem degreeOf_pseudo_remainder_le_of_degreeOf_eq_zero {i : σ} {f : MvPolynomial σ R}
    (h : f.degreeOf i = 0) : (g.pseudo f).remainder.degreeOf i ≤ g.degreeOf i := by
  unfold pseudo
  split_ifs with f_zero
  · exact Nat.le_refl _
  match hc : f.vars.max with
  | ⊥ => simp only [degreeOf_zero, zero_le]
  | some c =>
    have : c ≠ i := by contrapose! h; exact degreeOf_max_vars_ne_zero <| h ▸ hc
    exact degreeOf_pseudoOf_remainder_le_of_degreeOf_eq_zero g this h

theorem pseudo_remainder_reducedTo (h : f ≠ 0) : (g.pseudo f).remainder.reducedTo f := by
  rw [pseudo, if_neg h]
  match h : f.vars.max with
  | ⊥ => simp only; trivial
  | some c => exact g.pseudoOf_remainder_reducedTo h

theorem pseudo_remainder_isRemainder (h : f ≠ 0) : (g.pseudo f).remainder.IsRemainder g f :=
  ⟨g.pseudo_remainder_reducedTo f h, _, _, g.pseudo_equation f⟩

theorem isRemainder_of_eq_pseudo_remainder {r g f : MvPolynomial σ R} (h : f ≠ 0) :
    (g.pseudo f).remainder = r → r.IsRemainder g f := fun hr ↦
  hr ▸ g.pseudo_remainder_isRemainder f h

theorem pseudo_remainder_eq_zero_of_dvd {g f : MvPolynomial σ R} (h : f ∣ g) :
    (g.pseudo f).remainder = 0 := by
  unfold pseudo
  split <;> expose_names
  · simpa [h_1] using h
  match hc : f.vars.max with
  | ⊥ => simp only
  | some c => exact pseudoOf_remainder_eq_zero_of_dvd h <| degreeOf_max_vars_ne_zero hc

theorem pseudo_remainder_eq_of_degreeOf_eq_zero {g f : MvPolynomial σ R} {c : σ}
    (h1 : f.vars.max = some c) (h2 : g.degreeOf c = 0) : (g.pseudo f).remainder = g := by
  unfold pseudo
  split <;> expose_names
  · simp only
  simp only [h1]
  exact pseudoOf_remainder_eq_of_degreeOf_eq_zero h2 <| degreeOf_max_vars_ne_zero h1

end Field

end MvPolynomial
