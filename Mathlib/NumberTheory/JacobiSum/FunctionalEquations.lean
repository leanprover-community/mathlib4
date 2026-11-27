/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: moltdog
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Functional equations for Jacobi sums

This file proves the standard functional equations satisfied by Jacobi sums `J(χ, φ)`
of multiplicative characters `χ, φ` on a finite field `F` (see `jacobiSum`), together
with their consequences for Gauss sums.

## Main results

* `jacobiSum_eq_apply_neg_one_mul_jacobiSum_inv`: the `S₃` symmetry
  `J(A, B) = A(−1) * J(A, (AB)⁻¹)`, obtained from the involution `x ↦ x/(x-1)`
  on `F \ {0, 1}`.
* `jacobiSum_self_eq`: the *doubling formula* `J(A, A) = A(4)⁻¹ * J(A, ε)`, where `ε`
  is the quadratic character of `F`; equivalently `A(4) * J(A, A) = J(A, ε)`
  (`apply_four_mul_jacobiSum_self`).
* `eq_quadChar_of_sq_eq_one`: uniqueness of the nontrivial quadratic character;
  any `η` with `η^2 = 1`, `η ≠ 1` equals `quadChar F R`.
* `jacobiSum_pow_pred`: the *tower law*. If `χ` has order `2^s` with `s ≥ 2`, then
  `J(χ^{2^{s-1}-1}, χ^{2^{s-1}-1}) = χ(4)^2 * J(χ, χ)`.
* `gaussSum_quadChar_mul`: the *twist identity* for Gauss sums,
  `τ(εX) * τ(X) = X(4)⁻¹ * τ(ε) * τ(X^2)`.
* `jacobiSum_descent`: the *descent identity*
  `J(εA, εB) * (AB)(4) * J(A, B) * J(AB, AB) = ε(−1) * #F * J(A^2, B^2)`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
  (Chapter 8)][IrelandRosen1990]
* [B. C. Berndt, R. J. Evans, K. S. Williams, *Gauss and Jacobi Sums*][BerndtEvansWilliams1998]
-/

@[expose] public section

open Finset

/-- The quadratic character of `F`, viewed as an `R`-valued multiplicative character:
`quadraticChar F` composed with the canonical ring homomorphism `ℤ →+* R`. -/
noncomputable abbrev quadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (R : Type*) [CommRing R] : MulChar F R :=
  (quadraticChar F).ringHomComp (algebraMap ℤ R)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
### The `S₃` symmetry

The substitution `x ↦ x / (x - 1)` is an involution of `F \ {0, 1}` that implements
`J(A, B) = A(−1) * J(A, (AB)⁻¹)`. Together with `jacobiSum_comm` this generates the
full `S₃` action on Jacobi sums.
-/

section ThreeSym

variable {R : Type*} [CommRing R]

/-- The involution `x ↦ x / (x - 1)` maps `univ \ {0, 1}` to itself. -/
lemma div_sub_one_mem {x : F} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    x / (x - 1) ∈ (univ : Finset F) \ ({0, 1} : Finset F) := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.mem_insert, Finset.mem_singleton]
  refine not_or.mpr ⟨?_, ?_⟩
  · exact fun h => hx0 ((div_eq_zero_iff.mp h).resolve_right hx1')
  · exact fun h =>
      one_ne_zero (by linear_combination (div_eq_one_iff_eq hx1').mp h : (1 : F) = 0)

omit [Fintype F] [DecidableEq F] in
/-- The map `x ↦ x / (x - 1)` is involutive away from `1`. -/
theorem div_sub_one_invol {x : F} (hx1 : x ≠ 1) :
    x / (x - 1) / (x / (x - 1) - 1) = x := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  field_simp
  ring

/-- The `S₃` symmetry of the Jacobi sum: `J(A, B) = A(−1) * J(A, (AB)⁻¹)`.
The involution `x ↦ x/(x−1)` on `F \ {0,1}` carries the summand
`A(x) * (AB)⁻¹(1−x)` to `A(−1) * A(t) * B(1−t)`; all boundary terms vanish. -/
theorem jacobiSum_eq_apply_neg_one_mul_jacobiSum_inv (A B : MulChar F R) :
    jacobiSum A B = A (-1) * jacobiSum A (A * B)⁻¹ := by
  have hA1 : A (-1) * A (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have hbij : ∑ x ∈ univ \ ({0, 1} : Finset F), A x * (A * B)⁻¹ (1 - x)
      = A (-1) * ∑ x ∈ univ \ ({0, 1} : Finset F), A x * B (1 - x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij (fun x => x / (x - 1)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and] at hx
      exact div_sub_one_mem hx.1 hx.2
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and] at hx hy
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hy0, hy1⟩ := hy
      have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have hy1' : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
      have hmul : x * (y - 1) = y * (x - 1) := (div_eq_div_iff hx1' hy1').mp hxy
      exact sub_eq_zero.mp (by linear_combination -hmul : x - y = (0 : F))
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and] at ht
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨t / (t - 1), ?_, div_sub_one_invol ht1⟩
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and]
      have h := div_sub_one_mem ht0 ht1
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and] at h
      exact h
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have h1t : 1 - x / (x - 1) = -(x - 1)⁻¹ := by field_simp; ring
      have hAB : (A * B)⁻¹ (1 - x) =
          A (-1) * A (x - 1)⁻¹ * B (-1) * B (x - 1)⁻¹ := by
        have h2 : (1 - x)⁻¹ = -(x - 1)⁻¹ := by rw [← neg_sub, inv_neg]
        rw [MulChar.inv_apply', h2, MulChar.mul_apply, ← neg_one_mul, map_mul, map_mul]
        ac_rfl
      have hAt : A (x / (x - 1)) = A x * A (x - 1)⁻¹ := by
        rw [div_eq_mul_inv, map_mul]
      have hBt : B (1 - x / (x - 1)) = B (-1) * B (x - 1)⁻¹ := by
        rw [h1t, ← neg_one_mul, map_mul]
      rw [hAB, hAt, hBt]
      ring
  rw [jacobiSum_eq_sum_sdiff, jacobiSum_eq_sum_sdiff, hbij, ← mul_assoc, hA1, one_mul]

end ThreeSym

/-!
### The doubling formula

The substitution `z = 1 - 2x` turns `x(1-x)` into `(1 - z^2)/4`; counting the fibers
`{z : z^2 = t}` via `quadraticChar_card_sqrts` gives `A(4) * J(A, A) = J(A, ε)`.
-/

section Doubling

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The doubling formula for Jacobi sums (product form):
`A(4) * J(A, A) = J(A, ε)` for `A` nontrivial and `2 ≠ 0` in `F`. -/
theorem apply_four_mul_jacobiSum_self (h2 : (2 : F) ≠ 0) {A : MulChar F R}
    (hA : A ≠ 1) : A 4 * jacobiSum A A = jacobiSum A (quadChar F R) := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero h2 h2
  have hrc : ringChar F ≠ 2 := fun h =>
    h2 (by simpa [h] using CharP.cast_eq_zero F (ringChar F))
  -- the reparametrizations x ↦ 1 − 2x and t ↦ 1 − t
  have hbij : Function.Bijective (fun x : F => 1 - 2 * x) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun z => (1 - z) * 2⁻¹,
       fun x => by
         show (1 - (1 - 2 * x)) * 2⁻¹ = x
         rw [sub_sub_cancel, mul_comm 2, mul_assoc, mul_inv_cancel₀ h2, mul_one],
       fun z => by
         show 1 - 2 * ((1 - z) * 2⁻¹) = z
         rw [mul_comm 2, mul_assoc, inv_mul_cancel₀ h2, mul_one, sub_sub_cancel]⟩
  have hsub : Function.Bijective (fun t : F => 1 - t) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun t => 1 - t, fun t => sub_sub_cancel 1 t, fun t => sub_sub_cancel 1 t⟩
  -- step 1: A(4)·J(A,A) = ∑ z, A (1 - z²)   [x(1−x) = (1−z²)/4 under z = 1−2x]
  have step1 : A 4 * jacobiSum A A = ∑ z : F, A (1 - z ^ 2) := by
    unfold jacobiSum
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective _ hbij _ _ fun x => ?_
    have hkey : (1 : F) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) := by ring
    rw [hkey, map_mul, ← map_mul]
  -- step 2: ∑ z, A (1 - z²) = J(A, ε)   [fiber count via quadraticChar_card_sqrts]
  have step2 : ∑ z : F, A (1 - z ^ 2) = jacobiSum A (quadChar F R) := by
    unfold jacobiSum
    have hfib : ∑ z : F, A (1 - z ^ 2) =
        ∑ t : F, ∑ z ∈ univ.filter (fun z => z ^ 2 = t), A (1 - t) := by
      simpa using
        (Finset.sum_fiberwise' (univ : Finset F) (fun z : F => z ^ 2)
          (fun t => A (1 - t))).symm
    have hcard : ∀ t : F,
        ((univ.filter (fun z => z ^ 2 = t)).card : R) = quadChar F R t + 1 := by
      intro t
      have hset : (univ.filter (fun z : F => z ^ 2 = t)) =
          {x : F | x ^ 2 = t}.toFinset := by
        ext z; simp
      have key := congr_arg (algebraMap ℤ R ·) (quadraticChar_card_sqrts (F := F) hrc t)
      rw [hset]
      simp only [MulChar.ringHomComp_apply, eq_intCast, Int.cast_natCast,
        Int.cast_add, Int.cast_one] at key ⊢
      exact key
    calc ∑ z : F, A (1 - z ^ 2)
        = ∑ t : F, ((univ.filter (fun z => z ^ 2 = t)).card : R) * A (1 - t) := by
          rw [hfib]
          exact sum_congr rfl fun t _ => by rw [sum_const, nsmul_eq_mul]
      _ = ∑ t : F, (quadChar F R t * A (1 - t) + A (1 - t)) := by
          refine sum_congr rfl fun t _ => ?_
          rw [hcard t, add_mul, one_mul]
      _ = ∑ t : F, quadChar F R t * A (1 - t) + ∑ t : F, A (1 - t) := sum_add_distrib
      _ = ∑ x : F, A x * quadChar F R (1 - x) := by
          rw [Fintype.sum_bijective _ hsub (fun t => quadChar F R t * A (1 - t))
            (fun x => A x * quadChar F R (1 - x))
            (fun t => by rw [sub_sub_cancel, mul_comm]),
           Fintype.sum_bijective _ hsub (fun t => A (1 - t)) (fun x => A x)
            (fun t => rfl),
           MulChar.sum_eq_zero_of_ne_one hA, add_zero]
  rw [step1, step2]

variable {F' : Type*} [Field F']

/-- The doubling formula for Jacobi sums (Ireland–Rosen, Theorem 8.3.1-style):
`J(A, A) = A(4)⁻¹ * J(A, ε)` for `A` nontrivial and `2 ≠ 0` in `F`. -/
theorem jacobiSum_self_eq (h2 : (2 : F) ≠ 0) {A : MulChar F F'} (hA : A ≠ 1) :
    jacobiSum A A = (A 4)⁻¹ * jacobiSum A (quadChar F F') := by
  have h4 : A (4 : F) ≠ 0 := by
    have h4' : (4 : F) ≠ 0 := by
      have h : (4 : F) = 2 * 2 := by norm_num
      rw [h]; exact mul_ne_zero h2 h2
    exact MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr h4')
  have h := apply_four_mul_jacobiSum_self h2 hA
  rw [← h, ← mul_assoc, inv_mul_cancel₀ h4, one_mul]

end Doubling

/-!
### Uniqueness of the quadratic character
-/

section Uniqueness

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Any nontrivial `R`-valued multiplicative character `η` on `F` with `η^2 = 1`
equals the quadratic character `quadChar F R` (for `F` of odd characteristic). -/
theorem eq_quadChar_of_sq_eq_one (_hrc : ringChar F ≠ 2)
    {η : MulChar F R} (hη : η ^ 2 = 1) (hη1 : η ≠ 1) : η = quadChar F R := by
  have hηq : η.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hη
  have hsq_one : ∀ {x : F}, IsSquare x → x ≠ 0 → η x = 1 := by
    intro x hx hx0
    obtain ⟨b, hb⟩ := hx
    have hb0 : b ≠ 0 := fun h => hx0 (by rw [hb, h, mul_zero])
    rcases hηq b with h0 | h1 | hneg
    · exact absurd h0 (MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hb0))
    · rw [hb, map_mul, h1, mul_one]
    · rw [hb, map_mul, hneg, neg_mul_neg, one_mul]
  apply MulChar.ext
  intro a
  have ha : ((a : Fˣ) : F) ≠ 0 := (a.isUnit).ne_zero
  show η (a : F) = quadChar F R (a : F)
  rw [show quadChar F R (a : F) = algebraMap ℤ R (quadraticChar F (a : F)) from rfl]
  by_cases hs : IsSquare (a : F)
  · rw [hsq_one hs ha, (quadraticChar_one_iff_isSquare ha).mpr hs, map_one]
  · have hneg : η (a : F) = -1 := by
      rcases hηq (a : F) with h0 | h1 | hneg
      · exact absurd h0
          (MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))
      · exfalso
        apply hη1
        apply MulChar.ext
        intro x
        show η (x : F) = (1 : MulChar F R) (x : F)
        have hx : ((x : Fˣ) : F) ≠ 0 := (x.isUnit).ne_zero
        rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
        by_cases hxs : IsSquare (x : F)
        · exact hsq_one hxs hx
        · have hxa : IsSquare ((x : F) * (a : F)⁻¹) := by
            rw [← quadraticChar_one_iff_isSquare
              (mul_ne_zero hx (inv_ne_zero ha)), map_mul,
              quadraticChar_neg_one_iff_not_isSquare.mpr hxs,
              quadraticChar_neg_one_iff_not_isSquare.mpr
                (fun hsa => hs (isSquare_inv.mp hsa)),
              neg_mul_neg, one_mul]
          have key : η (x : F) = η (a : F) * η ((x : F) * (a : F)⁻¹) := by
            have hxa' : (a : F) * ((x : F) * (a : F)⁻¹) = (x : F) := by
              rw [mul_comm (a : F), mul_assoc, inv_mul_cancel₀ ha, mul_one]
            nth_rw 1 [← hxa']
            rw [map_mul]
          rw [key, h1, hsq_one hxa (mul_ne_zero hx (inv_ne_zero ha)), mul_one]
      · exact hneg
    rw [hneg, quadraticChar_neg_one_iff_not_isSquare.mpr hs]
    simp

end Uniqueness

/-!
### The tower law
-/

section Tower

variable {F' : Type*} [Field F']

/-- The *tower law*: for `χ` of order `2^s`, `s ≥ 2`,
`J(χ^{2^{s-1}-1}, χ^{2^{s-1}-1}) = χ(4)^2 * J(χ,χ)`.

Equivalently, writing `σ` for the Galois action `χ ↦ χ^{2^{s-1}-1}` on character values,
`σ` acts on the Jacobi sum by multiplication with `χ(4)^2` — the Jacobi sum is an
eigenvector for this Galois element with eigenvalue `χ(2)^4`.

Proof: write `B = χ^{2^{s-1}-1} = ε·χ̄` (uniqueness of the quadratic character);
then `{B, ε, χ}` is a single `S₃`-orbit, so `J(B,ε) = J(χ,ε)`, and the doubling
formula applied to `B` and to `χ` supplies the two `χ(4)` factors. -/
theorem jacobiSum_pow_pred {s : ℕ} (hs : 2 ≤ s) {χ : MulChar F F'}
    (hχ : orderOf χ = 2 ^ s) :
    jacobiSum (χ ^ (2 ^ (s - 1) - 1)) (χ ^ (2 ^ (s - 1) - 1))
      = χ 4 ^ 2 * jacobiSum χ χ := by
  -- divisibility: orderOf χ = 2^s | q - 1, hence 4 | q - 1
  have hq4 : 4 ∣ Fintype.card F - 1 := by
    have hd : orderOf χ ∣ Fintype.card F - 1 := MulChar.orderOf_dvd_card_sub_one F χ
    rw [hχ] at hd
    exact dvd_trans
      (show (4 : ℕ) ∣ 2 ^ s by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 hs)
      hd
  have hrc : ringChar F ≠ 2 := by
    intro h
    have hcard : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    have hdvd : ringChar F ∣ Fintype.card F :=
      (CharP.cast_eq_zero_iff F (ringChar F) _).mp hcard
    obtain ⟨k, hk⟩ := hq4; obtain ⟨l, hl⟩ := hdvd
    have hq1 : 0 < Fintype.card F := Fintype.card_pos
    rw [h] at hl; omega
  have h2 : (2 : F) ≠ 0 := by
    intro h20
    apply hrc
    have hd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F _ _).mp h20
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left CharP.ringChar_ne_one
  have h4ne : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  -- eps facts: ε² = 1, ε(4) = 1, ε(−1) = 1
  have hεsq : (quadChar F F') ^ 2 = 1 :=
    MulChar.isQuadratic_iff_sq_eq_one.mp ((quadraticChar_isQuadratic F).comp (algebraMap ℤ F'))
  have hεε : (quadChar F F') * quadChar F F' = 1 := by rw [← pow_two]; exact hεsq
  have epsF4 : (quadChar F F') (4 : F) = 1 := by
    rw [MulChar.ringHomComp_apply,
      (quadraticChar_one_iff_isSquare h4ne).mpr ⟨2, by norm_num⟩, map_one]
  have epsFn1 : (quadChar F F') (-1 : F) = 1 := by
    rw [MulChar.ringHomComp_apply,
      (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
        (FiniteField.isSquare_neg_one_iff.mpr (by omega)), map_one]
  -- power bookkeeping: B = χ^{m-1} = ε·χ̄, η = χ^m = ε
  have hm : 0 < 2 ^ (s - 1) := pow_pos (by norm_num) _
  have hm1 : 2 ^ (s - 1) - 1 + 1 = 2 ^ (s - 1) := Nat.sub_add_cancel hm
  set B : MulChar F F' := χ ^ (2 ^ (s - 1) - 1) with hBdef
  set η : MulChar F F' := χ ^ (2 ^ (s - 1)) with hηdef
  have hsqη : η ^ 2 = 1 := by
    have h2m : 2 ^ (s - 1) * 2 = 2 ^ s := by
      conv_rhs => rw [show s = s - 1 + 1 by omega, pow_succ]
    calc η ^ 2 = χ ^ (2 ^ (s - 1) * 2) := by rw [hηdef, ← pow_mul]
      _ = χ ^ (2 ^ s) := by rw [h2m]
      _ = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have hlt : 2 ^ (s - 1) < 2 ^ s :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hη1 : η ≠ 1 := by
    rw [hηdef]
    intro h
    have hdvd : orderOf χ ∣ 2 ^ (s - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hχ] at hdvd
    exact (Nat.not_dvd_of_pos_of_lt hm hlt) hdvd
  have hη : η = quadChar F F' := eq_quadChar_of_sq_eq_one hrc hsqη hη1
  have hB : B = quadChar F F' * χ⁻¹ := by
    rw [hBdef]
    have e : χ ^ (2 ^ (s - 1) - 1) = χ ^ (2 ^ (s - 1)) * χ⁻¹ := by
      have h : χ ^ (2 ^ (s - 1)) = χ ^ (2 ^ (s - 1) - 1) * χ := by
        conv_lhs => rw [← hm1, pow_succ]
      rw [h, mul_inv_cancel_right]
    rw [e, ← hηdef, hη]
  have hB1 : B ≠ 1 := by
    rw [hBdef]
    intro h
    have hdvd : orderOf χ ∣ 2 ^ (s - 1) - 1 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hχ] at hdvd
    have hlt2 : 2 ^ (s - 1) - 1 < 2 ^ s :=
      lt_of_lt_of_le (Nat.sub_one_lt hm.ne')
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hpos : 0 < 2 ^ (s - 1) - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
    exact (Nat.not_dvd_of_pos_of_lt hpos hlt2) hdvd
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hχ
    have : (1 : ℕ) < 2 ^ s := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  -- unit-value facts
  have hχ4 : χ 4 ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr h4ne)
  have hχn1 : χ (-1) ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))
  -- B(4) = χ(4)⁻¹, B(−1) = χ(−1)⁻¹
  have hB4 : (B 4)⁻¹ = χ 4 := by
    have e : B 4 = (χ 4)⁻¹ := by
      rw [hB, MulChar.mul_apply, MulChar.inv_apply_eq_inv', epsF4, one_mul]
    rw [e, inv_inv]
  have hBn1 : B (-1) = (χ (-1))⁻¹ := by
    rw [hB, MulChar.mul_apply, MulChar.inv_apply_eq_inv', epsFn1, one_mul]
  -- pair reductions: (Bε)⁻¹ = χ, (χB)⁻¹ = ε
  have hBc : (B * quadChar F F')⁻¹ = χ := by
    rw [hB]
    have e1 : quadChar F F' * χ⁻¹ * quadChar F F' = χ⁻¹ := by
      calc quadChar F F' * χ⁻¹ * quadChar F F' = χ⁻¹ * (quadChar F F' * quadChar F F') := by ac_rfl
        _ = χ⁻¹ := by rw [hεε, mul_one]
    rw [e1, inv_inv]
  have hχBc : (χ * B)⁻¹ = quadChar F F' := by
    rw [hB]
    have e1 : χ * (quadChar F F' * χ⁻¹) = quadChar F F' := by
      calc χ * (quadChar F F' * χ⁻¹) = quadChar F F' * (χ * χ⁻¹) := by ac_rfl
        _ = quadChar F F' := by rw [mul_inv_cancel, mul_one]
    rw [e1]
    exact inv_eq_of_mul_eq_one_left hεε
  -- doubling on χ: J(χ,ε) = χ(4)·J(χ,χ)
  have step5 : jacobiSum χ (quadChar F F') = χ 4 * jacobiSum χ χ := by
    have hd := jacobiSum_self_eq h2 hχ1
    have key : χ 4 * jacobiSum χ χ = jacobiSum χ (quadChar F F') := by
      rw [hd, ← mul_assoc, mul_inv_cancel₀ hχ4, one_mul]
    exact key.symm
  -- the chain
  calc jacobiSum B B = (B 4)⁻¹ * jacobiSum B (quadChar F F') := jacobiSum_self_eq h2 hB1
    _ = χ 4 * jacobiSum B (quadChar F F') := by rw [hB4]
    _ = χ 4 * (B (-1) * jacobiSum B χ) := by rw [jacobiSum_eq_apply_neg_one_mul_jacobiSum_inv, hBc]
    _ = χ 4 * (B (-1) * jacobiSum χ B) := by rw [jacobiSum_comm]
    _ = χ 4 * (B (-1) * (χ (-1) * jacobiSum χ (quadChar F F'))) := by
        rw [jacobiSum_eq_apply_neg_one_mul_jacobiSum_inv, hχBc]
    _ = χ 4 * jacobiSum χ (quadChar F F') := by
        rw [hBn1, ← mul_assoc ((χ (-1))⁻¹) (χ (-1)),
          inv_mul_cancel₀ hχn1, one_mul]
    _ = χ 4 * (χ 4 * jacobiSum χ χ) := by rw [step5]
    _ = χ 4 ^ 2 * jacobiSum χ χ := by ring

end Tower

/-!
### The twist identity and the descent identity
-/

section Descent

variable {F' : Type*} [Field F']

/-- The *twist identity* for Gauss sums: for `X` nontrivial with `X²` nontrivial,
`τ(ε·X, ψ) = X(4)⁻¹ * τ(ε,ψ) * τ(X²,ψ) / τ(X,ψ)`
(where `ε` is the quadratic character). This is the doubling formula rewritten
via `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`. -/
theorem gaussSum_quadChar_mul (h2 : (2 : F) ≠ 0) (hq : (Fintype.card F : F') ≠ 0)
    {X : MulChar F F'} (hX : X ≠ 1) (hX2 : X ^ 2 ≠ 1) (hεX : quadChar F F' * X ≠ 1)
    {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    gaussSum (quadChar F F' * X) ψ =
      (X 4)⁻¹ * (gaussSum (quadChar F F') ψ * gaussSum (X ^ 2) ψ) / gaussSum X ψ := by
  have hd : jacobiSum X X = (X 4)⁻¹ * jacobiSum X (quadChar F F') :=
    jacobiSum_self_eq h2 hX
  have hXε : X * quadChar F F' ≠ 1 := mul_comm (quadChar F F') X ▸ hεX
  have hXX : X * X ≠ 1 := pow_two X ▸ hX2
  have hτ : ∀ {Y : MulChar F F'}, Y ≠ 1 → gaussSum Y ψ ≠ 0 :=
    fun hY => gaussSum_ne_zero_of_nontrivial hq hY hψ
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hq hXX hψ,
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hq hXε hψ] at hd
  have key : gaussSum (X * quadChar F F') ψ =
      (X 4)⁻¹ * (gaussSum (quadChar F F') ψ * gaussSum (X * X) ψ) / gaussSum X ψ := by
    have hτX : gaussSum X ψ ≠ 0 := hτ hX
    have hτXε : gaussSum (X * quadChar F F') ψ ≠ 0 := hτ hXε
    have hτXX : gaussSum (X * X) ψ ≠ 0 := hτ hXX
    field_simp at hd ⊢
    linear_combination hd
  rw [mul_comm X (quadChar F F'), ← pow_two] at key
  exact key

/-- The *descent identity*: for nontrivial `A`, `B` with `AB`, `A²`, `B²`, `(AB)²`,
`εA`, `εB` all nontrivial,

  `J(εA, εB) * (AB)(4) * J(A, B) * J(AB, AB) = ε(−1) * #F * J(A², B²)`.

Every Jacobi sum expands as `ττ/τ` (`jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`);
the two twists `τ(εX) = X(4)⁻¹·τε·τ(X²)/τX` (`gaussSum_quadChar_mul`) and
`τε² = ε(−1)·q` (`gaussSum_sq`) then close the identity. -/
theorem jacobiSum_descent (h2 : (2 : F) ≠ 0) (hq : (Fintype.card F : F') ≠ 0)
    (hrc' : ringChar F' ≠ 2)
    {A B : MulChar F F'}
    (hA : A ≠ 1) (hB : B ≠ 1) (hAB : A * B ≠ 1)
    (hA2 : A ^ 2 ≠ 1) (hB2 : B ^ 2 ≠ 1) (hAB2 : (A * B) ^ 2 ≠ 1)
    (hεA : quadChar F F' * A ≠ 1) (hεB : quadChar F F' * B ≠ 1)
    {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum (quadChar F F' * A) (quadChar F F' * B) * ((A * B) 4) * jacobiSum A B *
        jacobiSum (A * B) (A * B)
      = quadChar F F' (-1) * Fintype.card F * jacobiSum (A ^ 2) (B ^ 2) := by
  classical
  have h4ne : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hrc : ringChar F ≠ 2 := fun h =>
    h2 (by simpa [h] using CharP.cast_eq_zero F (ringChar F))
  have hε1 : (quadChar F F' : MulChar F F') ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hrc
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    rw [MulChar.ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one]
    exact Ring.neg_one_ne_one_of_char_ne_two hrc'
  have hεq : (quadChar F F' : MulChar F F').IsQuadratic :=
    (quadraticChar_isQuadratic F).comp (algebraMap ℤ F')
  have hεε : (quadChar F F' : MulChar F F') * quadChar F F' = 1 := by
    rw [← pow_two]; exact MulChar.isQuadratic_iff_sq_eq_one.mp hεq
  -- gauss-sum machinery
  have hτ : ∀ {X : MulChar F F'}, X ≠ 1 → gaussSum X ψ ≠ 0 :=
    fun hX => gaussSum_ne_zero_of_nontrivial hq hX hψ
  have jt : ∀ {X Y : MulChar F F'}, X * Y ≠ 1 →
      jacobiSum X Y = gaussSum X ψ * gaussSum Y ψ / gaussSum (X * Y) ψ :=
    fun h => jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hq h hψ
  have ne4 : ∀ {X : MulChar F F'}, X (4 : F) ≠ 0 :=
    fun {_} => MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr h4ne)
  -- the twist lemma: τ(εX) = X(4)⁻¹·τε·τ(X²)/τX
  have twist : ∀ {X : MulChar F F'}, X ≠ 1 → X ^ 2 ≠ 1 → quadChar F F' * X ≠ 1 →
      gaussSum (quadChar F F' * X) ψ =
        (X 4)⁻¹ * (gaussSum (quadChar F F') ψ * gaussSum (X ^ 2) ψ) / gaussSum X ψ :=
    fun hX hX2 hεX => gaussSum_quadChar_mul h2 hq hX hX2 hεX hψ
  -- τε² = ε(−1)·q
  have hgs : gaussSum (quadChar F F') ψ ^ 2 = quadChar F F' (-1) * Fintype.card F :=
    gaussSum_sq hε1 hεq hψ
  -- product bookkeeping
  have hprod : quadChar F F' * A * (quadChar F F' * B) = A * B := by
    rw [mul_assoc, mul_left_comm A (quadChar F F') B, ← mul_assoc, hεε, one_mul]
  -- the LHS expands to τε²·τ(A²)·τ(B²)/τ((AB)²)
  have hL : jacobiSum (quadChar F F' * A) (quadChar F F' * B) * ((A * B) 4) *
        jacobiSum A B * jacobiSum (A * B) (A * B)
      = gaussSum (quadChar F F') ψ ^ 2 * gaussSum (A ^ 2) ψ * gaussSum (B ^ 2) ψ /
        gaussSum ((A * B) ^ 2) ψ := by
    rw [jt (show quadChar F F' * A * (quadChar F F' * B) ≠ 1 by rw [hprod]; exact hAB),
      jt hAB,
      jt (show A * B * (A * B) ≠ 1 from pow_two (A * B) ▸ hAB2)]
    rw [twist hA hA2 hεA, twist hB hB2 hεB, hprod, ← pow_two (A * B),
      show (A * B) (4 : F) = A 4 * B 4 from MulChar.mul_apply _ _ _]
    field_simp [ne4, hτ hA, hτ hB, hτ hAB, hτ hAB2]
  -- substitute hL, τε² = ε(−1)q, and the J-form of J(A²,B²)
  rw [hL, hgs, jt (show A ^ 2 * B ^ 2 ≠ 1 from mul_pow A B 2 ▸ hAB2), ← mul_pow]
  ring

end Descent
