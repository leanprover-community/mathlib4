/-
Copyright (c) 2026 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!

# Polynomials with p-th power coefficients

In this file we prove https://stacks.math.columbia.edu/tag/031V, which gives a criterion for a root
of a polynomial over a field `k` of characteristic `p` to be a `p`-th power.

## Main results
- `zero_of_map_frob_is_pth_power`: let `K/k` be an extension of fields of characteristic `p`, let
  `α ∈ K` and let `P` be a separable polynomial over `k` whose coefficients are `p`-th powers in
  `k`. Then `α` is a `p`-th power in `K`.

-/

@[expose] public section

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {p : ℕ}

-- The minimal polynomial of a non `p`th power in a field of characteristic `p` is `X ^ p - C α`
lemma X_pow_p_sub_C_eq_minpoly_of_non_pth_power {α : k} (hα : ¬∃ β : k, β ^ p = α) {ρ : K}
    (hρ : ρ ^ p = algebraMap k K α) (hp : p.Prime) :
    X ^ p - C α = minpoly k ρ := by
  have hIrred : Irreducible (X ^ p - C α) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    tauto
  apply minpoly.eq_of_irreducible_of_monic hIrred
  · simp [hρ]
  · have hDeg : (X ^ p - C α).natDegree = p := by simp
    simp [Monic.def, leadingCoeff, hDeg,
          Polynomial.coeff_C_ne_zero (Nat.ne_zero_of_lt <| Nat.Prime.pos hp)]

@[stacks 031V "(2)"]
lemma zero_of_map_frob_is_pth_power {α : K} {P : k[X]} (hP : P.aeval α = 0) [CharP k p]
    [ExpChar k p] (hSep : P.Separable) (hp : p.Prime)
    (hQfrob_eq_P : ∃ Q : k[X], P = Polynomial.map (frobenius k p) Q) :
    ∃ β : K, β ^ p = α := by
  by_cases hα : ∃ β : K, β ^ p = α
  · assumption
  · obtain ⟨Q, hQ⟩ := hQfrob_eq_P
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) α)
      (Nat.Prime.pos hp)
    have QX_pow_p_dvd : (X ^ p - C α) ∣ Polynomial.mapAlg k K Q := by
      -- We will prove this by proving that `Q(ρ) = 0` and using that `X ^ p - C α` is the minimal
      -- polynomial of `ρ` over `K`, the result then follows from `minpoly.dvd`
      have hRoot : aeval ρ Q = 0 := by
        have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
        rw [← map_eq_zero (frobenius (AlgebraicClosure K) p), ← Polynomial.eval_map_algebraMap,
            ← Polynomial.eval₂_at_apply, frobenius_def, hρ, Polynomial.eval₂_map,
            ← RingHom.frobenius_comm, ← Polynomial.eval₂_map, ← hQ, ← Polynomial.aeval_def,
            aeval_algebraMap_eq_zero_iff]
        exact hP
      have _ : ExpChar K p := ExpChar.of_injective_algebraMap' k _
      rw [X_pow_p_sub_C_eq_minpoly_of_non_pth_power hα hρ hp]
      apply minpoly.dvd
      rw [← hRoot, mapAlg_eq_map, aeval_map_algebraMap]
    have hQSep : (mapAlg k K Q).Separable :=
      Polynomial.Separable.map ((Polynomial.separable_map _).mp (hQ ▸ hSep))
    apply Polynomial.Separable.of_dvd hQSep at QX_pow_p_dvd
    have hαNonZero : α ≠ 0 := fun hzero => ((hzero ▸ hα)
      (by use 0; exact zero_pow (pos_iff_ne_zero.mp (Nat.Prime.pos hp))))
    have hInsep_iff_p_ne_zero := ((ne_eq _ _) ▸
      (not_iff_not.mpr (X_pow_sub_C_separable_iff (Nat.Prime.pos hp) hαNonZero))).trans not_not
    have hpzero : (p : K) = 0 := by
      rw [← (CharP.charP_iff_prime_eq_zero hp), ← Algebra.charP_iff k K p]
      assumption
    exfalso
    exact hInsep_iff_p_ne_zero.mpr hpzero QX_pow_p_dvd

@[stacks 031V "(1)"]
lemma zero_of_minpoly_map_frob_is_pth_power (hp : p.Prime) [hSep : Algebra.IsSeparable k K] (α : K)
    [ExpChar k p] [CharP k p]
    (h_pth_power_coeff : ∃ Q : k[X], ((minpoly k α)) = Polynomial.map (frobenius k p) Q) :
    ∃ β : K, β ^ p = α :=
  zero_of_map_frob_is_pth_power (minpoly.aeval k α) ((Algebra.isSeparable_def k K).mp hSep α) hp
    h_pth_power_coeff
