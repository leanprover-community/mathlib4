
module

public import Mathlib

open Polynomial

-- alternative name: X_pow_p_sub_C_eq_minpoly_of_non_pth_power
-- The minimal polynomial of a non `p`th power in a field of characteristic `p` is `X ^ p - C α`
lemma non_pth_power_elem_minpoly {k K : Type*} [Field k] [Field K] [Algebra k K] {p : ℕ} {α : k}
    (hp : p.Prime) [ExpChar k p] (hα : ¬∃ β : k, β ^ p = α) {ρ : K}
    (hρ : ρ ^ p = algebraMap k K α) :
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
-- root_of_map_frob_is_pth_power
lemma pth_power_poly_imp_pth_power {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] {α : K} {P : Polynomial k}
    (hP : P.aeval α = 0) {p : ℕ} (hp : p.Prime) [CharP k p] [ExpChar k p]
    (hQfrob_eq_P : ∃ Q : Polynomial k, P = Polynomial.map (frobenius k p) Q)
    (hSep : P.Separable) :
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
      rw [non_pth_power_elem_minpoly hp hα hρ]
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
lemma pth_power_poly_imp_pth_power' {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [hSep : Algebra.IsSeparable k K] (α : K) {p : ℕ} (hp : p.Prime)
    [ExpChar k p] [CharP k p]
    (h_pth_power_coeff : ∃ Q : Polynomial k, ((minpoly k α)) = Polynomial.map (frobenius k p) Q) :
    ∃ β : K, β ^ p = α :=
  pth_power_poly_imp_pth_power (minpoly.aeval k α) hp h_pth_power_coeff
    ((Algebra.isSeparable_def k K).mp hSep α)
