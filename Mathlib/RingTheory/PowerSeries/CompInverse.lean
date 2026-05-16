/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Compositional inverse of formal power series

A **delta series** is a formal power series `f ∈ R⟦X⟧` with zero constant term and
unit linear coefficient. Every delta series has a unique **compositional inverse**
`g` satisfying `f(g) = X` and `g(f) = X` under composition (`PowerSeries.subst`).

The construction proceeds by coefficient recursion: coefficient `n` of `g` is
determined by coefficients `0` through `n - 1`, using the fact that `coeff n (g ^ d)`
for `d ≥ 2` depends only on lower coefficients of `g`.

## Main definitions

* `PowerSeries.IsDeltaSeries`: predicate for delta series
* `PowerSeries.compInv`: the compositional inverse

## Main results

* `PowerSeries.subst_compInv`: `f.subst (compInv f hf) = X` (right inverse)
* `PowerSeries.compInv_subst`: `(compInv f hf).subst f = X` (left inverse)
* `PowerSeries.compInv_isDeltaSeries`: the compositional inverse is a delta series

## References

* Roman, S., *The Umbral Calculus*, Academic Press, 1984, Chapter 2
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-! ### Delta series -/

/-- A **delta series** is a formal power series with zero constant term and unit
linear coefficient. These are the series that are invertible under composition. -/
structure IsDeltaSeries (f : R⟦X⟧) : Prop where
  constantCoeff_eq_zero : constantCoeff f = 0
  isUnit_coeff_one : IsUnit (coeff 1 f)

variable {f : R⟦X⟧}

/-- A delta series can be substituted into other power series. -/
theorem IsDeltaSeries.hasSubst (hf : IsDeltaSeries f) : HasSubst f :=
  HasSubst.of_constantCoeff_zero' hf.constantCoeff_eq_zero

/-- Extract the unit from the linear coefficient of a delta series. -/
noncomputable def IsDeltaSeries.linearUnit (hf : IsDeltaSeries f) : Rˣ :=
  hf.isUnit_coeff_one.choose

theorem IsDeltaSeries.val_linearUnit (hf : IsDeltaSeries f) :
    ↑hf.linearUnit = (coeff 1 f : R) := by
  exact hf.isUnit_coeff_one.choose_spec

/-! ### Recursive coefficient construction -/

/-- Coefficient `n` of the compositional inverse, computed by recursion on `n`. -/
noncomputable def compInvCoeff (u_inv : R) (f : R⟦X⟧) : ℕ → R
  | 0 => 0
  | 1 => u_inv
  | (n + 2) =>
    -u_inv * (Finset.Icc 2 (n + 2)).sum (fun d =>
      coeff d f * coeff (n + 2)
        ((mk fun m => if m < n + 2 then compInvCoeff u_inv f m else 0) ^ d))
  termination_by k => k

/-! ### The compositional inverse -/

/-- The **compositional inverse** of a delta series `f`. -/
noncomputable def compInv (f : R⟦X⟧) (hf : IsDeltaSeries f) : R⟦X⟧ :=
  mk (compInvCoeff (↑hf.linearUnit⁻¹) f)

/-! ### Agreement lemma -/

/-- For `d ≥ 1` and power series with zero constant term that agree below `n`,
their `d`-th powers also agree below `n`. -/
theorem coeff_pow_eq_of_agree_lt {n : ℕ} {g₁ g₂ : R⟦X⟧}
    (hg₁ : constantCoeff g₁ = 0)
    (hg₂ : constantCoeff g₂ = 0)
    (h : ∀ m, m < n → coeff m g₁ = coeff m g₂)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ m, m < n → coeff m (g₁ ^ d) = coeff m (g₂ ^ d) := by
  induction d with
  | zero => omega
  | succ d ih =>
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
        map_pow, map_pow, hg₁, hg₂]
    · rw [pow_succ' g₁ d, pow_succ' g₂ d, coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_antidiagonal] at hp
      by_cases hp1 : p.1 = 0
      · simp only [hp1, coeff_zero_eq_constantCoeff_apply, hg₁, hg₂, zero_mul]
      · by_cases hp2 : p.2 = 0
        · by_cases hd' : d = 0
          · subst hd'
            have hp1_eq : p.1 = m := by omega
            simp only [pow_zero, hp2, hp1_eq,
              coeff_zero_eq_constantCoeff_apply, map_one, mul_one, h m hm]
          · simp only [hp2, coeff_zero_eq_constantCoeff_apply, map_pow, hg₁, hg₂,
              zero_pow hd', mul_zero]
        · congr 1
          · exact h p.1 (by omega)
          · by_cases hd' : 1 ≤ d
            · exact ih hd' p.2 (by omega)
            · have hd0 : d = 0 := by omega
              subst hd0; simp

/-- For `d ≥ 2` and power series with zero constant term, `coeff n (g ^ d)` depends
only on coefficients of `g` at indices strictly below `n`. -/
theorem coeff_pow_eq_of_agree {g₁ g₂ : R⟦X⟧} {n : ℕ}
    (hg₁ : constantCoeff g₁ = 0)
    (hg₂ : constantCoeff g₂ = 0)
    (h : ∀ m, m < n → coeff m g₁ = coeff m g₂)
    {d : ℕ} (hd : 2 ≤ d) :
    coeff n (g₁ ^ d) = coeff n (g₂ ^ d) := by
  by_cases hn : n = 0
  · subst hn
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      map_pow, map_pow, hg₁, hg₂]
  · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
    change coeff n (g₁ ^ ((d + 1) + 1)) = coeff n (g₂ ^ ((d + 1) + 1))
    rw [pow_succ' g₁ (d + 1), pow_succ' g₂ (d + 1), coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_antidiagonal] at hp
    by_cases hp1 : p.1 = 0
    · simp only [hp1, coeff_zero_eq_constantCoeff_apply, hg₁, hg₂, zero_mul]
    · by_cases hp2 : p.2 = 0
      · simp only [hp2, coeff_zero_eq_constantCoeff_apply, map_pow, hg₁, hg₂,
          zero_pow (by omega : d + 1 ≠ 0), mul_zero]
      · rw [h p.1 (by omega),
          coeff_pow_eq_of_agree_lt hg₁ hg₂ h (by omega : 1 ≤ d + 1) p.2 (by omega)]

/-! ### Right and left inverse -/

/-- Substituting the compositional inverse into a delta series yields `X`.

The proof proceeds coefficient by coefficient:
- n = 0: both sides have zero constant term
- n = 1: the d = 1 substitution term gives `(coeff 1 f) * u⁻¹ = 1`
- n ≥ 2: the recursive construction of `compInvCoeff` ensures exact cancellation -/
theorem subst_compInv (hf : IsDeltaSeries f) :
    f.subst (compInv f hf) = X := by
  set g := compInv f hf with hg_def
  have hg0 : constantCoeff g = 0 := by
    simp only [hg_def, compInv, ← coeff_zero_eq_constantCoeff, coeff_mk, compInvCoeff]
  have hg_sub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hf0 : constantCoeff f = 0 := hf.constantCoeff_eq_zero
  apply ext; intro n
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
    have : constantCoeff (X : R⟦X⟧) = 0 := by simp
    rw [this]
    exact constantCoeff_subst_eq_zero hg0 f hf0
  | succ n =>
    rw [coeff_subst' hg_sub]
    cases n with
    | zero =>
      -- n+1 = 1: only the d=1 term survives
      rw [coeff_one_X, finsum_eq_single _ 1]
      · simp only [pow_one, smul_eq_mul]
        rw [hg_def, compInv, coeff_mk]
        have hunfold : compInvCoeff (↑hf.linearUnit⁻¹) f 1 = ↑hf.linearUnit⁻¹ := by
          unfold compInvCoeff; rfl
        rw [hunfold, ← hf.val_linearUnit]; exact hf.linearUnit.val_inv
      · intro d hd
        by_cases hd0 : d = 0
        · subst hd0; simp [coeff_zero_eq_constantCoeff_apply, hf0]
        · have hd2 : 2 ≤ d := by omega
          simp only [smul_eq_mul]
          apply mul_eq_zero_of_right
          rw [coeff_pow_eq_of_agree hg0 (map_zero _)
            (fun k hk => by
              have : k = 0 := by omega
              subst this
              rw [coeff_zero_eq_constantCoeff_apply, hg0, map_zero]) hd2]
          simp [zero_pow (by omega : d ≠ 0)]
    | succ n =>
      simp only [show n + 1 + 1 = n + 2 from by ring]
      have : coeff (n + 2) (X : R⟦X⟧) = 0 := by simp [coeff_X, show n + 2 ≠ 1 from by omega]
      rw [this]
      set u_inv := (↑hf.linearUnit⁻¹ : R) with hu_inv_def
      set u := (↑hf.linearUnit : R) with hu_def
      have hu_val : coeff 1 f = u := hf.val_linearUnit.symm
      have hu_inv : u * u_inv = 1 := by
        rw [hu_def, hu_inv_def]; exact hf.linearUnit.val_inv
      have gPartial_def : ∀ d, 2 ≤ d → d ≤ n + 2 →
          coeff (n + 2) (g ^ d) =
          coeff (n + 2) ((mk fun m =>
            if m < n + 2 then compInvCoeff u_inv f m else 0) ^ d) := by
        intro d hd _
        apply coeff_pow_eq_of_agree hg0
        · rw [← coeff_zero_eq_constantCoeff]; simp [coeff_mk, compInvCoeff]
        · intro m hm; simp only [hg_def, compInv, coeff_mk]; rw [if_pos hm]
        · exact hd
      have hb : compInvCoeff u_inv f (n + 2) =
          -u_inv * (Finset.Icc 2 (n + 2)).sum (fun d =>
            coeff d f * coeff (n + 2)
              ((mk fun m => if m < n + 2 then compInvCoeff u_inv f m else 0) ^ d)) := by
        conv_lhs => rw [compInvCoeff]
      have vanish : ∀ d, n + 2 < d → coeff (n + 2) (g ^ d) = 0 := by
        intro d hd
        apply coeff_of_lt_order
        exact lt_of_lt_of_le (by exact_mod_cast hd)
          (le_order_pow_of_constantCoeff_eq_zero d hg0)
      have support_sub : Function.support
          (fun d => coeff d f • coeff (n + 2) (g ^ d)) ⊆
          ↑(Finset.range (n + 3)) := by
        intro d hd
        simp only [Function.mem_support, smul_eq_mul, ne_eq] at hd
        simp only [Finset.mem_coe, Finset.mem_range]
        by_contra hle
        push Not at hle
        exact hd (by rw [vanish d (by omega), mul_zero])
      rw [finsum_eq_sum_of_support_subset _ support_sub]
      have hrange : Finset.range (n + 3) =
          ({0} : Finset ℕ) ∪ ({1} ∪ Finset.Icc 2 (n + 2)) := by
        ext d; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_Icc]; omega
      have hdisj1 : Disjoint ({0} : Finset ℕ) ({1} ∪ Finset.Icc 2 (n + 2)) := by
        rw [Finset.disjoint_left]; intro d hd
        simp only [Finset.mem_singleton] at hd; subst hd
        simp [Finset.mem_Icc]
      have hdisj2 : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (n + 2)) := by
        rw [Finset.disjoint_left]; intro d hd
        simp only [Finset.mem_singleton] at hd; subst hd
        simp [Finset.mem_Icc]
      rw [hrange, Finset.sum_union hdisj1, Finset.sum_union hdisj2,
        Finset.sum_singleton, Finset.sum_singleton]
      simp only [smul_eq_mul, pow_zero, coeff_zero_eq_constantCoeff_apply, hf0,
        zero_mul, zero_add, pow_one, hu_val]
      set S := (Finset.Icc 2 (n + 2)).sum fun d =>
        coeff d f * coeff (n + 2) (g ^ d)
      have hg_coeff : coeff (n + 2) g = compInvCoeff u_inv f (n + 2) := by
        simp only [hg_def, compInv, coeff_mk]; rfl
      have hb' : compInvCoeff u_inv f (n + 2) = -u_inv * S := by
        rw [hb]; congr 1
        apply Finset.sum_congr rfl
        intro d hd
        simp only [Finset.mem_Icc] at hd
        congr 1; exact (gPartial_def d hd.1 hd.2).symm
      rw [hg_coeff, hb']
      calc u * (-u_inv * S) + S
          = -(u * u_inv) * S + S := by ring
        _ = -1 * S + S := by rw [hu_inv]
        _ = 0 := by ring

/-- The compositional inverse of a delta series is itself a delta series. -/
theorem compInv_isDeltaSeries (hf : IsDeltaSeries f) :
    IsDeltaSeries (compInv f hf) where
  constantCoeff_eq_zero := by
    simp only [compInv, ← coeff_zero_eq_constantCoeff, coeff_mk, compInvCoeff]
  isUnit_coeff_one := by
    simp only [compInv, coeff_mk, compInvCoeff]
    exact hf.linearUnit⁻¹ |>.isUnit

/-- The left compositional inverse: composing in the other order also yields `X`. -/
theorem compInv_subst (hf : IsDeltaSeries f) :
    (compInv f hf).subst f = X := by
  set g := compInv f hf
  have hg_delta := compInv_isDeltaSeries hf
  set h := compInv g hg_delta
  have hgX : g.subst h = X := subst_compInv hg_delta
  have hfX : f.subst g = X := subst_compInv hf
  have hg_sub : HasSubst g :=
    HasSubst.of_constantCoeff_zero' hg_delta.constantCoeff_eq_zero
  have hh_sub : HasSubst h :=
    HasSubst.of_constantCoeff_zero' (compInv_isDeltaSeries hg_delta).constantCoeff_eq_zero
  have subst_X_id : ∀ (p : R⟦X⟧), subst (X : R⟦X⟧) p = p := by
    intro p
    rw [subst_def]
    have : (fun (_ : Unit) => (X : R⟦X⟧)) = MvPowerSeries.X := by
      ext ⟨⟩; rfl
    rw [this]; exact congr_fun MvPowerSeries.subst_self p
  have h_eq_f : h = f := by
    have := subst_comp_subst_apply hg_sub hh_sub f
    rw [hfX, subst_X hh_sub] at this
    rw [hgX, subst_X_id] at this
    exact this
  rw [← h_eq_f]; exact hgX

end PowerSeries

end -- noncomputable section
end -- public section
