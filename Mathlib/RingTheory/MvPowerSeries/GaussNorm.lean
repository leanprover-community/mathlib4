/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Gauss norm for multivariate power series

This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.

## Main definitions and results

* `MvPowerSeries.gaussNormC` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.

* `MvPowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `MvPowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `MvPowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarily for `g`), then
  the Gauss norm has the non-archimedean property.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ) (f : MvPowerSeries σ R)

section Semiring

variable [Semiring R]

/-- Given a multivariate power series `f` in, a function `v : R → ℝ` and a tuple `c` of real
  numbers, the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`. -/
noncomputable def gaussNorm : ℝ :=
   ⨆ t : σ →₀ ℕ, v (coeff t f) * t.prod (c · ^ ·)

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * ∏ i : t.support, c i` is bounded above,
  that is `gaussNormC f` is finite. -/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : σ →₀ ℕ) ↦ (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 := by simp [gaussNorm, vZero]

lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : σ →₀ ℕ) :
    v (coeff t f) * t.prod (c · ^ ·) ≤ gaussNorm v c f := by
  apply le_ciSup hbd

lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f := by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert (le_gaussNorm v c f h 0)
      simp
  · simp [h]

lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i ∈ n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a ↦ (fun i ↦ pow_pos (hc i) (n i)) i)
    specialize h_eq_zero (f.coeff n)
    grind
  _ ≤ _ := le_gaussNorm v c f hbd n

lemma gaussNorm_add_le_max (f g : MvPowerSeries σ R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
  have H (t : σ →₀ ℕ) : 0 ≤ ∏ i ∈ t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi ↦ pow_nonneg (hc i) (t i))
  have Final (t : σ →₀ ℕ) : v ((coeff t) (f + g)) * ∏ i ∈ t.support, c ↑i ^ t ↑i ≤
      max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
    specialize hv (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.iSup_le ?_ ?_
  · refine fun t ↦ calc
    _ ≤ _ := Final t
    _ ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i) with h | h
      · left
        simpa [h] using le_gaussNorm v c f hbfd t
      · right
        simpa [h] using le_gaussNorm v c g hbgd t
  · simp only [le_sup_iff]
    left
    exact gaussNorm_nonneg v c f vNonneg

private lemma foo (hc : 0 ≤ c) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))

-- The following three are adapted lemmas from Analysis/Normed/Group/Ultra - we
-- reduce NormedGroup with IsUltraMetric dist to a function with vUltra hypothesis

-- this is a weakening of `Finset.Nonempty.norm_sum_le_sup'_norm`
lemma Finset.Nonempty.map_sum_le_sup'_map {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → R)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) :
    v (∑ i ∈ s, f i) ≤ s.sup' hs fun x ↦ v (f x) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total (v (∑ i ∈ s, f i)) (v (f j))).imp ?_ ?_ <;> intro h
      · exact (vUltra _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (vUltra _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

-- this is a weakening of `exists_norm_finset_prod_le_of_nonempty`
lemma exists_map_finset_prod_le_of_nonempty {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (f : ι → R)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) : ∃ i ∈ t, v (∑ j ∈ t, f j) ≤ v (f i) := by
  simpa [Finset.le_sup'_iff] using Finset.Nonempty.map_sum_le_sup'_map v ht f vUltra

-- this is a weakening of `exists_norm_multiset_prod_le`
lemma exists_map_multiset_prod_le {ι : Type*} (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) (t : Finset ι) [Nonempty ι]
    (f : ι → R) : ∃ i, (t.Nonempty → i ∈ t) ∧ v (∑ j ∈ t, f j) ≤ v (f i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [vZero, vNonneg]
  · exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <|
      exists_map_finset_prod_le_of_nonempty v ht f vUltra

lemma gaussNorm_mul_le (f g : MvPowerSeries σ R) (hc : 0 ≤ c) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g := by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    change (v (coeff t (f * g)) * t.prod fun x1 x2 ↦ c x1 ^ x2) ≤
      (⨆ t, v (coeff t f) * t.prod fun x1 x2 ↦ c x1 ^ x2) *
      ⨆ t, v (coeff t g) * t.prod fun x1 x2 ↦ c x1 ^ x2
    obtain ⟨k, hk, hsum⟩ := exists_map_multiset_prod_le v vZero vNonneg vUltra
      (Finset.antidiagonal t) (fun a ↦ coeff a.1 f * coeff a.2 g)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk
        (Finset.nonempty_def.mpr ⟨(t, 0), by simp⟩)
    have hprod : t.prod (c · ^ ·) = k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·) := by
      simp only [← hk', pow_zero, implies_true, pow_add, Finsupp.prod_add_index']
    simp_rw [hprod]
    refine (mul_le_mul hsum (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2)) (vNonneg _)).trans
      ?_
    have : v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) ≤
        (v (coeff k.1 f) * k.1.prod (c · ^ ·)) * (v (coeff k.2 g) * k.2.prod (c · ^ ·)) := by
      calc
      _ ≤ v (coeff k.1 f) * v (coeff k.2 g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
        mul_le_mul (vMul _ _) (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2))
          (mul_nonneg (vNonneg _) (vNonneg _))
      _ = _ := by ring
    exact this.trans (mul_le_mul (le_gaussNorm v c f hbfd k.1) (le_gaussNorm v c g hbgd k.2)
      (mul_nonneg (vNonneg _) (foo c hc k.2)) (gaussNorm_nonneg v c f vNonneg))
  · exact mul_nonneg (gaussNorm_nonneg v c f vNonneg) (gaussNorm_nonneg v c g vNonneg)

end Semiring

variable [Ring R]

/-- Predicate for when the gaussNorm is achieved by an index. -/
def AchievesGaussNorm (i : σ →₀ ℕ) : Prop :=
  v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f
section absoluteValue

lemma ultrametric_strict (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) {a b : R}
    (hne : v a ≠ v b) : v (a + b) = max (v a) (v b) := by
  wlog hab : v a > v b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (vUltra a b)
  rcases le_max_iff.mp (vUltra (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [vNeg b] using hab))

-- this is a version of Fabrizio's apply_sum_eq_of_lt (in Algebra/Order/Ring/IsNonarchimedean)
-- but in our generality of function v + hypothesis
lemma antidiagonal_dominant [DecidableEq σ] (f g : MvPowerSeries σ R) (i j : σ →₀ ℕ)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vNeg : ∀ a, v a = v (-a))
    (hdom : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    v (coeff (i + j) (f * g))  = v (coeff i f * coeff j g) := by
  rw [coeff_mul]
  have hmem : (i, j) ∈ Finset.antidiagonal (i + j) := by simp [Finset.mem_antidiagonal]
  by_cases hcard : (Finset.antidiagonal (i + j)).card = 1
  · have h : Finset.antidiagonal (i + j) = {(i, j)} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      grind
    simp only [h, Finset.sum_singleton]
  · rw [← Finset.add_sum_erase _ _ hmem]
    have hNonempty : ((Finset.antidiagonal (i + j)).erase (i, j)).Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or] using
        ⟨Finset.ne_empty_of_mem hmem, fun h => by simp [h] at hcard⟩
    obtain ⟨m, hm, hvm⟩ := Finset.exists_max_image _ (fun p => v (coeff p.1 f * coeff p.2 g))
      hNonempty
    have hrest_le := (Finset.Nonempty.map_sum_le_sup'_map v hNonempty
      (fun p => coeff p.1 f * coeff p.2 g) vUltra).trans
      (Finset.sup'_le hNonempty _ (fun x hx => hvm x hx))
    rw [ultrametric_strict v vUltra vNeg (by grind), max_eq_left (le_of_lt (by grind))]

lemma gaussNorm_le_mul [DecidableEq σ] (f g : MvPowerSeries σ R)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) := by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _  = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀, ← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          have hprod : (i₀ + j₀).prod (c · ^ ·) = i₀.prod (c · ^ ·) * j₀.prod (c · ^ ·) := by
            simp [Finsupp.prod_add_index', pow_add]
          rw [hprod]; ring
    _ = v (coeff i₀ f * coeff j₀ g) * (i₀ + j₀).prod (c · ^ ·) := by rw [vMulEq]
    _ = v (coeff (i₀ + j₀) (f * g)) * (i₀ + j₀).prod (c · ^ ·) := by
      rw [antidiagonal_dominant v f g i₀ j₀ vUltra vMulEq vNeg hdom']
    _ ≤ gaussNorm v c (f * g) := le_gaussNorm v c (f * g) hbfg (i₀ + j₀)

end absoluteValue

end MvPowerSeries
