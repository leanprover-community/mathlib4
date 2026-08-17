import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Multiset

variable {R : Type*}

theorem esymm_cons [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [esymm, sum_map_mul_left]

@[simp]
theorem esymm_zero [CommSemiring R] (s : Multiset R) : s.esymm 0 = 1 := by
  simp [esymm]

@[simp]
theorem esymm_one [CommSemiring R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [esymm, powersetCard_one]

theorem two_mul_esymm_two [CommRing R] (s : Multiset R) : 2 * s.esymm 2 =
  s.sum ^ 2 - (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction with
  | empty => simp [esymm, powersetCard_zero_right]
  | cons a t ih => grind [sum_cons, map_cons, esymm_cons, esymm_one]

@[simp]
theorem esymm_card [CommSemiring R] (s : Multiset R) : s.esymm s.card = s.prod := by
  simp [esymm, powersetCard_self]

theorem esymm_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {s : Multiset R}
  (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ s.esymm k := by
  grind [esymm, sum_nonneg, mem_map, prod_nonneg, mem_of_le, mem_powersetCard]

private theorem esymm_map_inv_aux [Field R] (s : Multiset R) : 0 ∉ s → ∀ j k, s.card = j + k →
    (s.map (·⁻¹)).esymm k * s.prod = s.esymm j := by
  induction s using Multiset.induction with
  | empty => grind [map_zero, esymm_zero, card_zero]
  | cons a t _ =>
    intro _ j k _
    obtain _ | k := k
    · grind [esymm_zero, esymm_card, prod_cons]
    obtain _ | j := j
    · grind [esymm_zero, map_cons, card_cons, card_map, esymm_card, prod_map_inv', prod_cons,
        prod_ne_zero]
    · grind [map_cons, esymm_cons, prod_cons, card_cons]

theorem esymm_map_inv [Field R] {s : Multiset R} (h0 : 0 ∉ s) {n k : ℕ} (hs : s.card = n)
    (hk : k ≤ n) : (s.map (·⁻¹)).esymm k * s.esymm n = s.esymm (n - k) := by
  grind [esymm_map_inv_aux, esymm_card]


open Polynomial Real

variable {s : Multiset ℝ} {n k : ℕ}

/-- A special case of the Cauchy--Schwarz inequality. -/
theorem sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 ≤ (s.card : ℝ) * (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t _ =>
    simp only [sum_cons, card_cons, map_cons, Nat.cast_add, Nat.cast_one]
    rcases eq_or_ne (t.card : ℝ) 0 with _ | _
    · simp_all
    · nlinarith [sq_nonneg (t.card * a - t.sum), (by grind [Nat.cast_nonneg] : (0 : ℝ) < t.card)]

private theorem newton_zero (hs : s.card = n) :
    2 * (n : ℝ) ^ 2 * s.esymm 2 ≤ (n : ℝ) * ((n : ℝ) - 1) * (s.esymm 1) ^ 2 := by
  subst hs
  have := sq_sum_le_card_mul_sum_sq s
  rw [esymm_one]
  nlinarith [two_mul_esymm_two s, mul_nonneg (s.card.cast_nonneg (α := ℝ)) (sub_nonneg.mpr this)]

private theorem exists_esymm_derivative (hs : s.card = n + 1) :
    ∃ t : Multiset ℝ, t.card = n ∧
      ∀ k ≤ n, (n + 1) * t.esymm k = (n + 1 - k) * s.esymm k := by
  set f : ℝ[X] := (s.map (X + C ·)).prod with hf
  set g : ℝ[X] := C ((n : ℝ) + 1)⁻¹ * f.derivative
  set t := g.roots.map (- ·)
  have : f.natDegree = n + 1 := by
    rw [hf, natDegree_multiset_prod_of_monic]
    · simp [hs, add_comm]
    · grind [mem_map, monic_X_add_C]
  have : f.derivative.coeff n = (n : ℝ) + 1 := by
    grind [coeff_derivative, Monic.coeff_natDegree, monic_multiset_prod_of_monic, monic_X_add_C]
  have : f.derivative.natDegree ≤ n := by grind [natDegree_derivative_le]
  have : f.derivative.natDegree ≥ n := le_natDegree_of_ne_zero (by grind)
  have : g.natDegree = n := by grind [natDegree_C_mul]
  have : g.Splits := by grind [splits_iff_card_roots, roots_C_mul, card_roots_le_derivative,
    f.derivative.card_roots', Splits.multisetProd, mem_map, Splits.X_add_C]
  have : g = (t.map (X + C ·)).prod := by
    grind [prod_multiset_X_sub_C_of_monic_of_roots_card_eq, splits_iff_card_roots, map_map,
      Monic, leadingCoeff]
  have : t.card = n := by grind [card_map, splits_iff_card_roots]
  refine ⟨t, this, fun k hk ↦ ?_⟩
  have : ((n - k + 1 : ℕ) : ℝ) = n + 1 - k := by simp [Nat.cast_sub hk]; grind
  have : g.coeff (n - k) = t.esymm k := by grind [prod_X_add_C_coeff]
  grind [coeff_derivative, prod_X_add_C_coeff]

private theorem exists_esymm_div_choose (hs : s.card = n + 1) : ∃ t : Multiset ℝ, t.card = n ∧
    ∀ k ≤ n, t.esymm k / (n.choose k) = s.esymm k / ((n + 1).choose k) := by
  obtain ⟨t, htc, ht⟩ := exists_esymm_derivative hs
  refine ⟨t, htc, fun k hk ↦ ?_⟩
  have : ((n + 1 - k : ℕ) : ℝ) = n + 1 - k := by rw [Nat.cast_sub (by omega)]; grind
  have : (n.choose k : ℝ) * (n + 1) = ((n + 1).choose k : ℝ) * (n + 1 - k : ℕ) :=
    mod_cast n.choose_mul_succ_eq k
  rw [div_eq_div_iff]
  · apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    grind
  · exact_mod_cast (Nat.choose_pos hk).ne'
  · exact_mod_cast (Nat.choose_pos (by omega)).ne'

/-- The normalized elementary symmetric functions: `s.nesymm k = s.esymm k / (s.card.choose k)`. -/
noncomputable def nesymm (s : Multiset ℝ) (k : ℕ) : ℝ := s.esymm k / (s.card.choose k)

private theorem newton_aux (n : ℕ) : ∀ s : Multiset ℝ, s.card = n → ∀ k, k + 2 ≤ n →
    s.nesymm k * s.nesymm (k + 2) ≤ (s.nesymm (k + 1)) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k hk
    rcases eq_or_lt_of_le hk with rfl | _
    · by_cases h0 : 0 ∈ s
      · nth_rewrite 2 [nesymm]
        rw [← hs, esymm_card, prod_eq_zero h0]
        grind [sq_nonneg]
      · have : 2 * (k + 2) * (s.esymm k * s.esymm (k + 2)) ≤ (k + 1) * (s.esymm (k + 1)) ^ 2 := by
          rw [(by rfl : k + 1 = k + 2 - 1), ← esymm_map_inv h0 hs (by omega),
            (by rfl : s.esymm k = s.esymm (k + 2 - 2)), ← esymm_map_inv h0 hs (by omega)]
          have := newton_zero (s := s.map (·⁻¹)) (n := k + 2) (by grind [card_map])
          push_cast at this ⊢
          nlinarith [sq_nonneg (s.esymm (k + 2))]
        have : ((k + 2).choose k : ℝ) * 2 = (k + 2) * (k + 1) := by
          norm_cast
          rw [← (k + 2).choose_symm (k := k) (by omega), (by omega : k + 2 - k = 2)]
          rcases k.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> grind [Nat.choose_two_right]
        have : ((k + 2).choose (k + 1) : ℝ) = k + 2 := by
          rw [(by rfl : k + 1 = k + 2 - 1), (k + 2).choose_symm (k := 1) (by omega)]
          simp
        unfold nesymm
        field_simp
        rw [hs, this, div_le_div_iff₀ (mod_cast (by grind [Nat.choose_pos])) (by positivity)]
        simp
        nlinarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      grind [nesymm, exists_esymm_div_choose hs]

/-- **Newton's inequality** : the normalized elementary symmetric functions are log-concave. -/
theorem nesymm_mul_nesymm_le_sq_nesymm (hs : s.card = n) (hk : k + 2 ≤ n) :
    s.nesymm k * s.nesymm (k + 2) ≤ (s.nesymm (k + 1)) ^ 2 := newton_aux n s hs k hk

/-- **Newton's inequality** : unnormalized form. -/
theorem esymm_mul_esymm_le_sq_esymm (hs : s.card = n) (hk : k + 2 ≤ n) :
    (n.choose (k + 1)) ^ 2 * (s.esymm k * s.esymm (k + 2))
      ≤ (n.choose k) * (n.choose (k + 2)) * (s.esymm (k + 1)) ^ 2 := by
  have : (0 : ℝ) < n.choose k := mod_cast Nat.choose_pos (by omega)
  have : (0 : ℝ) < n.choose (k + 1) := mod_cast Nat.choose_pos (by omega)
  have : (0 : ℝ) < n.choose (k + 2) := mod_cast Nat.choose_pos hk
  have h := nesymm_mul_nesymm_le_sq_nesymm hs hk
  simp only [nesymm, hs] at h
  field_simp at h
  nlinarith

/-- **Newton's inequality**: reduced form. -/
theorem esymm_mul_esymm_le_sq_esymm' (hs : s.card = n) (hk : k + 2 ≤ n) :
    ((k : ℝ) + 2) * ((n : ℝ) - k) * (s.esymm k * s.esymm (k + 2))
      ≤ ((k : ℝ) + 1) * ((n : ℝ) - k - 1) * (s.esymm (k + 1)) ^ 2 := by
  have : (0 : ℝ) < (n.choose (k + 1))^2 := sq_pos_of_pos (mod_cast Nat.choose_pos (by omega))
  have : (0 : ℝ) ≤ (k + 2) * (n - k) := by
    apply mul_nonneg (by positivity); rw [sub_nonneg]; exact_mod_cast (by omega)
  have : (k + 2) * (n - k) * ((n.choose k : ℝ) * (n.choose (k + 2)))
      = (k + 1) * (n - k - 1) * (n.choose (k + 1)) ^ 2 := by
    rw [show (n : ℝ) - k - 1 = (n - (k + 1) : ℕ) by rw [Nat.cast_sub (by omega)]; grind,
      ← Nat.cast_sub (by omega)]
    norm_cast
    grind [Nat.choose_succ_right_eq]
  nlinarith [esymm_mul_esymm_le_sq_esymm hs hk]

private theorem esymm_succ_eq_zero_of_esymm_eq_zero
    (hs : ∀ x ∈ s, 0 ≤ x) (h : s.esymm k = 0) : s.esymm (k + 1) = 0 := by
  rw [esymm]
  refine sum_eq_zero fun y hy ↦ ?_
  simp only [mem_map, mem_powersetCard] at hy
  obtain ⟨w, ⟨hws, hwc⟩, rfl⟩ := hy
  obtain ⟨z, hzw⟩ := card_pos_iff_exists_mem.mp (by omega : 0 < w.card)
  obtain ⟨w', rfl⟩ := exists_cons_of_mem hzw
  have : w' ∈ s.powersetCard k := (mem_powersetCard.mpr ⟨(le_cons_self w' z).trans hws,
    by simpa using hwc⟩)
  have {t : Multiset ℝ} (ht : t ∈ s.powersetCard k) : 0 ≤ t.prod :=
    prod_nonneg fun z hz ↦ hs z (mem_of_le (mem_powersetCard.mp ht).1 hz)
  grind [prod_cons, le_antisymm, single_le_sum, mem_map, mem_map_of_mem, esymm]

private theorem hp_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (j : ℕ) : 0 ≤ nesymm s j :=
  div_nonneg (esymm_nonneg hs j) (by positivity)

/-- **Maclaurin's inequality.** `(s.nesymm (k + 1)) ^ k ≤ (s.nesymm k) ^ (k + 1)`. -/
theorem pow_esymm_le (hs : ∀ x ∈ s, 0 ≤ x)
    (hcard : s.card = n) : k + 1 ≤ n → (s.nesymm (k + 1)) ^ k ≤ (s.nesymm k) ^ (k + 1) := by
  induction k with
  | zero => simp [nesymm]
  | succ k ih =>
    intro hk
    by_cases hp1 : s.nesymm (k + 1) = 0
    · have : s.nesymm (k + 2) = 0 := by
        rw [nesymm, esymm_succ_eq_zero_of_esymm_eq_zero hs, zero_div]
        rw [nesymm, div_eq_zero_iff, hcard] at hp1
        exact hp1.resolve_right (mod_cast (Nat.choose_pos (by omega)).ne')
      grind
    · have : 0 < (s.nesymm (k + 1)) ^ k := by grind [hp_nonneg, pow_pos]
      have : (s.nesymm (k + 2)) ^ (k + 1) * (s.nesymm (k + 1)) ^ k
          ≤ (s.nesymm (k + 1)) ^ (k + 2) * (s.nesymm (k + 1)) ^ k := by
        calc
          _ ≤ _ := mul_le_mul_of_nonneg_left (ih (by omega)) (pow_nonneg (hp_nonneg hs _) _)
          _ = (s.nesymm k * s.nesymm (k + 2)) ^ (k + 1) := by rw [mul_pow, mul_comm]
          _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (hp_nonneg hs _) (hp_nonneg hs _))
            (nesymm_mul_nesymm_le_sq_nesymm hcard (by omega : k + 2 ≤ n)) _
          _ = _ := by rw [← pow_mul, ← pow_add]; grind
      nlinarith

/-- **Maclaurin's inequality.** The normalized means `(s.nesymm k)^(k⁻¹)` are antitone. -/
theorem rpow_esymm_antitone (hs : ∀ x ∈ s, 0 ≤ x) (hk1 : 1 ≤ k) (hcard : s.card = n)
    (hk : k + 1 ≤ n) : (s.nesymm (k + 1)) ^ ((k + 1 : ℝ)⁻¹) ≤ (s.nesymm k) ^ ((k : ℝ)⁻¹) := by
  have : 0 ≤ s.nesymm (k + 1) := hp_nonneg hs _
  calc
    _ = ((s.nesymm (k + 1)) ^ k) ^ (((k : ℝ) * (k + 1))⁻¹) := by
      rw [← rpow_natCast (s.nesymm _) k, ← rpow_mul (by positivity)]
      congr 1; field_simp
    _ ≤ _ :=
      rpow_le_rpow (pow_nonneg this k) (pow_esymm_le hs hcard hk) (by positivity)
    _ = _ := by
      rw [← rpow_natCast (s.nesymm k) _, ← rpow_mul (hp_nonneg hs _)]
      congr 1; grind


end Multiset
