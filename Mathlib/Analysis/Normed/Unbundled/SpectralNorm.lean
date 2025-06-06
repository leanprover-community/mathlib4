/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.InvariantExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The spectral norm and the norm extension theorem

This file shows that if `K` is a nonarchimedean normed field and `L/K` is an algebraic extension,
then there is a natural extension of the norm on `K` to a `K`-algebra norm on `L`, the so-called
*spectral norm*. The spectral norm of an element of `L` only depends on its minimal polynomial
over `K`, so for `K ⊆ L ⊆ M` are two extensions of `K`, the spectral norm on `M` restricts to the
spectral norm on `L`. This work can be used to uniquely extend the `p`-adic norm on `ℚ_[p]` to an
algebraic closure of `ℚ_[p]`, for example.

## Details

We define the spectral value and the spectral norm. We prove the norm extension theorem
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Theorem 3.2.1/2)]
[bosch-guntzer-remmert] : given a nonarchimedean normed field `K` and an algebraic
extension `L/K`, the spectral norm is a power-multiplicative `K`-algebra norm on `L` extending
the norm on `K`. All `K`-algebra automorphisms of `L` are isometries with respect to this norm.
If `L/K` is finite, we get a formula relating the spectral norm on `L` with any other
power-multiplicative norm on `L` extending the norm on `K`.

As a prerequisite, we formalize the proof of [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert].

## Main Definitions

* `spectralValue` : the spectral value of a polynomial in `R[X]`.
* `spectralNorm` :The spectral norm `|y|_sp` is the spectral value of the minimal polynomial
  of `y : L` over `K`.
* `spectralAlgNorm` : the spectral norm is a `K`-algebra norm on `L`.

## Main Results

* `norm_le_spectralNorm` : if `f` is a power-multiplicative `K`-algebra norm on `L`, then `f` is
  bounded above by `spectralNorm K L`.
* `spectralNorm_eq_of_equiv` : the `K`-algebra automorphisms of `L` are isometries with respect to
  the spectral norm.
* `spectralNorm_eq_iSup_of_finiteDimensional_normal` : if `L/K` is finite and normal, then
  `spectralNorm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`.
* `isPowMul_spectralNorm` : the spectral norm is power-multiplicative.
* `isNonarchimedean_spectralNorm` : the spectral norm is nonarchimedean.
* `spectralNorm_extends` : the spectral norm extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, spectral value, seminorm, norm, nonarchimedean
-/

open Polynomial

open scoped Polynomial


noncomputable section

variable {R : Type*}

section spectralValue

open Nat Real

section Seminormed

variable [SeminormedRing R]

/-- The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.natDegree - n : ℝ))`, if
  `n < p.natDegree`, or to `0` otherwise. -/
def spectralValueTerms (p : R[X]) : ℕ → ℝ := fun n : ℕ ↦
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) else 0

theorem spectralValueTerms_of_lt_natDegree (p : R[X]) {n : ℕ} (hn : n < p.natDegree) :
    spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) := by
  simp [spectralValueTerms, if_pos hn]

theorem spectralValueTerms_of_natDegree_le (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    spectralValueTerms p n = 0 := by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

/-- The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation
  for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial
  splits into linear factors, then its spectral value is the norm of its largest root.
  See `max_norm_root_eq_spectralValue`. -/
def spectralValue (p : R[X]) : ℝ := iSup (spectralValueTerms p)

/-- The range of `spectralValue_terms p` is a finite set. -/
theorem spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerms p)).Finite :=
  Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio p.natDegree).image (fun n ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)))) <| by
      aesop (add simp [Set.range_subset_iff, spectralValueTerms])

open List in
/-- The sequence `spectralValue_terms p` is bounded above. -/
theorem spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValueTerms p)) :=
  (spectralValueTerms_finite_range p).bddAbove

/-- The sequence `spectralValue_terms p` is nonnegative. -/
theorem spectralValueTerms_nonneg (p : R[X]) (n : ℕ) : 0 ≤ spectralValueTerms p n := by
  simp only [spectralValueTerms]
  split_ifs with h
  · exact rpow_nonneg (norm_nonneg _) _
  · exact le_refl _

/-- The spectral value of a polyomial is nonnegative. -/
theorem spectralValue_nonneg (p : R[X]) : 0 ≤ spectralValue p :=
  iSup_nonneg (spectralValueTerms_nonneg p)

variable [Nontrivial R]

/-- The polynomial `X - r` has spectral value `‖ r ‖`. -/
theorem spectralValue_X_sub_C (r : R) : spectralValue (X - C r) = ‖r‖ := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, lt_one_iff, coeff_sub, cast_one, one_div]
  suffices (⨆ n : ℕ, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, cast_zero, sub_zero, coeff_X_zero, coeff_C_zero, zero_sub,
        norm_neg, inv_one, rpow_one]
    · rw [if_neg hn, if_neg hn]
  · apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun n ↦ ?_)
      (fun _ hx ↦ ⟨0, by simp only [eq_self_iff_true, if_true, hx]⟩)
    split_ifs
    · exact le_refl _
    · exact norm_nonneg _

/-- The polynomial `X ^ n` has spectral value `0`. -/
theorem spectralValue_X_pow (n : ℕ) : spectralValue (X ^ n : R[X]) = 0 := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert ciSup_const using 2
  · ext m
    by_cases hmn : m < n
    · rw [if_pos hmn, rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (_root_.ne_of_lt hmn),
        norm_zero, one_div, ne_eq, inv_eq_zero, ← cast_sub (le_of_lt hmn), cast_eq_zero,
        Nat.sub_eq_zero_iff_le]
      exact ⟨Eq.refl _, not_le_of_lt hmn⟩
    · rw [if_neg hmn]
  · infer_instance

end Seminormed

section Normed

variable [NormedRing R]

/-- The spectral value of `p` equals zero if and only if `p` is of the form `X ^ n`. -/
theorem spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    spectralValue p = 0 ↔ p = X ^ p.natDegree := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ spectralValue_X_pow p.natDegree⟩
  rw [spectralValue] at h
  ext n
  rw [coeff_X_pow]
  split_ifs with hn
  · rw [hn, coeff_natDegree]; exact hp
  · by_cases hn' : n < p.natDegree
    · have h_le : iSup (spectralValueTerms p) ≤ 0 := h.le
      have h_exp : 0 < 1 / ((p.natDegree : ℝ) - n) := by
        rw [one_div_pos, ← cast_sub (le_of_lt hn'), cast_pos]
        exact Nat.sub_pos_of_lt hn'
      have h0 : (0 : ℝ) = 0 ^ (1 / ((p.natDegree : ℝ) - n)) := by rw [zero_rpow (ne_of_gt h_exp)]
      rw [iSup, csSup_le_iff (spectralValueTerms_bddAbove p) (Set.range_nonempty _)] at h_le
      specialize h_le (spectralValueTerms p n) ⟨n, rfl⟩
      simp only [spectralValueTerms, if_pos hn'] at h_le
      rw [h0, rpow_le_rpow_iff (norm_nonneg _) (le_refl _) h_exp] at h_le
      exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _))
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn))

end Normed

end spectralValue

/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert]. -/
section BddBySpectralValue

open Real

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]

open Nat in
/-- The norm of any root of `p` is bounded by the spectral value of `p`. See
[S. Bosch, U. Güntzer, R. Remmert,*Non-Archimedean Analysis* (Proposition 3.1.2/1(1))]
[bosch-guntzer-remmert]. -/
theorem norm_root_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) :
    f x ≤ spectralValue p := by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt : ∀ (n : ℕ) (_ : n < p.natDegree), ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      intro n hn
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))) ^ (p.natDegree - n) =
          ‖p.coeff n‖ := by
        rw [← rpow_natCast, ← rpow_mul (norm_nonneg _), mul_comm, rpow_mul (norm_nonneg _),
          rpow_natCast, ← cast_sub (le_of_lt hn), one_div,
          pow_rpow_inv_natCast (norm_nonneg _) (_root_.ne_of_gt (tsub_pos_of_lt hn))]
      have h_base : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) < f x := by
        rw [spectralValue, iSup, not_le, Set.Finite.csSup_lt_iff (spectralValueTerms_finite_range p)
          (Set.range_nonempty (spectralValueTerms p))] at h_ge
        have h_rg : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) ∈
          Set.range (spectralValueTerms p) := by use n; simp only [spectralValueTerms, if_pos hn]
        exact h_ge (‖p.coeff n‖₊ ^ (1 / (p.natDegree - n : ℝ))) h_rg
      rw [← hexp, ← rpow_natCast, ← rpow_natCast]
      exact rpow_lt_rpow (rpow_nonneg (norm_nonneg _) _) h_base (cast_pos.mpr (tsub_pos_of_lt hn))
    have h_deg : 0 < p.natDegree := natDegree_pos_of_monic_of_aeval_eq_zero hp hx
    have h_lt : f ((Finset.range p.natDegree).sum fun i : ℕ ↦ p.coeff i • x ^ i) <
        f (x ^ p.natDegree) := by
      have hn' : ∀ (n : ℕ) (_ : n < p.natDegree), f (p.coeff n • x ^ n) < f (x ^ p.natDegree) := by
        intro n hn
        by_cases hn0 : n = 0
        · rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (succ_le_iff.mpr h_deg),
            ← Nat.sub_zero p.natDegree, ← hn0]
          exact (mul_le_of_le_one_right (norm_nonneg _) hf_pm.map_one_le_one).trans_lt (hn_lt n hn)
        · have : p.natDegree = p.natDegree - n + n := by rw [Nat.sub_add_cancel (le_of_lt hn)]
          rw [map_smul_eq_mul, hf_pm _ (succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)),
            hf_pm _ (succ_le_iff.mpr h_deg), this, pow_add]
          exact (mul_lt_mul_right (pow_pos (lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hx0)) _)).mpr
            (hn_lt n hn)
      set g := fun i : ℕ ↦ p.coeff i • x ^ i
      obtain ⟨m, hm_in, hm⟩ : ∃ (m : ℕ) (_ : 0 < p.natDegree → m < p.natDegree),
          f ((Finset.range p.natDegree).sum g) ≤ f (g m) := by
        obtain ⟨m, hm, h⟩ := IsNonarchimedean.finset_image_add hf_na g (Finset.range p.natDegree)
        rw [Finset.nonempty_range_iff, ← zero_lt_iff, Finset.mem_range] at hm
        exact ⟨m, hm, h⟩
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))
    have h0 : f 0 ≠ 0 := by
      have h_eq : f 0 = f (x ^ p.natDegree) := by
        rw [← hx, aeval_eq_sum_range, Finset.sum_range_succ, add_comm, hp.coeff_natDegree,
          one_smul, ← max_eq_left_of_lt h_lt]
        exact IsNonarchimedean.add_eq_max_of_ne hf_na (ne_of_gt h_lt)
      exact h_eq ▸ ne_of_gt (lt_of_le_of_lt (apply_nonneg _ _) h_lt)
    exact h0 (map_zero _)

open Multiset

/-- If `f` is a nonarchimedean, power-multiplicative `K`-algebra norm on `L`, then the spectral
value of a polynomial `p : K[X]` that decomposes into linear factos in `L` is equal to the
maximum of the norms of the roots. See [S. Bosch, U. Güntzer, R. Remmert,*Non-Archimedean Analysis*
(Proposition 3.1.2/1(2))][bosch-guntzer-remmert]. -/
theorem max_norm_root_eq_spectralValue [DecidableEq L] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (map (fun a : L ↦ X - C a) s).prod) :
    (⨆ x : L, if x ∈ s then f x else 0) = spectralValue p := by
  have h_le : 0 ≤ ⨆ x : L, ite (x ∈ s) (f x) 0 := by
    apply iSup_nonneg (fun _ ↦ ?_)
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le (fun x ↦ ?_)
    by_cases hx : x ∈ s
    · have hx0 : aeval x p = 0 := aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s hx hp
      rw [if_pos hx]
      exact norm_root_le_spectralValue hf_pm hf_na
        (monic_of_monic_mapAlg (hp ▸ monic_multisetProd_X_sub_C s)) hx0
    · simp only [if_neg hx, spectralValue_nonneg _]
  · apply ciSup_le (fun m ↦ ?_)
    by_cases hm : m < p.natDegree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.natDegree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← rpow_le_rpow_iff (rpow_nonneg (norm_nonneg _) _) h_le h, ← rpow_mul (norm_nonneg _),
        one_div_mul_cancel (ne_of_gt h), rpow_one, ← Nat.cast_sub (le_of_lt hm), rpow_natCast]
      have hps : card s = p.natDegree := by
        rw [← natDegree_map (algebraMap K L), ← mapAlg_eq_map, hp,
          natDegree_multiset_prod_X_sub_C_eq_card]
      have hc : ‖p.coeff m‖ = f (((mapAlg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, mapAlg_eq_map, coeff_map]
      rw [hc, hp, prod_X_sub_C_coeff s (hps ▸ le_of_lt hm)]
      have h : f ((-1) ^ (card s - m) * s.esymm (card s - m)) = f (s.esymm (card s - m)) := by
        rcases neg_one_pow_eq_or L (card s - m) with h1 | hn1
        · rw [h1, one_mul]
        · rw [hn1, neg_mul, one_mul, map_neg_eq_map]
      rw [h, esymm]
      obtain ⟨t, ht_card, hts, ht_ge⟩ : ∃ t : Multiset L, card t = card s - m ∧
          (∀ x : L, x ∈ t → x ∈ s) ∧ f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod :=
        hf_na.multiset_powerset_image_add s m
      apply le_trans ht_ge
      have h_pr : f t.prod ≤ (t.map f).prod := le_prod_of_submultiplicative_of_nonneg f
        (apply_nonneg _) (le_of_eq hf1) (map_mul_le_mul _) t
      apply le_trans h_pr
      have hs_ne : s ≠ 0 :=
        have hpos : 0 < s.toFinset.card := by
          have hs0 : 0 < s.card := hps ▸ lt_of_le_of_lt (zero_le _) hm
          obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hs0
          exact Finset.card_pos.mpr ⟨x, mem_toFinset.mpr hx⟩
        toFinset_nonempty.mp (Finset.card_pos.mp hpos)
      obtain ⟨y, hyx, hy_max⟩ : ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y :=
        exists_max_image f hs_ne
      have : (map f t).prod ≤ f y ^ (p.natDegree - m) := by
        set g : L → NNReal := fun x ↦ ⟨f x, apply_nonneg f x⟩
        have h_card : p.natDegree - m = card (t.map g) := by rw [card_map, ht_card, ← hps]
        have hx_le : ∀ x : NNReal, x ∈ map g t → x ≤ g y := by
          intro r hr
          obtain ⟨_, hzt, hzr⟩ := mem_map.mp hr
          exact hzr ▸ hy_max _ (hts _ hzt)
        have : (map g t).prod ≤ g y ^ (p.natDegree - m) := h_card ▸ prod_le_pow_card _ _ hx_le
        simpa [g, ← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_mk, NNReal.coe_multiset_prod,
          map_map, Function.comp_apply, NNReal.coe_mk] using this
      have h_bdd : BddAbove (Set.range fun x : L ↦ ite (x ∈ s) (f x) 0) := by
        use f y
        intro r hr
        obtain ⟨z, hz⟩ := Set.mem_range.mpr hr
        simp only at hz
        rw [← hz]
        split_ifs with h
        · exact hy_max _ h
        · exact apply_nonneg _ _
      exact le_trans this (pow_le_pow_left₀ (apply_nonneg _ _)
        (le_trans (by rw [if_pos hyx]) (le_ciSup h_bdd y)) _)
    · simp only [spectralValueTerms, if_neg hm, h_le]

end BddBySpectralValue


section spectralNorm
/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert,*Non-Archimedean Analysis*
(Theorem 3.2.1/2)][bosch-guntzer-remmert]. -/

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

/-- If `L` is an algebraic extension of a normed field `K` and `y : L` then the spectral norm
  `spectralNorm K y : ℝ` of `y` (written `|y|_sp` in the textbooks) is the spectral value of the
  minimal polynomial of `y` over `K`. -/
def spectralNorm (y : L) : ℝ := spectralValue (minpoly K y)

variable {K L}

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` equals its spectral norm
  when regarding `x` as an element of `L`. -/
theorem spectralNorm.eq_of_tower {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm K E x = spectralNorm K L (algebraMap E L x) := by
  have hx :  minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

variable (E : IntermediateField K L)

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` when regarded as an element
  of the normal closure of `E` equals its spectral norm when regarding `x` as an element of `L`. -/
theorem spectralNorm.eq_of_normalClosure' (x : E) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
      (algebraMap E (normalClosure K E (AlgebraicClosure E)) x) =
    spectralNorm K L (algebraMap E L x) := by
  simp only [spectralNorm, spectralValue]
  have h_min : minpoly K (algebraMap (↥E) (↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) x) =
      minpoly K (algebraMap (↥E) L x) := by
    rw [minpoly.algebraMap_eq (algebraMap (↥E) ↥(normalClosure K E (AlgebraicClosure E))).injective
      x, ← minpoly.algebraMap_eq (algebraMap (↥E) L).injective x]
  simp_rw [h_min]

/-- If `L/E/K` is a tower of fields and `x = algebraMap E L g`, then then the spectral norm
  of `g : E` when regarded as an element of the normal closure of `E` equals the spectral norm
  of `x : L`. -/
theorem spectralNorm.eq_of_normalClosure {E : IntermediateField K L} {x : L} (g : E)
    (h_map : algebraMap E L g = x) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
        (algebraMap E (normalClosure K E (AlgebraicClosure E)) g) =
      spectralNorm K L x :=
  h_map ▸ spectralNorm.eq_of_normalClosure' E g

variable (y : L)

open Real

/-- `spectralNorm K L (0 : L) = 0`. -/
theorem spectralNorm_zero : spectralNorm K L (0 : L) = 0 := by
  unfold spectralNorm
  rw [minpoly.zero, ← pow_one X, spectralValue_X_pow 1]

/-- `spectralNorm K L y` is nonnegative. -/
theorem spectralNorm_nonneg (y : L) : 0 ≤ spectralNorm K L y :=
  le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

/-- `spectralNorm K L y` is positive if `y ≠ 0`. -/
theorem spectralNorm_zero_lt {y : L} (hy : y ≠ 0) (hy_alg : IsAlgebraic K y) :
    0 < spectralNorm K L y := by
  apply lt_of_le_of_ne (spectralNorm_nonneg _)
  rw [spectralNorm, ne_eq, eq_comm, spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  intro h
  apply minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  rw [h, coeff_X_pow, if_neg (ne_of_lt (minpoly.natDegree_pos hy_alg.isIntegral))]

/-- If `spectralNorm K L x = 0`, then `x = 0`. -/
theorem eq_zero_of_map_spectralNorm_eq_zero {x : L} (hx : spectralNorm K L x = 0)
    (hx_alg : IsAlgebraic K x) : x = 0 := by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

/-- If `f` is a power-multiplicative `K`-algebra norm on `L`, then `f`
  is bounded above by `spectralNorm K L`. -/
theorem norm_le_spectralNorm {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {x : L} (hx_alg : IsAlgebraic K x) :
    f x ≤ spectralNorm K L x :=
  norm_root_le_spectralValue hf_pm hf_na (minpoly.monic hx_alg.isIntegral)
    (by rw [minpoly.aeval])

/-- The `K`-algebra automorphisms of `L` are isometries with respect to the spectral norm. -/
theorem spectralNorm_eq_of_equiv (σ : L ≃ₐ[K] L) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

-- We first assume that the extension is finite and normal

section FiniteNormal

variable (K L) [h_fin : FiniteDimensional K L] [hn : Normal K L]

/--
If `L/K` is finite and normal, then `spectralNorm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`. -/
theorem spectralNorm_eq_iSup_of_finiteDimensional_normal
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    spectralNorm K L x = ⨆ σ : L ≃ₐ[K] L, f (σ x) := by
  classical
  have hf1 : f 1 = 1 := by
    rw [← (algebraMap K L).map_one, hf_ext]
    simp [nnnorm_one, NNReal.coe_nonneg]
  refine le_antisymm ?_ (ciSup_le fun σ ↦
    norm_root_le_spectralValue hf_pm hf_na
      (minpoly.monic (hn.isIntegral x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have hp_sp : Splits (algebraMap K L) (minpoly K x) := hn.splits x
    obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).mp hp_sp
    have h_lc : (algebraMap K L) (minpoly K x).leadingCoeff = 1 := by
      rw [minpoly.monic (hn.isIntegral x), map_one]
    rw [h_lc, map_one, one_mul] at hs
    simp only [spectralNorm]
    rw [← max_norm_root_eq_spectralValue hf_pm hf_na hf1 _ _ hs]
    apply ciSup_le
    intro y
    split_ifs with h
    · obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[K] L, σ x = y := minpoly.exists_algEquiv_of_root'
        (Algebra.IsAlgebraic.isAlgebraic x) (aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s h hs)
      rw [← hσ]
      convert le_ciSup (Finite.bddAbove_range _) σ
      · rfl
      · exact instNonemptyOfInhabited
      · exact SemilatticeSup.to_isDirected_le
    · exact iSup_nonneg fun σ ↦ apply_nonneg _ _

open IsUltrametricDist

/-- If `L/K` is finite and normal, then `spectralNorm K L = invariantExtension K L`. -/
theorem spectralNorm_eq_invariantExtension [hu : IsUltrametricDist K] :
    spectralNorm K L = invariantExtension K L := by
  ext x
  have hna := hu.isNonarchimedean_norm
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
    with hf
  have hf_pow : IsPowMul f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖ := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.1
  have hf_na : IsNonarchimedean f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.2
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pow hf_na hf_ext]
  simp only [invariantExtension_apply, algNormOfAlgEquiv_apply, hf]

/- Note that the main results below are reproved without the finite dimensionality and normality
  assumptions later on in this file. -/

/-- If `L/K` is finite and normal, then `spectralNorm K L` is power-multiplicative.
  See also the more general result `isPowMul_spectralNorm`. -/
theorem isPowMul_spectralNorm_of_finiteDimensional_normal [IsUltrametricDist K] :
    IsPowMul (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension K L]
  exact isPowMul_invariantExtension K L

/-- The spectral norm is a `K`-algebra norm on `L` when `L/K` is finite and normal.
  See also `spectralAlgNorm` for a more general construction. -/
def spectralAlgNorm_of_finiteDimensional_normal [IsUltrametricDist K] : AlgebraNorm K L where
  toFun     := spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_invariantExtension K L, map_zero]
  add_le'   := by rw [spectralNorm_eq_invariantExtension]; exact map_add_le_add _
  neg'      := by rw [spectralNorm_eq_invariantExtension]; exact map_neg_eq_map _
  mul_le'   :=  by
    simp only [spectralNorm_eq_invariantExtension]
    exact map_mul_le_mul (invariantExtension K L)
  smul'     := by
    simp [spectralNorm_eq_invariantExtension, AlgebraNormClass.map_smul_eq_mul _]
  eq_zero_of_map_eq_zero' x := by
    simp only [spectralNorm_eq_invariantExtension]
    exact eq_zero_of_map_eq_zero _

theorem spectralAlgNorm_of_finiteDimensional_normal_def [IsUltrametricDist K] (x : L) :
    spectralAlgNorm_of_finiteDimensional_normal K L x = spectralNorm K L x := rfl

/-- The spectral norm is nonarchimedean when `L/K` is finite and normal.
  See also `isNonarchimedean_spectralNorm` for a more general result. -/
theorem isNonarchimedean_spectralNorm_of_finiteDimensional_normal
    [IsUltrametricDist K] : IsNonarchimedean (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension]
  exact isNonarchimedean_invariantExtension K L

/-- The spectral norm extends the norm on `K` when `L/K` is finite and normal.
  See also `spectralNorm_extends` for a more general result. -/
theorem spectralNorm_extends_of_finiteDimensional [IsUltrametricDist K] (x : K) :
    spectralNorm K L (algebraMap K L x) = ‖x‖ := by
  rw [spectralNorm_eq_invariantExtension, invariantExtension_extends K L x]

/-- If `L/K` is finite and normal, and `f` is a power-multiplicative `K`-algebra norm on `L`
  extending the norm on `K`, then `f = spectralNorm K L`. -/
theorem spectralNorm_unique_of_finiteDimensional_normal {f : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖₊)
    (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x : L), f x = f (σ x)) (x : L) : f x = spectralNorm K L x := by
  have h_sup : (⨆ σ : L ≃ₐ[K] L, f (σ x)) = f x := by
    rw [← @ciSup_const _ (L ≃ₐ[K] L) _ _ (f x)]
    exact iSup_congr fun σ ↦ by rw [hf_iso σ x]
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pm hf_na hf_ext, h_sup]

end FiniteNormal

-- Now we let `L/K` be any algebraic extension.

open scoped IntermediateField

instance : SeminormClass (AlgebraNorm K ↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) K
  ↥(normalClosure K (↥E) (AlgebraicClosure ↥E)) := AlgebraNormClass.toSeminormClass

/-- The spectral norm extends the norm on `K`. -/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ := by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_X_sub_C k

theorem spectralNorm_one : spectralNorm K L 1 = 1 := by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

variable [IsUltrametricDist K]

/-- `spectralNorm K L (-y) = spectralNorm K L y` . -/
theorem spectralNorm_neg {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (-y) = spectralNorm K L y := by
  set E := K⟮y⟯
  haveI h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hy,
    ← spectralNorm.eq_of_normalClosure (-g) hy, RingHom.map_neg,
    ← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_neg_eq_map _ _

/-- The spectral norm is compatible with the action of `K`. -/
theorem spectralNorm_smul (k : K) {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (k • y) = ‖k‖₊ * spectralNorm K L y := by
  set E := K⟮y⟯
  haveI h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) (k • g) =
      k • algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) g := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_assoc]
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hgy,
    ← spectralNorm.eq_of_normalClosure (k • g) rfl, h]
  rw [← spectralAlgNorm_of_finiteDimensional_normal_def]
  apply map_smul_eq_mul

/-- The spectral norm is submultiplicative. -/
theorem spectralNorm_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) ≤ spectralNorm K L x * spectralNorm K L y := by
  set E := K⟮x, y⟯
  haveI h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, y⟯ L) (gx * gy) := rfl
  rw [hxy, ← spectralNorm.eq_of_normalClosure (gx * gy) hxy,
    ← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y),
    ← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y),
    map_mul, ← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_mul_le_mul _ _ _

section IsAlgebraic

variable [h_alg : Algebra.IsAlgebraic K L]

/-- The spectral norm is power-multiplicative. -/
theorem isPowMul_spectralNorm : IsPowMul (spectralNorm K L) := by
  intro x n hn
  set E := K⟮x⟯
  haveI h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  rw [← spectralNorm.eq_of_normalClosure _ (IntermediateField.AdjoinSimple.algebraMap_gen K x),
    ← spectralNorm.eq_of_normalClosure (g ^ n) h_map, map_pow, ← hg]
  exact isPowMul_spectralNorm_of_finiteDimensional_normal _ _
    ((algebraMap ↥K⟮x⟯ ↥(normalClosure K (↥K⟮x⟯) (AlgebraicClosure ↥K⟮x⟯))) g) hn

/-- The spectral norm is nonarchimedean. -/
theorem isNonarchimedean_spectralNorm : IsNonarchimedean (spectralNorm K L) := by
  intro x y
  set E := K⟮x, y⟯
  haveI h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x + y = (algebraMap K⟮x, y⟯ L) (gx + gy) := rfl
  rw [hxy, ← spectralNorm.eq_of_normalClosure (gx + gy) hxy,
    ← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y),
    ← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y),
    _root_.map_add]
  apply isNonarchimedean_spectralNorm_of_finiteDimensional_normal

variable (K L) in
/-- The spectral norm is a `K`-algebra norm on `L`. -/
def spectralAlgNorm : AlgebraNorm K L where
  toFun       := spectralNorm K L
  map_zero'   := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg isNonarchimedean_spectralNorm
  mul_le' x y := spectralNorm_mul (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x   := spectralNorm_smul k (h_alg.isAlgebraic x)
  neg' x      := spectralNorm_neg (h_alg.isAlgebraic x)
  eq_zero_of_map_eq_zero' x hx := eq_zero_of_map_spectralNorm_eq_zero hx (h_alg.isAlgebraic x)

theorem spectralAlgNorm_def (x : L) : spectralAlgNorm K L x = spectralNorm K L x := rfl

theorem spectralAlgNorm_extends (k : K) : spectralAlgNorm K L (algebraMap K L k) = ‖k‖ :=
  spectralNorm_extends k

theorem spectralAlgNorm_one : spectralAlgNorm K L (1 : L) = 1 := spectralNorm_one

theorem spectralAlgNorm_isPowMul : IsPowMul (spectralAlgNorm K L) := isPowMul_spectralNorm

end IsAlgebraic

end spectralNorm
