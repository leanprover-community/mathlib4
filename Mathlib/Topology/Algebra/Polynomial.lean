/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `Polynomial.continuous_eval₂`: `Polynomial.eval₂` defines a continuous function.
* `Polynomial.continuous_aeval`: `Polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `Polynomial.continuousAt_aeval`,
  `Polynomial.continuousWithinAt_aeval`, `Polynomial.continuousOn_aeval`.
* `Polynomial.continuous`:  `Polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `Polynomial.continuousAt`, `Polynomial.continuousWithinAt`,
  `Polynomial.continuousOn`.
* `Polynomial.tendsto_norm_atTop`: `fun x ↦ ‖Polynomial.eval (z x) p‖` tends to infinity provided
  that `fun x ↦ ‖z x‖` tends to infinity and `0 < degree p`;
* `Polynomial.tendsto_abv_eval₂_atTop`, `Polynomial.tendsto_abv_atTop`,
  `Polynomial.tendsto_abv_aeval_atTop`: a few versions of the previous statement for
  `IsAbsoluteValue abv` instead of norm.

## Tags

Polynomial, continuity
-/


open IsAbsoluteValue Filter

namespace Polynomial

section IsTopologicalSemiring

variable {R S : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] (p : R[X])

@[continuity, fun_prop]
protected theorem continuous_eval₂ [Semiring S] (p : S[X]) (f : S →+* R) :
    Continuous fun x => p.eval₂ f x := by
  simp only [eval₂_eq_sum]
  exact continuous_finset_sum _ fun c _ => continuous_const.mul (continuous_pow _)

@[continuity, fun_prop]
protected theorem continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _

@[fun_prop]
protected theorem continuousAt {a : R} : ContinuousAt (fun x => p.eval x) a :=
  p.continuous.continuousAt

@[fun_prop]
protected theorem continuousWithinAt {s a} : ContinuousWithinAt (fun x => p.eval x) s a :=
  p.continuous.continuousWithinAt

@[fun_prop]
protected theorem continuousOn {s} : ContinuousOn (fun x => p.eval x) s :=
  p.continuous.continuousOn

end IsTopologicalSemiring

section TopologicalAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A] (p : R[X])

@[continuity, fun_prop]
protected theorem continuous_aeval : Continuous fun x : A => aeval x p :=
  p.continuous_eval₂ _

@[fun_prop]
protected theorem continuousAt_aeval {a : A} : ContinuousAt (fun x : A => aeval x p) a :=
  p.continuous_aeval.continuousAt

@[fun_prop]
protected theorem continuousWithinAt_aeval {s a} :
    ContinuousWithinAt (fun x : A => aeval x p) s a :=
  p.continuous_aeval.continuousWithinAt

@[fun_prop]
protected theorem continuousOn_aeval {s} : ContinuousOn (fun x : A => aeval x p) s :=
  p.continuous_aeval.continuousOn

end TopologicalAlgebra

theorem tendsto_abv_eval₂_atTop {R S k α : Type*} [Semiring R] [Ring S]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : R →+* S) (abv : S → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (hf : f p.leadingCoeff ≠ 0) {l : Filter α} {z : α → S} (hz : Tendsto (abv ∘ z) l atTop) :
    Tendsto (fun x => abv (p.eval₂ f (z x))) l atTop := by
  revert hf; refine degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [leadingCoeff_mul_X, leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] using (ihp hf).atTop_mul_atTop₀ hz
  · intro _ a hd ihp hf
    rw [add_comm, leadingCoeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf
    refine .atTop_of_add_const (abv (-f a)) ?_
    refine tendsto_atTop_mono (fun _ => abv_add abv _ _) ?_
    simpa using ihp hf

theorem tendsto_abv_atTop {R k α : Type*} [Ring R]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k] (abv : R → k)
    [IsAbsoluteValue abv] (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (p.eval (z x))) l atTop := by
  apply tendsto_abv_eval₂_atTop _ _ _ h _ hz
  exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

theorem tendsto_abv_aeval_atTop {R A k α : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (abv : A → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (h₀ : algebraMap R A p.leadingCoeff ≠ 0) {l : Filter α} {z : α → A}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (aeval (z x) p)) l atTop :=
  tendsto_abv_eval₂_atTop _ abv p hd h₀ hz

variable {α R : Type*} [NormedRing R] [IsAbsoluteValue (norm : R → ℝ)]

theorem tendsto_norm_atTop (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) : Tendsto (fun x => ‖p.eval (z x)‖) l atTop :=
  p.tendsto_abv_atTop norm h hz

theorem exists_forall_norm_le [ProperSpace R] (p : R[X]) : ∃ x, ∀ y, ‖p.eval x‖ ≤ ‖p.eval y‖ :=
  if hp0 : 0 < degree p then
    p.continuous.norm.exists_forall_le <| p.tendsto_norm_atTop hp0 tendsto_norm_cocompact_atTop
  else
    ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

section Roots

open Polynomial NNReal

variable {F K : Type*} [CommRing F] [NormedField K]

open Multiset

theorem eq_one_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (hB : B < 0) (h1 : p.Monic)
    (h2 : Splits f p) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) : p = 1 :=
  h1.natDegree_eq_zero_iff_eq_one.mp (by
    contrapose! hB
    rw [← h1.natDegree_map f, natDegree_eq_card_roots' h2] at hB
    obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB)
    exact le_trans (norm_nonneg _) (h3 z hz))

theorem coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ) (h1 : p.Monic)
    (h2 : Splits f p) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) :
    ‖(map f p).coeff i‖ ≤ B ^ (p.natDegree - i) * p.natDegree.choose i := by
  obtain hB | hB := lt_or_ge B 0
  · rw [eq_one_of_roots_le hB h1 h2 h3, Polynomial.map_one, natDegree_one, zero_tsub, pow_zero,
      one_mul, coeff_one]
    split_ifs with h <;> simp [h]
  rw [← h1.natDegree_map f]
  obtain hi | hi := lt_or_ge (map f p).natDegree i
  · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
    positivity
  rw [coeff_eq_esymm_roots_of_splits ((splits_id_iff_splits f).2 h2) hi, (h1.map _).leadingCoeff,
    one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  apply ((norm_multiset_sum_le _).trans <| sum_le_card_nsmul _ _ fun r hr => _).trans
  · rw [Multiset.map_map, card_map, card_powersetCard, ← natDegree_eq_card_roots' h2,
      Nat.choose_symm hi, mul_comm, nsmul_eq_mul]
  intro r hr
  simp_rw [Multiset.mem_map] at hr
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hr
  rw [mem_powersetCard] at hs
  lift B to ℝ≥0 using hB
  rw [← coe_nnnorm, ← NNReal.coe_pow, NNReal.coe_le_coe, ← nnnormHom_apply, ← MonoidHom.coe_coe,
    MonoidHom.map_multiset_prod]
  refine (prod_le_pow_card _ B fun x hx => ?_).trans_eq (by rw [card_map, hs.2])
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
  exact h3 z (mem_of_le hs.1 hz)

/-- The coefficients of the monic polynomials of bounded degree with bounded roots are
uniformly bounded. -/
theorem coeff_bdd_of_roots_le {B : ℝ} {d : ℕ} (f : F →+* K) {p : F[X]} (h1 : p.Monic)
    (h2 : Splits f p) (h3 : p.natDegree ≤ d) (h4 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) (i : ℕ) :
    ‖(map f p).coeff i‖ ≤ max B 1 ^ d * d.choose (d / 2) := by
  obtain hB | hB := le_or_gt 0 B
  · apply (coeff_le_of_roots_le i h1 h2 h4).trans
    calc
      _ ≤ max B 1 ^ (p.natDegree - i) * p.natDegree.choose i := by gcongr; apply le_max_left
      _ ≤ max B 1 ^ d * p.natDegree.choose i := by
        gcongr
        · apply le_max_right
        · exact le_trans (Nat.sub_le _ _) h3
      _ ≤ max B 1 ^ d * d.choose (d / 2) := by
        gcongr; exact (i.choose_mono h3).trans (i.choose_le_middle d)
  · rw [eq_one_of_roots_le hB h1 h2 h4, Polynomial.map_one, coeff_one]
    refine le_trans ?_ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right B 1)) ?_)
    · split_ifs <;> norm_num
    · exact mod_cast Nat.succ_le_iff.mpr (Nat.choose_pos (d.div_le_self 2))

end Roots

end Polynomial
