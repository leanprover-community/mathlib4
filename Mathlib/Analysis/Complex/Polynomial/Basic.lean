/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Yury Kudryashov
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Topology.Algebra.Polynomial

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also provide some specific results about the Galois groups of ℚ-polynomials with specific numbers
of non-real roots.

We also show that an irreducible real polynomial has degree at most two.
-/

open Polynomial Bornology Complex

open scoped ComplexConjugate

namespace Complex

/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf

instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp

end Complex

/-- An algebraic extension of ℝ is isomorphic to either ℝ or ℂ as an ℝ-algebra. -/
theorem Real.nonempty_algEquiv_or (F : Type*) [Field F] [Algebra ℝ F] [Algebra.IsAlgebraic ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

namespace Polynomial.Gal

section Rationals

theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact (p.Splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain p⟩

attribute [local instance] splits_ℚ_ℂ
attribute [local ext] Complex.ext

/-- The number of complex roots equals the number of real roots plus
the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : ℚ[X]) :
    (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card +
        (galActionHom p ℂ (restrict p ℂ
        (AlgEquiv.restrictScalars ℚ Complex.conjAe))).support.card := by
  by_cases hp : p = 0
  · haveI : IsEmpty (p.rootSet ℂ) := by rw [hp, rootSet_zero]; infer_instance
    simp_rw [(galActionHom p ℂ _).support.eq_empty_of_isEmpty, hp, rootSet_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom ℚ ℝ ℂ) := (algebraMap ℝ ℂ).injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective, ←
    Finset.card_image_of_injective _ inj]
  let a : Finset ℂ := ?_
  on_goal 1 => let b : Finset ℂ := ?_
  on_goal 1 => let c : Finset ℂ := ?_
  change a.card = b.card + c.card
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 := by
    intro z; rw [Set.mem_toFinset, mem_rootSet_of_ne hp]
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [b, Finset.mem_image, Set.mem_toFinset, mem_rootSet_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [aeval_algHom_apply, hw, map_zero], rfl⟩
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom ℚ ℝ ℂ z.re = z := by
        ext
        · rfl
        · rw [hz2]; rfl
      exact ⟨z.re, inj (by rwa [← aeval_algHom_apply, key, map_zero]), key⟩
  have hc0 :
    ∀ w : p.rootSet ℂ, galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ)) w = w ↔
        w.val.im = 0 := by
    intro w
    rw [Subtype.ext_iff, galActionHom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp_rw [c, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_rootSet.mp w.2).2, mt (hc0 w).mpr (Equiv.Perm.mem_support.mp hw)⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, mem_rootSet.mpr ⟨hp, hz1⟩⟩, Equiv.Perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
  rw [← Finset.card_union_of_disjoint]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb, hc]
    tauto

/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
theorem galActionHom_bijective_of_prime_degree {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (galActionHom p ℂ) := by
  classical
  have h1 : Fintype.card (p.rootSet ℂ) = p.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup, ← natDegree_eq_card_roots]
    · exact IsAlgClosed.splits_codomain p
    · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)
  let conj' := restrict p ℂ (Complex.conjAe.restrictScalars ℚ)
  refine
    ⟨galActionHom_injective p ℂ, fun x =>
      (congr_arg (x ∈ ·) (show (galActionHom p ℂ).range = ⊤ from ?_)).mpr
        (Subgroup.mem_top x)⟩
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
  · rw [h1]
    simpa only [Fintype.card_eq_nat_card,
      Nat.card_congr (MonoidHom.ofInjective (galActionHom_injective p ℂ)).toEquiv.symm]
      using prime_degree_dvd_card p_irr p_deg
  · exact ⟨conj', rfl⟩
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.toFinset_card (rootSet p ℝ), ← Set.toFinset_card (rootSet p ℂ)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm

/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
theorem galActionHom_bijective_of_prime_degree' {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.rootSet ℝ) + 1 ≤ Fintype.card (p.rootSet ℂ))
    (p_roots2 : Fintype.card (p.rootSet ℂ) ≤ Fintype.card (p.rootSet ℝ) + 3) :
    Function.Bijective (galActionHom p ℂ) := by
  apply galActionHom_bijective_of_prime_degree p_irr p_deg
  let n := (galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
         rw [← MonoidHom.map_pow, ← MonoidHom.map_pow,
          show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from
            AlgEquiv.ext Complex.conj_conj,
          MonoidHom.map_one, MonoidHom.map_one])
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  simp_rw [Set.toFinset_card] at key
  omega

end Rationals

end Polynomial.Gal

lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : (X - C ((starRingEnd ℂ) z)) * (X - C z) ∣ map (algebraMap ℝ ℂ) p := by
  apply IsCoprime.mul_dvd
  · exact isCoprime_X_sub_C_of_isUnit_sub <| .mk0 _ <| sub_ne_zero.2 <| mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

/-- If `z` is a non-real complex root of a real polynomial,
then `p` is divisible by a quadratic polynomial. -/
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p := by
  rw [← map_dvd_map' (algebraMap ℝ ℂ)]
  convert p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by simp
    _ = (X - C (conj z)) * (X - C z) := by
      rw [← add_conj, map_add, ← mul_conj', map_mul]
      ring

/-- An irreducible real polynomial has natural degree at most two. -/
lemma Irreducible.natDegree_le_two {p : ℝ[X]} (hp : Irreducible p) : natDegree p ≤ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  rw [← finrank_real_complex]
  convert minpoly.natDegree_le z using 1
  · rw [← minpoly.eq_of_irreducible hp hz, natDegree_mul hp.ne_zero (by simpa using hp.ne_zero),
      natDegree_C, add_zero]
  infer_instance

/-- An irreducible real polynomial has degree at most two. -/
lemma Irreducible.degree_le_two {p : ℝ[X]} (hp : Irreducible p) : degree p ≤ 2 :=
  natDegree_le_iff_degree_le.1 hp.natDegree_le_two
