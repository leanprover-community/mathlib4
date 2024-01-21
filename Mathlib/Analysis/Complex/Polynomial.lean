/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Topology.Algebra.Polynomial

#align_import analysis.complex.polynomial from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also provide some specific results about the Galois groups of ℚ-polynomials with specific numbers
of non-real roots.
-/

open Polynomial Bornology

open scoped Polynomial

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
#align complex.exists_root Complex.exists_root

instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp
#align complex.is_alg_closed Complex.isAlgClosed

end Complex

namespace Polynomial.Gal

section Rationals

theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact (p.Splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain p⟩
#align polynomial.gal.splits_ℚ_ℂ Polynomial.Gal.splits_ℚ_ℂ

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
  let b : Finset ℂ := ?_
  let c : Finset ℂ := ?_
  -- Porting note: was
  --   change a.card = b.card + c.card
  suffices a.card = b.card + c.card by exact this
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 := by
    intro z; rw [Set.mem_toFinset, mem_rootSet_of_ne hp]
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [Finset.mem_image, Set.mem_toFinset, mem_rootSet_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [aeval_algHom_apply, hw, AlgHom.map_zero], rfl⟩
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom ℚ ℝ ℂ z.re = z := by ext; rfl; rw [hz2]; rfl
      exact ⟨z.re, inj (by rwa [← aeval_algHom_apply, key, AlgHom.map_zero]), key⟩
  have hc0 :
    ∀ w : p.rootSet ℂ, galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ)) w = w ↔
        w.val.im = 0 := by
    intro w
    rw [Subtype.ext_iff, galActionHom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp_rw [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_rootSet.mp w.2).2, mt (hc0 w).mpr (Equiv.Perm.mem_support.mp hw)⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, mem_rootSet.mpr ⟨hp, hz1⟩⟩, Equiv.Perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
  rw [← Finset.card_disjoint_union]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb, hc]
    tauto
#align polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv

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
  have h2 : Fintype.card p.Gal = Fintype.card (galActionHom p ℂ).range :=
    Fintype.card_congr (MonoidHom.ofInjective (galActionHom_injective p ℂ)).toEquiv
  let conj := restrict p ℂ (Complex.conjAe.restrictScalars ℚ)
  refine'
    ⟨galActionHom_injective p ℂ, fun x =>
      (congr_arg (Membership.mem x) (show (galActionHom p ℂ).range = ⊤ from _)).mpr
        (Subgroup.mem_top x)⟩
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
  · rw [h1]
    convert prime_degree_dvd_card p_irr p_deg using 1
    convert h2.symm
  · exact ⟨conj, rfl⟩
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.toFinset_card (rootSet p ℝ), ← Set.toFinset_card (rootSet p ℂ)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm
#align polynomial.gal.gal_action_hom_bijective_of_prime_degree Polynomial.Gal.galActionHom_bijective_of_prime_degree

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
  rw [key, add_le_add_iff_left] at p_roots1 p_roots2
  rw [key, add_right_inj]
  suffices ∀ m : ℕ, 2 ∣ m → 1 ≤ m → m ≤ 3 → m = 2 by exact this n hn p_roots1 p_roots2
  rintro m ⟨k, rfl⟩ h2 h3
  exact le_antisymm
      (Nat.lt_succ_iff.mp
        (lt_of_le_of_ne h3 (show 2 * k ≠ 2 * 1 + 1 from Nat.two_mul_ne_two_mul_add_one)))
      (Nat.succ_le_iff.mpr
        (lt_of_le_of_ne h2 (show 2 * 0 + 1 ≠ 2 * k from Nat.two_mul_ne_two_mul_add_one.symm)))
#align polynomial.gal.gal_action_hom_bijective_of_prime_degree' Polynomial.Gal.galActionHom_bijective_of_prime_degree'

end Rationals

end Polynomial.Gal
