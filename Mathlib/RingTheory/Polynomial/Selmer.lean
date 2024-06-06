/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Data.Polynomial.UnitTrinomial
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

#align_import ring_theory.polynomial.selmer from "leanprover-community/mathlib"@"3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6"

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/


namespace Polynomial

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [this, pow_zero, pow_one, eq_self_iff_true, or_true_iff, true_or_iff]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, self_eq_add_left] at h1)
  · exact one_ne_zero (by rwa [key, self_eq_add_right] at h1)
  · exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_aux Polynomial.X_pow_sub_X_sub_one_irreducible_aux

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible Polynomial.X_pow_sub_X_sub_one_irreducible

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_rat Polynomial.X_pow_sub_X_sub_one_irreducible_rat

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

instance {α β : Type*} [Monoid α] [Subsingleton β] [MulAction α β] :
    MulAction.IsPretransitive α β :=
  ⟨fun _ _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩

open NumberField

abbrev galoisGroup (K : Type*) [Field K] [Algebra ℚ K] := K ≃ₐ[ℚ] K

def _root_.AlgEquiv.mapRingOfIntegers {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] (σ : K ≃ₐ[F] L) : 𝓞 K ≃ₐ[𝓞 F] 𝓞 L :=
  AlgEquiv.ofRingEquiv (f := (σ.restrictScalars ℤ).mapIntegralClosure.toRingEquiv)
    fun x ↦ Subtype.ext (σ.commutes' x)

def _root_.AlgEquiv.mapRingOfIntegers' {F K : Type*} [Field F] [Field K] [Algebra F K] :
    (K ≃ₐ[F] K) →* (𝓞 K ≃ₐ[𝓞 F] 𝓞 K) :=
  MonoidHom.mk' AlgEquiv.mapRingOfIntegers fun _ _ ↦ rfl

abbrev inertiaSubgroup {K : Type*} [Field K] [Algebra ℚ K] (q : Ideal (𝓞 K)) : Subgroup (galoisGroup K) where
  carrier := {σ : galoisGroup K | ∀ x : (𝓞 K), AlgEquiv.mapRingOfIntegers' σ x - x ∈ q}
  one_mem' := by simp
  inv_mem' := by
    intro σ hσ x
    specialize hσ (AlgEquiv.mapRingOfIntegers' σ⁻¹ x)
    rw [map_inv] at hσ ⊢
    rw [sub_mem_comm_iff]
    convert hσ
    symm
    apply apply_symm_apply
  mul_mem' := by
    intro σ τ hσ hτ x
    specialize hσ (AlgEquiv.mapRingOfIntegers' τ x)
    specialize hτ x
    rw [map_mul, AlgEquiv.mul_apply]
    have key := add_mem hσ hτ
    rwa [sub_add_sub_cancel] at key

theorem keythm {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] :
    ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), inertiaSubgroup q = ⊤ := by
  -- key idea: fixed field of this subgroup has no ramified primes
  let G := K ≃ₐ[ℚ] K
  let H := ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), inertiaSubgroup q
  let F := fixedField H
  change H = ⊤
  suffices h : F = ⊥ by
    rw [← fixingSubgroup_fixedField H]
    change fixingSubgroup F = ⊤
    rw [h]
    -- easy lemma for mathlib
    ext
    simp [IntermediateField.fixingSubgroup, _root_.fixingSubgroup, fixingSubmonoid, mem_bot]

  sorry

#check NumberField.abs_discr_gt_two

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  let f : ℚ[X] := X ^ n - X - 1
  change Function.Bijective (Gal.galActionHom f ℂ)
  have : MulAction.IsPretransitive f.Gal (f.rootSet ℂ) := by
    rcases eq_or_ne n 1 with rfl | hn
    · have : IsEmpty (rootSet f ℂ) := by simp
      infer_instance
    exact Gal.galAction_isPretransitive _ _ (X_pow_sub_X_sub_one_irreducible_rat hn)
  let K := f.SplittingField
  let R := 𝓞 K
  let S0 : Set f.Gal := ⋃ (q : Ideal R) (hq : q.IsMaximal),
    (↑(inertiaSubgroup q : Set (f.SplittingField ≃ₐ[ℚ] f.SplittingField)))
  let S : Set f.Gal := S0 \ {1}
  have hS0 : Subgroup.closure S0 = ⊤ := by
    simp only [Subgroup.closure_iUnion, Subgroup.closure_eq]
    exact keythm
  have hS1 : Subgroup.closure S = ⊤ := by
    have h : Subgroup.closure (S0 ∩ {1}) = ⊥ := by
      rw [eq_bot_iff, ← Subgroup.closure_singleton_one]
      exact Subgroup.closure_mono (Set.inter_subset_right S0 {1})
    rw [← hS0, ← Set.diff_union_inter S0 {1}, Subgroup.closure_union, h, sup_bot_eq]
  have hS2 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom f.Gal (f.rootSet ℂ) σ) := by
    rintro σ ⟨hσ, hσ1 : σ ≠ 1⟩
    rw [Set.mem_iUnion] at hσ
    obtain ⟨q, hσ⟩ := hσ
    rw [Set.mem_iUnion] at hσ
    obtain ⟨hq, hσ : ∀ x : R, σ.mapRingOfIntegers x - x ∈ q⟩ := hσ
    let F := R ⧸ q
    let π : R →+* F := Ideal.Quotient.mk q
    have : Field F := Ideal.Quotient.field q
    -- finite field, might not need to consider the characteristic
    -- reduce to action on roots in R
    sorry
  exact ⟨Gal.galActionHom_injective f ℂ, surjective_of_isSwap_of_isPretransitive S hS2 hS1⟩

  -- have : ∀ p : Nat.Primes, ∀ q : factors (map (algebraMap ℤ R) p)
  -- roots lie in the ring of integers OK
  -- if q is a prime idea of OK, then there is a ring homomorphism to the finite field OK/q
  -- the whole Galois group acts on OK
  -- the decomposition group acts on OK/q
  -- the inertia group acts trivially on OK/q
  --
  -- there are n roots in OK
  -- there are n or n-1 roots in OK/q (possible double root)
  -- Let σ(x) = x (mod p) for all x in OK
  -- If there are n roots in OK/q, then σ must act trivially on the roots in OK
  -- If x and y collapse (mod p), then maybe σ swaps x and y, but no more
  -- Now run through p's and σ's

  -- the key is proving closure/generating
  -- we need to know that if a subgroup contains every σ(x) = x (mod p) for every p, then it's ⊤
  -- we need to know that if a subfield is fixed by ..., then it's ⊥
  -- key facts from algebraic number theory: p divides discriminant implies ramified
  -- ramified means there exists σ(x) = x (mod p)

end Polynomial
