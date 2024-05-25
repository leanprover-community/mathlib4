/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Topology.NoetherianSpace

#align_import algebraic_geometry.prime_spectrum.noetherian from "leanprover-community/mathlib"@"052f6013363326d50cb99c6939814a4b8eb7b301"

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/


universe u v

namespace PrimeSpectrum

open Submodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/
theorem exists_primeSpectrum_prod_le (I : Ideal R) :
    ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I := by
  -- Porting note: Need to specify `P` explicitly
  refine IsNoetherian.induction
    (P := fun I => ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I)
    (fun (M : Ideal R) hgt => ?_) I
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : ∀ z ∉ M, M < M + span R {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left htop
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  apply le_trans (Submodule.mul_le_mul h_Wx h_Wy)
  rw [add_mul]
  apply sup_le (show M * (M + span R {y}) ≤ M from Ideal.mul_le_right)
  rw [mul_add]
  apply sup_le (show span R {x} * M ≤ M from Ideal.mul_le_left)
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
#align prime_spectrum.exists_prime_spectrum_prod_le PrimeSpectrum.exists_primeSpectrum_prod_le

/-- In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3]) -/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥ := by
  revert h_nzI
  -- Porting note: Need to specify `P` explicitly
  refine IsNoetherian.induction (P := fun I => I ≠ ⊥ → ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥)
    (fun (M : Ideal A) hgt => ?_) I
  intro h_nzM
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime := by
      apply Ring.not_isField_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h_prM : M.IsPrime
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    exact ⟨le_rfl, h_nzM⟩
  obtain ⟨x, hx, y, hy, h_xy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left h_topM
  have lt_add : ∀ z ∉ M, M < M + span A {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  refine ⟨le_trans (Submodule.mul_le_mul h_Wx_le h_Wy_le) ?_, mt Ideal.mul_eq_bot.mp ?_⟩
  · rw [add_mul]
    apply sup_le (show M * (M + span A {y}) ≤ M from Ideal.mul_le_right)
    rw [mul_add]
    apply sup_le (show span A {x} * M ≤ M from Ideal.mul_le_left)
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  · rintro (hx | hy) <;> contradiction
#align prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain

open TopologicalSpace

instance : NoetherianSpace (PrimeSpectrum R) := by
  apply ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr
  have H := ‹IsNoetherianRing R›
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H
  exact (closedsEmbedding R).dual.wellFounded H

lemma _root_.minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite :=
  minimalPrimes.equivIrreducibleComponents R
    |>.set_finite_iff
    |>.mpr NoetherianSpace.finite_irreducibleComponents

end PrimeSpectrum
