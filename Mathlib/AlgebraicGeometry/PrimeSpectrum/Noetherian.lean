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
  refine' IsNoetherian.induction
    (P := fun I => ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I)
    (fun (M : Ideal R) hgt => _) I
  by_cases h_prM : M.IsPrime
  -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) M
  · use {⟨M, h_prM⟩}
    -- ⊢ Multiset.prod (Multiset.map asIdeal {{ asIdeal := M, IsPrime := h_prM }}) ≤ M
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    -- 🎉 no goals
  by_cases htop : M = ⊤
  -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) M
  · rw [htop]
    -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) ⊤
    exact ⟨0, le_top⟩
    -- 🎉 no goals
  have lt_add : ∀ (z) (_ : z ∉ M), M < M + span R {z} := by
    intro z hz
    refine' lt_of_le_of_ne le_sup_left fun m_eq => hz _
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left htop
  -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) M
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) M
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  -- ⊢ (fun I => ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I) M
  use Wx + Wy
  -- ⊢ Multiset.prod (Multiset.map asIdeal (Wx + Wy)) ≤ M
  rw [Multiset.map_add, Multiset.prod_add]
  -- ⊢ Multiset.prod (Multiset.map asIdeal Wx) * Multiset.prod (Multiset.map asIdea …
  apply le_trans (Submodule.mul_le_mul h_Wx h_Wy)
  -- ⊢ (M + span R {x}) * (M + span R {y}) ≤ M
  rw [add_mul]
  -- ⊢ M * (M + span R {y}) + span R {x} * (M + span R {y}) ≤ M
  apply sup_le (show M * (M + span R {y}) ≤ M from Ideal.mul_le_right)
  -- ⊢ span R {x} * (M + span R {y}) ≤ M
  rw [mul_add]
  -- ⊢ span R {x} * M + span R {x} * span R {y} ≤ M
  apply sup_le (show span R {x} * M ≤ M from Ideal.mul_le_left)
  -- ⊢ span R {x} * span R {y} ≤ M
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  -- 🎉 no goals
#align prime_spectrum.exists_prime_spectrum_prod_le PrimeSpectrum.exists_primeSpectrum_prod_le

/-- In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3]) -/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥ := by
  revert h_nzI
  -- ⊢ I ≠ ⊥ → ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ I ∧ Multiset.prod (Mul …
  -- Porting note: Need to specify `P` explicitly
  refine' IsNoetherian.induction (P := fun I => I ≠ ⊥ → ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥)
    (fun (M : Ideal A) hgt => _) I
  intro h_nzM
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  have hA_nont : Nontrivial A
  -- ⊢ Nontrivial A
  apply IsDomain.toNontrivial
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  by_cases h_topM : M = ⊤
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  · rcases h_topM with rfl
    -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ ⊤ ∧ Multiset.prod (Multiset.ma …
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime := by
      apply Ring.not_isField_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    -- ⊢ Multiset.prod (Multiset.map asIdeal {{ asIdeal := p_id, IsPrime := h_pp }})  …
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
    -- 🎉 no goals
  by_cases h_prM : M.IsPrime
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    -- ⊢ Multiset.prod (Multiset.map asIdeal {{ asIdeal := M, IsPrime := h_prM }}) ≤  …
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    -- ⊢ { asIdeal := M, IsPrime := h_prM }.asIdeal ≤ M ∧ { asIdeal := M, IsPrime :=  …
    exact ⟨le_rfl, h_nzM⟩
    -- 🎉 no goals
  obtain ⟨x, hx, y, hy, h_xy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left h_topM
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  have lt_add : ∀ (z) (_ : z ∉ M), M < M + span A {z} := by
    intro z hz
    refine' lt_of_le_of_ne le_sup_left fun m_eq => hz _
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  -- ⊢ ∃ Z, Multiset.prod (Multiset.map asIdeal Z) ≤ M ∧ Multiset.prod (Multiset.ma …
  use Wx + Wy
  -- ⊢ Multiset.prod (Multiset.map asIdeal (Wx + Wy)) ≤ M ∧ Multiset.prod (Multiset …
  rw [Multiset.map_add, Multiset.prod_add]
  -- ⊢ Multiset.prod (Multiset.map asIdeal Wx) * Multiset.prod (Multiset.map asIdea …
  refine' ⟨le_trans (Submodule.mul_le_mul h_Wx_le h_Wy_le) _, mt Ideal.mul_eq_bot.mp _⟩
  -- ⊢ (M + span A {x}) * (M + span A {y}) ≤ M
  · rw [add_mul]
    -- ⊢ M * (M + span A {y}) + span A {x} * (M + span A {y}) ≤ M
    apply sup_le (show M * (M + span A {y}) ≤ M from Ideal.mul_le_right)
    -- ⊢ span A {x} * (M + span A {y}) ≤ M
    rw [mul_add]
    -- ⊢ span A {x} * M + span A {x} * span A {y} ≤ M
    apply sup_le (show span A {x} * M ≤ M from Ideal.mul_le_left)
    -- ⊢ span A {x} * span A {y} ≤ M
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
    -- 🎉 no goals
  · rintro (hx | hy) <;> contradiction
    -- ⊢ False
                         -- 🎉 no goals
                         -- 🎉 no goals
#align prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain

open TopologicalSpace

instance : NoetherianSpace (PrimeSpectrum R) := by
  apply ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr
  -- ⊢ WellFounded fun s t => s < t
  have H := ‹IsNoetherianRing R›
  -- ⊢ WellFounded fun s t => s < t
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H
  -- ⊢ WellFounded fun s t => s < t
  exact (closedsEmbedding R).dual.wellFounded H
  -- 🎉 no goals

end PrimeSpectrum
