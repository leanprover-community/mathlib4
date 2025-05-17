/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Support

/-!

# Krull Dimension of Module

In this file we define `Module.supportDim R M` for a `R`-module `M` as
the krull dimension of its support. It is equal to the krull dimension of `R / Ann M` when
`M` is finitely generated.

-/

variable (R : Type*) [CommRing R]

variable (M : Type*) [AddCommGroup M] [Module R M] (N : Type*) [AddCommGroup N] [Module R N]

namespace Module

open Order

/-- The krull dimension of module, defined as `krullDim` of its support. -/
noncomputable def supportDim : WithBot ℕ∞ :=
  krullDim (Module.support R M)

lemma supportDim_eq_bot_of_subsingleton [Subsingleton M] : supportDim R M = ⊥ := by
  simpa [supportDim, support_eq_empty_iff]

lemma supportDim_ne_bot_of_nontrivial [Nontrivial M] : supportDim R M ≠ ⊥ := by
  simpa [supportDim, support_eq_empty_iff, not_subsingleton_iff_nontrivial]

lemma supportDim_eq_bot_iff_subsingleton : supportDim R M = ⊥ ↔ Subsingleton M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff]

lemma supportDim_ne_bot_iff_nontrivial : supportDim R M ≠ ⊥ ↔ Nontrivial M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff, not_subsingleton_iff_nontrivial]

lemma supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] :
    supportDim R M = ringKrullDim (R ⧸ annihilator R M) := by
  simp only [supportDim]
  rw [support_eq_zeroLocus, ringKrullDim_quotient]

lemma supportDim_self_eq_ringKrullDim : supportDim R R = ringKrullDim R := by
  have : annihilator R R = ⊥ :=
    annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a ↦ a)
  rw [supportDim_eq_ringKrullDim_quotient_annihilator, this]
  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))

lemma supportDim_quotient_eq_ringKrullDim (I : Ideal R) :
    supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]

lemma supportDim_le_ringKrullDim : supportDim R M ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (fun a ↦ a) fun {_ _} lt ↦ lt

lemma supportDim_le_of_injective (f : M →ₗ[R] N) (h : Function.Injective f) :
    supportDim R M ≤ supportDim R N :=
  krullDim_le_of_strictMono (fun a ↦ ⟨a.1, Module.support_subset_of_injective f h a.2⟩)
    (fun {_ _} lt ↦ lt)

lemma supportDim_le_of_surjective (f : M →ₗ[R] N) (h : Function.Surjective f) :
    supportDim R N ≤ supportDim R M :=
  krullDim_le_of_strictMono (fun a ↦ ⟨a.1, Module.support_subset_of_surjective f h a.2⟩)
    (fun {_ _} lt ↦ lt)

lemma supportDim_eq_of_equiv (e : M ≃ₗ[R] N) :
    supportDim R M = supportDim R N :=
  le_antisymm (supportDim_le_of_injective R M N e e.injective)
    (supportDim_le_of_surjective R M N e e.surjective)

end Module

open Ideal IsLocalRing

lemma IsLocalRing.maximalIdeal_mem_support [IsLocalRing R] [Module.Finite R M] [Nontrivial M] :
    ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ ∈ Module.support R M:= by
  simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  apply IsLocalRing.le_maximalIdeal
  simpa [Module.annihilator_eq_top_iff.not, not_subsingleton_iff_nontrivial]

lemma zeroLocus_eq_singleton (m : Ideal R) [max : m.IsMaximal] :
    PrimeSpectrum.zeroLocus m = {⟨m, IsMaximal.isPrime' m⟩} := by
  ext I
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le max I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]

lemma support_of_dimension_zero [IsLocalRing R] [Module.Finite R N] [Nontrivial N]
    (dim : Module.supportDim R N = 0) :
    Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  rw [zeroLocus_eq_singleton]
  apply le_antisymm
  · intro p hp
    by_contra nmem
    simp at nmem
    have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
    have := IsLocalRing.maximalIdeal_mem_support R N
    have : Module.supportDim R N > 0 := by
      simp [Module.supportDim, Order.krullDim_pos_iff]
      use p
      simp only [hp, true_and]
      use ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩
    exact (ne_of_lt this) dim.symm
  · simpa using IsLocalRing.maximalIdeal_mem_support R N
