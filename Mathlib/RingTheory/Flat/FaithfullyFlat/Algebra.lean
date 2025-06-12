/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Properties of faithfully flat algebras

An `A`-algebra `B` is faithfully flat if `B` is faithfully flat as an `A`-module. In this
file we give equivalent characterizations of faithful flatness in the algebra case.

## Main results

Let `B` be a faithfully flat `A`-algebra:

- `Ideal.comap_map_eq_self_of_faithfullyFlat`: the contraction of the extension of any ideal of
  `A` to `B` is the ideal itself.
- `Module.FaithfullyFlat.tensorProduct_mk_injective`: The natural map `M →ₗ[A] B ⊗[A] M` is
  injective for any `A`-module `M`.
- `PrimeSpectrum.specComap_surjective_of_faithfullyFlat`: The map on prime spectra induced by
  a faithfully flat ring map is surjective. See also
  `Ideal.exists_isPrime_liesOver_of_faithfullyFlat` for a version stated in terms of
  `Ideal.LiesOver`.

Conversely, let `B` be a flat `A`-algebra:

- `Module.FaithfullyFlat.of_specComap_surjective`: `B` is faithfully flat over `A`,
  if the induced map on prime spectra is surjective.
- `Module.FaithfullyFlat.of_flat_of_isLocalHom`: flat + local implies faithfully flat

-/

universe u v

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

open TensorProduct LinearMap

/-- If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `A`-algebra. -/
lemma Module.FaithfullyFlat.of_specComap_surjective [Flat A B]
    (h : Function.Surjective ((algebraMap A B).specComap)) :
    Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.specComap_asIdeal (algebraMap A B) m', hm']
  rw [Ideal.smul_top_eq_map, this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    fun top ↦ m'.isPrime.ne_top <| top_le_iff.mp <| top ▸ Ideal.map_comap_le

/-- If `A` is local and `B` is a local and flat `A`-algebra, then `B` is faithfully flat. -/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≤
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 2).mp ‹_›
  rw [eqt, top_le_iff, Submodule.restrictScalars_eq_top_iff] at this
  exact Ideal.IsPrime.ne_top' this

variable [Module.FaithfullyFlat A B]

/-- If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective. -/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B ⊗[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
  exact Algebra.TensorProduct.mk_one_injective_of_isScalarTower _

open Algebra.TensorProduct in
/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp]
    exact (AlgEquiv.injective _).comp <|
      Module.FaithfullyFlat.tensorProduct_mk_injective (A ⧸ I)
  intro x hx
  rw [Ideal.mem_comap] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply inj
  have : ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
      TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
    simp [← Algebra.algebraMap_eq_smul_one, hx]
  simp [this]

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
lemma Ideal.comap_surjective_of_faithfullyFlat :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I ↦ ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/-- If `B` is faithfully flat over `A`, every prime of `A` comes from a prime of `B`. -/
lemma Ideal.exists_isPrime_liesOver_of_faithfullyFlat (p : Ideal A) [p.IsPrime] :
    ∃ (P : Ideal B), P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, _, hP⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).mp <|
    p.comap_map_eq_self_of_faithfullyFlat (B := B)
  exact ⟨P, inferInstance, ⟨hP.symm⟩⟩

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
lemma PrimeSpectrum.specComap_surjective_of_faithfullyFlat :
    Function.Surjective (algebraMap A B).specComap := fun I ↦
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr
    I.asIdeal.comap_map_eq_self_of_faithfullyFlat
