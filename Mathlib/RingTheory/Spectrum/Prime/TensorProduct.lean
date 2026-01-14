/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.SurjectiveOnStalks

/-!

# Lemmas regarding the prime spectrum of tensor products

## Main result
- `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`:
  If `R →+* T` is surjective on stalks (see Mathlib/RingTheory/SurjectiveOnStalks.lean),
  then `Spec(S ⊗[R] T) → Spec S × Spec T` is a topological embedding
  (where `Spec S × Spec T` is the cartesian product with the product topology).
-/

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing T] [Algebra R T]

open TensorProduct Topology

/-- The canonical map from `Spec(S ⊗[R] T)` to the cartesian product `Spec S × Spec T`. -/
noncomputable
def PrimeSpectrum.tensorProductTo (x : PrimeSpectrum (S ⊗[R] T)) :
    PrimeSpectrum S × PrimeSpectrum T :=
  ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩

@[fun_prop]
lemma PrimeSpectrum.continuous_tensorProductTo : Continuous (tensorProductTo R S T) :=
  (comap _).2.prodMk (comap _).2

variable (hRT : (algebraMap R T).SurjectiveOnStalks)
include hRT

lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
    (p₁ p₂ : PrimeSpectrum (S ⊗[R] T))
    (h : tensorProductTo R S T p₁ = tensorProductTo R S T p₂) :
    p₁ ≤ p₂ := by
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intros x hxp₁
  by_contra hxp₂
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul x
    (p₂.asIdeal.comap g) inferInstance
  have h₁ : a ⊗ₜ[R] t ∈ p₁.asIdeal := e ▸ p₁.asIdeal.mul_mem_left (1 ⊗ₜ[R] (r • t)) hxp₁
  have h₂ : a ⊗ₜ[R] t ∉ p₂.asIdeal := e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
  rw [← mul_one a, ← one_mul t, ← Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
  have h₃ : t ∉ p₂.asIdeal.comap g := fun h ↦ h₂ (Ideal.mul_mem_left _ _ h)
  have h₄ : a ∉ p₂.asIdeal.comap (algebraMap S (S ⊗[R] T)) :=
    fun h ↦ h₂ (Ideal.mul_mem_right _ _ h)
  replace h₃ : t ∉ p₁.asIdeal.comap g := by
    rwa [show p₁.asIdeal.comap g = p₂.asIdeal.comap g from congr($h.2.1)]
  replace h₄ : a ∉ p₁.asIdeal.comap (algebraMap S (S ⊗[R] T)) := by
    rwa [show p₁.asIdeal.comap (algebraMap S (S ⊗[R] T)) = p₂.asIdeal.comap _ from congr($h.1.1)]
  exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁

lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks :
    IsEmbedding (tensorProductTo R S T) := by
  refine ⟨?_, fun p₁ p₂ e ↦
    (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
      (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
  rintro _ ⟨f, rfl⟩
  rw [@isOpen_iff_forall_mem_open]
  rintro J (hJ : f ∉ J.asIdeal)
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul f
    (J.asIdeal.comap g) inferInstance
  refine ⟨_, ?_, ⟨_, (basicOpen a).2.prod (basicOpen t).2, rfl⟩, ?_⟩
  · rintro x ⟨hx₁ : a ⊗ₜ[R] (1 : T) ∉ x.asIdeal, hx₂ : (1 : S) ⊗ₜ[R] t ∉ x.asIdeal⟩
      (hx₃ : f ∈ x.asIdeal)
    apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← e]
    exact x.asIdeal.mul_mem_left _ hx₃
  · have : a ⊗ₜ[R] (1 : T) * (1 : S) ⊗ₜ[R] t ∉ J.asIdeal := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← e]
      exact J.asIdeal.primeCompl.mul_mem ht hJ
    rwa [J.isPrime.mul_mem_iff_mem_or_mem.not, not_or] at this
