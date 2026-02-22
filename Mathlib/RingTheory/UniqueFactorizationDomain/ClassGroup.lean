/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich, Alexei Piskunov, Jonathan Shneyer
-/
module

public import Mathlib.RingTheory.ClassGroup

/-!
# The class group of a Unique Factorization Domain is trivial
This file proves that the ideal class group of a Normalized GCD Domain is trivial.
The main application is to Unique Factorization Domains,
which are known to be Normalized GCD Domains.

## Main result
- `NormalizedGCDMonoid.subsingleton_classGroup` : the class group of a domain with
normalizable gcd is trivial. This includes unique factorization domains.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

open scoped nonZeroDivisors

open FractionalIdeal Ideal

@[expose] public section

variable {R : Type*} [CommRing R] [IsDomain R] [Nonempty (NormalizedGCDMonoid R)]
namespace NormalizedGCDMonoid

lemma isPrincipal_of_exists_mul_ne_zero_isPrincipal
    {J : Ideal R} (hJ : ∃ K : Ideal R, J * K ≠ 0 ∧ (J * K).IsPrincipal) :
    J.IsPrincipal := by
  letI : NormalizedGCDMonoid R :=
    Classical.choice (inferInstance : Nonempty (NormalizedGCDMonoid R))
  obtain ⟨K, hJK0, hK⟩ := hJ
  rcases hK.principal with ⟨x, hJK⟩
  have hxmemJK : x ∈ J * K := by simp [hJK, mem_span_singleton_self]
  -- Shrink `K` to a finitely generated subideal `K'` witnessing `x ∈ J * K'`.
  have : ∃ T : Finset R, (T : Set R) ⊆ K ∧ x ∈ J * span T := by
    obtain ⟨S, T, hSJ, hTK, hx⟩ := Submodule.mem_span_mul_finite_of_mem_mul hxmemJK
    refine ⟨T, hTK, ?_⟩
    rw [← J.span_eq, span_mul_span]
    exact span_mono (Set.mul_subset_mul_right hSJ) hx
  obtain ⟨T, hTK, hxT⟩ := this
  set K' : Ideal R := span T
  -- Let `g` be the gcd of the chosen generators of `K'`; then `K' ≤ (g)`.
  let g : R := T.gcd id
  have hK' : K' ≤ span {g} :=
    span_le.mpr fun z hz ↦ mem_span_singleton.mpr (Finset.gcd_dvd hz)
  -- Upgrade to `x ∈ J * (g)`, hence `(x) ≤ J * (g)`.
  have hxJg : x ∈ J * span {g} := mul_mono_right hK' hxT
  have hx0 : x ≠ 0 := by
    intro hx
    apply hJK0
    simpa [hJK]
  -- From `(x) = J * (g)`, extract `y` with `x = y * g` and cancel `(g)` to show `J` is principal.
  suffices J * span {g} = span {x} by
    obtain ⟨y, hyJ, rfl⟩ := (Ideal.mem_mul_span_singleton).1 hxJg
    rw [← span_singleton_mul_span_singleton, span_singleton_mul_left_inj] at this
    · exact ⟨y, this⟩
    · contrapose! hx0
      rw [hx0, mul_zero]
  -- Show `J * (g) ≤ (x)` by proving `x ∣ b * g` for all `b ∈ J`.
  refine le_antisymm
      (mul_le.mpr fun b hb z hz ↦ ?_)
      ((span_singleton_le_iff_mem _).mpr hxJg)
  obtain ⟨z, rfl⟩ := mem_span_singleton.mp hz
  rw [mem_span_singleton, ← mul_assoc]
  apply dvd_mul_of_dvd_left
  suffices x ∣ normalize b * g from this.trans ((associated_normalize b).mul_right g).dvd'
  -- Show `x ∣ b * g` by proving `x ∣ b * c` for all `b ∈ J` and `c ∈ T`.
  rw [← Finset.gcd_mul_left, Finset.dvd_gcd_iff]
  intro c hc
  rw [← mem_span_singleton, span, ← hJK]
  exact mul_mem_mul hb (hTK hc)

/-- In a normalized GCD domain, an integral ideal that is invertible as a fractional ideal
is principal.

Public API note: see `ClassGroup.isPrincipal_of_isUnit_coeIdeal`. -/
private theorem isPrincipal_of_isUnit_fractionalIdeal (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨a, K, ha0, h⟩ := exists_eq_spanSingleton_mul (I : FractionalIdeal R⁰ (FractionRing R))⁻¹
  have hIK : I * K = Ideal.span ({a} : Set R) :=
    (coeIdeal_inj (K := FractionRing R)).mp <| by
      rw [coeIdeal_mul, coeIdeal_span_singleton]
      rw [← mul_inv_cancel_iff_isUnit] at hI
      have ha0' := spanSingleton_mul_inv (R₁ := R) (FractionRing R)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr ha0))
      replace h :=
        congrArg
          (fun t =>
            spanSingleton R⁰ ((algebraMap R (FractionRing R)) a) * I * t)
          h.symm
      dsimp only at h
      rwa [mul_mul_mul_comm, ← spanSingleton_inv, ha0', one_mul, mul_assoc, hI, mul_one] at h
  refine isPrincipal_of_exists_mul_ne_zero_isPrincipal (J := I) ?_
  refine ⟨K, ?_, ?_⟩
  · simp [hIK, ha0]
  · simpa [hIK] using (inferInstance : (Ideal.span {a}).IsPrincipal)

/-- In a normalized GCD domain, every invertible fractional ideal is principal.

Public API note: see `ClassGroup.isPrincipal_coeSubmodule_of_isUnit`. -/
private theorem isPrincipal_fractionalIdeal_of_isUnit
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (I : Submodule R (FractionRing R)).IsPrincipal := by
  let J : Ideal R := (I : FractionalIdeal R⁰ (FractionRing R)).num
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) :=
    FractionalIdeal.isUnit_num.mpr ⟨I, rfl⟩
  have hJprin : J.IsPrincipal := isPrincipal_of_isUnit_fractionalIdeal J hJunit
  exact isPrincipal_of_isPrincipal_num
    (I : FractionalIdeal R⁰ (FractionRing R)) hJprin

/-- The ideal class group of a domain with normalizable gcd is trivial.
This includes unique factorization domains. -/
instance subsingleton_classGroup : Subsingleton (ClassGroup R) := by
  refine subsingleton_of_forall_eq 1 ?_
  intro x
  refine ClassGroup.induction (FractionRing R) ?_ x
  intro I
  exact ClassGroup.mk_eq_one_iff.mpr
    (isPrincipal_fractionalIdeal_of_isUnit I)


end NormalizedGCDMonoid
