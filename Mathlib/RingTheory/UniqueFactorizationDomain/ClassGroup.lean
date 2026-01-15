/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich, Alexei Piskunov, Jonathan Shneyer
-/
module

public import Mathlib.RingTheory.ClassGroup
import Mathlib.Algebra.GCDMonoid.Finset


/-!
# The class group of a Unique Factorization Domain is trivial
This file proves that the ideal class group of a Normalized GCD Domain is trivial.
The main application is to Unique Factorization Domains,
which are known to be Normalized GCD Domains.

## Main result
- `NormalizedGCDMonoid.instSubsingletonClassGroup` : the class group of a
  Normalized GCD Domain is trivial.
- `UniqueFactorizationMonoid.instSubsingletonClassGroup` : the class group of a UFD is trivial.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

open scoped nonZeroDivisors Pointwise BigOperators

open IsLocalization IsFractionRing

section CommRing

variable {R : Type*} [CommRing R]

section Domain
variable [IsDomain R]

/-- Bridge lemma: if `J` is a unit after coercion to fractional ideals, then `J` admits an
integral inverse up to a principal ideal. -/
lemma Ideal.exists_mul_eq_span_singleton_of_isUnit_coe (J : Ideal R)
    (hJ : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ (K : Ideal R) (x : R), x ≠ 0 ∧ J * K = Ideal.span ({x} : Set R) := by
  obtain ⟨a, K, ha0, h⟩ := exists_eq_spanSingleton_mul (J : FractionalIdeal R⁰ (FractionRing R))⁻¹
  refine ⟨K, a, ha0, (coeIdeal_inj (K := FractionRing R)).mp ?_⟩
  rw [coeIdeal_mul, coeIdeal_span_singleton]
  rw [← mul_inv_cancel_iff_isUnit] at hJ
  replace ha0 := spanSingleton_mul_inv (R₁ := R) (FractionRing R)
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.2 ha0))
  replace h := congr(spanSingleton R⁰ ((algebraMap R (FractionRing R)) a) * J * $h.symm)
  rwa [mul_mul_mul_comm, ← spanSingleton_inv, ha0, one_mul, mul_assoc, hJ, mul_one] at h

lemma Ideal.isPrincipal_of_exists_mul_eq_span_singleton [NormalizedGCDMonoid R]
    {J K : Ideal R} {x : R} (hx0 : x ≠ 0) (hJK : J * K = span {x}) :
    J.IsPrincipal := by
  classical
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
  have hK' : K' ≤ span {g} := span_le.mpr fun z hz ↦ mem_span_singleton.mpr (Finset.gcd_dvd hz)
  -- Upgrade to `x ∈ J * (g)`, hence `(x) ≤ J * (g)`.
  have hxJg : x ∈ J * span {g} := mul_mono_right hK' hxT
  -- From `(x) = J * (g)`, extract `y` with `x = y * g` and cancel `(g)` to show `J` is principal.
  suffices J * span {g} = span {x} by
    obtain ⟨y, rfl⟩ := mem_span_singleton'.mp (Ideal.mul_le_left hxJg)
    rw [← span_singleton_mul_span_singleton, span_singleton_mul_left_inj] at this
    · exact ⟨y, this⟩
    · contrapose! hx0
      rw [hx0, mul_zero]
  -- Show `J * (g) ≤ (x)` by proving `x ∣ b * g` for all `b ∈ J`.
  refine le_antisymm (mul_le.mpr fun b hb z hz ↦ ?_) ((span_singleton_le_iff_mem _).mpr hxJg)
  obtain ⟨z, rfl⟩ := mem_span_singleton.mp hz
  rw [mem_span_singleton, ← mul_assoc]
  apply dvd_mul_of_dvd_left
  suffices x ∣ normalize b * g from this.trans ((associated_normalize b).mul_right g).dvd'
  -- Show `x ∣ b * g` by proving `x ∣ b * c` for all `b ∈ J` and `c ∈ T`.
  rw [← Finset.gcd_mul_left, Finset.dvd_gcd_iff]
  intro c hc
  rw [← mem_span_singleton, ← hJK]
  exact mul_mem_mul hb (hTK hc)

/-- In a normalized GCD domain, an integral ideal that is invertible as a fractional ideal
is principal. -/
theorem Ideal.isPrincipal_of_isUnit_fractionalIdeal [NormalizedGCDMonoid R] (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨K, x, hx0, hIK⟩ := Ideal.exists_mul_eq_span_singleton_of_isUnit_coe I hI
  exact Ideal.isPrincipal_of_exists_mul_eq_span_singleton hx0 hIK

@[expose] public section

/-- In a normalized GCD domain, every invertible fractional ideal is principal. -/
theorem FractionalIdeal.isUnit_num {I : FractionalIdeal R⁰ (FractionRing R)} :
    IsUnit (I.num  : FractionalIdeal R⁰ (FractionRing R)) ↔ IsUnit I := by
  have hden0 : algebraMap R (FractionRing R) I.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let u : (FractionRing R)ˣ := Units.mk0 (algebraMap R (FractionRing R) I.den) hden0
  have hdenUnit : IsUnit (spanSingleton R⁰ (algebraMap R (FractionRing R) I.den)) :=
    ⟨toPrincipalIdeal R (FractionRing R) u, by simp [u]⟩
  obtain ⟨c, hc⟩ := hdenUnit
  rw [← den_mul_self_eq_num', ← hc, Units.isUnit_units_mul]

section NormalizedGCDMonoid
variable [NormalizedGCDMonoid R]

/-- In a normalized GCD domain, every invertible fractional ideal is principal. -/
theorem NormalizedGCDMonoid.fractionalIdeal_isPrincipal_of_isUnit
  (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (I : Submodule R (FractionRing R)).IsPrincipal := by
  let J : Ideal R := (I : FractionalIdeal R⁰ (FractionRing R)).num
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) := isUnit_num.mpr ⟨I, rfl⟩
  have hJprin : J.IsPrincipal := ideal_isPrincipal_of_isUnit_fractionalIdeal J hJunit
  exact isPrincipal_of_num_isPrincipal (I : FractionalIdeal R⁰ (FractionRing R)) hJprin

/-- In a normalized GCD Domain, every class in the ideal class group is `1`. -/
theorem NormalizedGCDMonoid.classGroup_eq_one (x : ClassGroup R) : x = 1 :=
  ClassGroup.induction (FractionRing R)
    (fun I ↦ ClassGroup.mk_eq_one_iff.mpr (fractionalIdeal_isPrincipal_of_isUnit I)) x

/-- The ideal class group of a normalized GCD Domain is trivial. -/
instance NormalizedGCDMonoid.instSubsingletonClassGroup : Subsingleton (ClassGroup R) :=
  subsingleton_of_forall_eq 1 NormalizedGCDMonoid.classGroup_eq_one

end NormalizedGCDMonoid
section UFD

variable [UniqueFactorizationMonoid R]

/-- The ideal class group of a UFD is trivial. -/
noncomputable instance UniqueFactorizationMonoid.instSubsingletonClassGroup :
    Subsingleton (ClassGroup R) :=
  letI : NormalizedGCDMonoid R :=
    Classical.choice (inferInstance : Nonempty (NormalizedGCDMonoid R))
  NormalizedGCDMonoid.instSubsingletonClassGroup R

end UFD
end

end Domain
end CommRing
