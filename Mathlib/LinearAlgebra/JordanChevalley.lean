/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Squarefree.UniqueFactorizationDomain
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Semisimple

/-!
# Jordan-Chevalley-Dunford decomposition

TODO explain

## Main definitions / results:

 * `Module.End.exists_isNilpotent_isSemisimple`: an endomorphism of a finite-dimensional vector
   space over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms.

-/

open Polynomial

section FindHome -- Tidy up + move the lemmas in this section, and then remove it from this file.

@[simp]
lemma Algebra.aeval_mem_adjoin_singleton {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (p : R[X]) (a : A) :
    aeval a p ∈ Algebra.adjoin R {a} := by
  simpa only [Algebra.adjoin_singleton_eq_range_aeval] using Set.mem_range_self p

lemma Polynomial.coe_aeval_mk_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {S : Subalgebra R A} {a : A} (ha : a ∈ S) (p : R[X]) :
    (aeval (⟨a, ha⟩ : S) p : A) = aeval a p :=
  (aeval_algHom_apply S.val (⟨a, ha⟩ : S) p).symm

lemma Polynomial.aeval_mem_foo {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {S : Subalgebra R A} {a : A} (ha : a ∈ S) (p : R[X]) :
    aeval a p ∈ S := by
  change aeval (S.val (⟨a, ha⟩ : S)) p ∈ S
  rw [aeval_algHom_apply]
  simp only [Subalgebra.coe_val, SetLike.coe_mem]

@[simp]
lemma Polynomial.aeval_mk_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {S : Subalgebra R A} {a : A} (ha : a ∈ S) (p : R[X]) (h' := aeval_mem_foo ha p) :
    aeval (⟨a, ha⟩ : S) p = ⟨aeval a p, h'⟩ := by
  rw [Subtype.ext_iff]
  exact (aeval_algHom_apply S.val (⟨a, ha⟩ : S) p).symm

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (a : A) :
    CommRing <| Algebra.adjoin R {a} :=
  { mul_comm := by
      intro ⟨p, hp⟩ ⟨q, hq⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval R a] at hp hq
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Submonoid.mk_mul_mk, Subtype.mk.injEq,
        ← AlgHom.map_mul, mul_comm p' q'] }

end FindHome

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : End K V}

-- TODO Upgrade to include uniqueness using `Module.End.eq_zero_of_isNilpotent_isSemisimple`
theorem exists_isNilpotent_isSemisimple_of_dvd_pow_separable
    {g : K[X]} {n : ℕ} (hg₀ : minpoly K f ∣ g ^ n) (hg₁ : g.Separable) :
    ∃ s ∈ Algebra.adjoin K {f}, IsNilpotent (f - s) ∧ s.IsSemisimple := by
  have key₁ : IsNilpotent (aeval
      (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}) g) := by
    use n
    obtain ⟨q, hq⟩ := hg₀
    rw [← AlgHom.map_pow, hq, aeval_mk_apply]
    simp only [map_mul, minpoly.aeval, zero_mul]
    rfl
  have key₂ : IsUnit (aeval
      (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}) (derivative g)) := by
    obtain ⟨a, b, h⟩ : IsCoprime (g ^ n) (derivative g) := hg₁.pow_left
    set f' : Algebra.adjoin K {f} := ⟨f, Algebra.self_mem_adjoin_singleton K f⟩
    apply isUnit_of_mul_eq_one' (aeval f' b)
    replace h : (aeval f b) * (aeval f (derivative g)) = 1 := by
      simpa only [map_add, map_mul, map_one, minpoly.dvd_iff.mp hg₀, mul_zero, zero_add]
        using (aeval f).congr_arg h
    rw [Subtype.ext_iff]
    simpa [coe_aeval_mk_apply] using h
  obtain ⟨⟨b, h₁⟩, ⟨⟨n, h₂⟩, h₃⟩, _⟩ := exists_unique_nilpotent_sub_and_aeval_eq_zero key₁ key₂
  refine ⟨b, ⟨h₁, ⟨n, ?_⟩, ?_⟩⟩
  · rw [Subtype.ext_iff] at h₂
    simpa using h₂
  · replace h₃ : aeval b g = 0 := by rwa [Subtype.ext_iff, coe_aeval_mk_apply] at h₃
    exact isSemisimple_of_squarefree_aeval_eq_zero hg₁.squarefree h₃

/-- **Jordan-Chevalley-Dunford decomposition**: an endomorphism of a finite-dimensional vector space
over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms.

TODO Upgrade to include uniqueness -/
theorem exists_isNilpotent_isSemisimple [PerfectField K] :
    ∃ s ∈ Algebra.adjoin K {f}, IsNilpotent (f - s) ∧ s.IsSemisimple := by
  obtain ⟨g, n, hg₁, -, hg₀⟩ := exists_squarefree_dvd_pow_of_ne_zero (minpoly.ne_zero_of_finite K f)
  rw [← PerfectField.separable_iff_squarefree] at hg₁
  exact exists_isNilpotent_isSemisimple_of_dvd_pow_separable hg₀ hg₁

end Module.End
