/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType

#align_import ring_theory.rees_algebra from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Rees algebra

The Rees algebra of an ideal `I` is the subalgebra `R[It]` of `R[t]` defined as `R[It] = ⨁ₙ Iⁿ tⁿ`.
This is used to prove the Artin-Rees lemma, and will potentially enable us to calculate some
blowup in the future.

## Main definition

- `reesAlgebra` : The Rees algebra of an ideal `I`, defined as a subalgebra of `R[X]`.
- `adjoin_monomial_eq_reesAlgebra` : The Rees algebra is generated by the degree one elements.
- `reesAlgebra.fg` : The Rees algebra of a f.g. ideal is of finite type. In particular, this
implies that the rees algebra over a noetherian ring is still noetherian.

-/


universe u v

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

open Polynomial

open Polynomial BigOperators

/-- The Rees algebra of an ideal `I`, defined as the subalgebra of `R[X]` whose `i`-th coefficient
falls in `I ^ i`. -/
def reesAlgebra : Subalgebra R R[X] where
  carrier := { f | ∀ i, f.coeff i ∈ I ^ i }
  mul_mem' hf hg i := by
    rw [coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    rw [← Finset.Nat.mem_antidiagonal.mp e, pow_add]
    exact Ideal.mul_mem_mul (hf j) (hg k)
  one_mem' i := by
    rw [coeff_one]
    split_ifs with h
    · subst h
      simp
    · simp
  add_mem' hf hg i := by
    rw [coeff_add]
    exact Ideal.add_mem _ (hf i) (hg i)
  zero_mem' i := Ideal.zero_mem _
  algebraMap_mem' r i := by
    rw [algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
#align rees_algebra reesAlgebra

theorem mem_reesAlgebra_iff (f : R[X]) : f ∈ reesAlgebra I ↔ ∀ i, f.coeff i ∈ I ^ i :=
  Iff.rfl
#align mem_rees_algebra_iff mem_reesAlgebra_iff

theorem mem_reesAlgebra_iff_support (f : R[X]) :
    f ∈ reesAlgebra I ↔ ∀ i ∈ f.support, f.coeff i ∈ I ^ i := by
  apply forall_congr'
  intro a
  rw [mem_support_iff, Iff.comm, imp_iff_right_iff, Ne.def, ← imp_iff_not_or]
  exact fun e => e.symm ▸ (I ^ a).zero_mem
#align mem_rees_algebra_iff_support mem_reesAlgebra_iff_support

theorem reesAlgebra.monomial_mem {I : Ideal R} {i : ℕ} {r : R} :
    monomial i r ∈ reesAlgebra I ↔ r ∈ I ^ i := by
  simp (config := { contextual := true }) [mem_reesAlgebra_iff_support, coeff_monomial, ←
    imp_iff_not_or]
#align rees_algebra.monomial_mem reesAlgebra.monomial_mem

theorem monomial_mem_adjoin_monomial {I : Ideal R} {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    monomial n r ∈ Algebra.adjoin R (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
  induction' n with n hn generalizing r
  · exact Subalgebra.algebraMap_mem _ _
  · rw [pow_succ] at hr
    apply Submodule.smul_induction_on
      -- Porting note: did not need help with motive previously
      (p := fun r => (monomial (Nat.succ n)) r ∈ Algebra.adjoin R (Submodule.map (monomial 1) I)) hr
    · intro r hr s hs
      rw [Nat.succ_eq_one_add, smul_eq_mul, ← monomial_mul_monomial]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_image_of_mem _ hr)) (hn hs)
    · intro x y hx hy
      rw [monomial_add]
      exact Subalgebra.add_mem _ hx hy
#align monomial_mem_adjoin_monomial monomial_mem_adjoin_monomial

theorem adjoin_monomial_eq_reesAlgebra :
    Algebra.adjoin R (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) = reesAlgebra I := by
  apply le_antisymm
  · apply Algebra.adjoin_le _
    rintro _ ⟨r, hr, rfl⟩
    exact reesAlgebra.monomial_mem.mpr (by rwa [pow_one])
  · intro p hp
    rw [p.as_sum_support]
    apply Subalgebra.sum_mem _ _
    rintro i -
    exact monomial_mem_adjoin_monomial (hp i)
#align adjoin_monomial_eq_rees_algebra adjoin_monomial_eq_reesAlgebra

variable {I}

theorem reesAlgebra.fg (hI : I.FG) : (reesAlgebra I).FG := by
  classical
    obtain ⟨s, hs⟩ := hI
    rw [← adjoin_monomial_eq_reesAlgebra, ← hs]
    use s.image (monomial 1)
    rw [Finset.coe_image]
    change
      _ =
        Algebra.adjoin R
          (Submodule.map (monomial 1 : R →ₗ[R] R[X]) (Submodule.span R ↑s) : Set R[X])
    rw [Submodule.map_span, Algebra.adjoin_span]
#align rees_algebra.fg reesAlgebra.fg

instance [IsNoetherianRing R] : Algebra.FiniteType R (reesAlgebra I) :=
  ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg <| IsNoetherian.noetherian I)⟩

instance [IsNoetherianRing R] : IsNoetherianRing (reesAlgebra I) :=
  Algebra.FiniteType.isNoetherianRing R _
