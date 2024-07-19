/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/


open scoped Classical
open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)
variable [Algebra R A]

theorem RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩

theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

end Ring

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  obtain ⟨P, hP⟩ := hb
  refine ⟨P, hP.1, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap A,
    aeval_algHom_apply, aeval_map_algebraMap, aeval_def, hP.2, _root_.map_zero]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (f : A →ₐ[R] B) (hf : Function.Injective f)

theorem isIntegral_algHom_iff {x : A} : IsIntegral R (f x) ↔ IsIntegral R x := by
  refine ⟨fun ⟨p, hp, hx⟩ ↦ ⟨p, hp, ?_⟩, IsIntegral.map f⟩
  rwa [← f.comp_algebraMap, ← AlgHom.coe_toRingHom, ← hom_eval₂, AlgHom.coe_toRingHom,
    map_eq_zero_iff f hf] at hx

end

theorem Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A]
    {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree f))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality A
  have hf1 : f ≠ 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs ↦ ?_).antisymm fun r hr ↦ ?_
  · rcases Finset.mem_image.1 hs with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p hf, map_add, map_mul, hfx,
      zero_mul, add_zero, ← sum_C_mul_X_pow_eq (p %ₘ f), aeval_def, eval₂_sum, sum_def]
  refine sum_mem fun k hkq ↦ ?_
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial, ← Algebra.smul_def]
  exact smul_mem _ _ (subset_span <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <|
    (le_natDegree_of_mem_supp _ hkq).trans_lt <| natDegree_modByMonic_lt p hf hf1)

theorem IsIntegral.fg_adjoin_singleton {x : B} (hx : IsIntegral R x) :
    (Algebra.adjoin R {x}).toSubmodule.FG := by
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

variable (f : R →+* B)

theorem RingHom.isIntegralElem_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.isIntegralElem_map

theorem isIntegral_zero : IsIntegral R (0 : B) :=
  (algebraMap R B).isIntegralElem_zero

theorem RingHom.isIntegralElem_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.isIntegralElem_map

theorem isIntegral_one : IsIntegral R (1 : B) :=
  (algebraMap R B).isIntegralElem_one

variable (f : R →+* S)

theorem IsIntegral.of_pow {x : B} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x := by
  rcases hx with ⟨p, hmonic, heval⟩
  exact ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

end
