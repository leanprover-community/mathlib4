/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file contains results about nilpotent elements that involve ring theory.
-/

assert_not_exists Cardinal

universe u v

open Function Module Set

variable {R S : Type*} {x y : R}

theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl

theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical := by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp.symm)

theorem isNilpotent_iff_zero_mem_powers [Monoid R] [Zero R] {x : R} :
    IsNilpotent x ↔ 0 ∈ Submonoid.powers x := Iff.rfl

section CommSemiring

variable [CommSemiring R] {x y : R}

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical

theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl

theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
    nilradical R = sInf { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_sInf ⊥).trans <| by simp_rw [and_iff_right bot_le]

theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  rfl

theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H

@[simp]
theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero

theorem nilradical_eq_bot_iff {R : Type*} [CommSemiring R] : nilradical R = ⊥ ↔ IsReduced R := by
  simp_rw [eq_bot_iff, SetLike.le_def, Submodule.mem_bot, mem_nilradical, isReduced_iff]

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn

@[simp]
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn

variable {R}
variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]

@[simp]
lemma isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M →ₗ[R] M) :
    IsNilpotent (toMatrix b b f) ↔ IsNilpotent f := by
  refine exists_congr fun k ↦ ?_
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

end LinearMap

@[simp]
lemma Matrix.isNilpotent_toLin'_iff {ι : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
    (A : Matrix ι ι R) :
    IsNilpotent A.toLin' ↔ IsNilpotent A := by
  have : A.toLin'.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) = A := LinearMap.toMatrix'_toLin' A
  conv_rhs => rw [← this]
  rw [LinearMap.isNilpotent_toMatrix_iff]

namespace Module.End

section

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

lemma isNilpotent_restrict_of_le {f : End R M} {p q : Submodule R M}
    {hp : MapsTo f p p} {hq : MapsTo f q q} (h : p ≤ q) (hf : IsNilpotent (f.restrict hq)) :
    IsNilpotent (f.restrict hp) := by
  obtain ⟨n, hn⟩ := hf
  use n
  ext ⟨x, hx⟩
  replace hn := DFunLike.congr_fun hn ⟨x, h hx⟩
  simp_rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] at hn ⊢
  rw [Module.End.pow_restrict, LinearMap.restrict_apply] at hn ⊢
  ext
  exact (congr_arg Subtype.val hn :)

lemma isNilpotent.restrict
    {f : M →ₗ[R] M} {p : Submodule R M} (hf : MapsTo f p p) (hnil : IsNilpotent f) :
    IsNilpotent (f.restrict hf) := by
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, LinearMap.ext fun m ↦ by simp only [Module.End.pow_restrict n, hn,
    LinearMap.restrict_apply, LinearMap.zero_apply]; rfl⟩

end

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]

end Module.End
