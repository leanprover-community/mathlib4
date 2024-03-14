/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.PID
import Mathlib.Data.Polynomial.Module.FiniteDimensional
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.CompleteSublattice
import Mathlib.RingTheory.Nilpotent
import Mathlib.RingTheory.SimpleModule

/-!
# Semisimple linear endomorphisms

Given an `R`-module `M` together with an `R`-linear endomorphism `f : M → M`, the following two
conditions are equivalent:
 1. Every `f`-invariant submodule of `M` has an `f`-invariant complement.
 2. `M` is a semisimple `R[X]`-module, where the action of the polynomial ring is induced by `f`.

A linear endomorphism `f` satisfying these equivalent conditions is known as a *semisimple*
endomorphism. We provide basic definitions and results about such endomorphisms in this file.

## Main definitions / results:
 * `Module.End.IsSemisimple`: the definition that a linear endomorphism is semisimple
 * `Module.End.isSemisimple_iff`: the characterisation of semisimplicity in terms of invariant
   submodules.
 * `Module.End.eq_zero_of_isNilpotent_isSemisimple`: the zero endomorphism is the only endomorphism
   that is both nilpotent and semisimple.
 * `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`: an endomorphism that is a root of a
   square-free polynomial is semisimple (in finite dimensions over a field).

## TODO

In finite dimensions over a field:
 * Sum / difference / product of commuting semisimple endomorphisms is semisimple
 * If semisimple then generalized eigenspace is eigenspace
 * Converse of `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
 * Restriction of semisimple endomorphism is semisimple
 * Triangularizable iff diagonalisable for semisimple endomorphisms

-/

open Set Function Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

section CommRing

variable (f g : End R M)

/-- A linear endomorphism of an `R`-module `M` is called *semisimple* if the induced `R[X]`-module
structure on `M` is semisimple. This is equivalent to saying that every `f`-invariant `R`-submodule
of `M` has an `f`-invariant complement: see `Module.End.isSemisimple_iff`. -/
abbrev IsSemisimple := IsSemisimpleModule R[X] (AEval' f)

variable {f g}

lemma isSemisimple_iff :
    f.IsSemisimple ↔ ∀ p : Submodule R M, p ≤ p.comap f → ∃ q, q ≤ q.comap f ∧ IsCompl p q := by
  set s := (AEval.comapSubmodule R M f).range
  have h : s = {p : Submodule R M | p ≤ p.comap f} := AEval.range_comapSubmodule R M f
  let e := CompleteLatticeHom.toOrderIsoRangeOfInjective _ (AEval.injective_comapSubmodule R M f)
  simp_rw [Module.End.IsSemisimple, IsSemisimpleModule, e.complementedLattice_iff,
    s.isComplemented_iff, ← SetLike.mem_coe, h, mem_setOf_eq]

@[simp]
lemma isSemisimple_zero [IsSemisimpleModule R M] : IsSemisimple (0 : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl

@[simp]
lemma isSemisimple_id [IsSemisimpleModule R M] : IsSemisimple (LinearMap.id : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl

@[simp] lemma isSemisimple_neg : (-f).IsSemisimple ↔ f.IsSemisimple := by simp [isSemisimple_iff]

lemma eq_zero_of_isNilpotent_isSemisimple (hn : IsNilpotent f) (hs : f.IsSemisimple) : f = 0 := by
  nontriviality M
  set k := nilpotencyClass f
  wlog hk : 2 ≤ k
  · replace hk : k = 0 ∨ k = 1 := by omega
    rcases hk with (hk₀ : nilpotencyClass f = 0) | (hk₁ : nilpotencyClass f = 1)
    · rw [← pos_nilpotencyClass_iff, hk₀] at hn; contradiction
    · exact eq_zero_of_nilpotencyClass_eq_one hk₁
  let p := LinearMap.ker (f ^ (k - 1))
  have hp : p ≤ p.comap f := fun x hx ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ← LinearMap.mul_apply, ← pow_succ', add_comm,
      pow_add, pow_one, LinearMap.mul_apply, hx, map_zero]
  obtain ⟨q, hq₀, hq₁, hq₂⟩ := isSemisimple_iff.mp hs p hp
  replace hq₂ : q ≠ ⊥ := hq₂.ne_bot_of_ne_top <|
    fun contra ↦ pow_pred_nilpotencyClass hn <| LinearMap.ker_eq_top.mp contra
  obtain ⟨m, hm₁ : m ∈ q, hm₀ : m ≠ 0⟩ := q.ne_bot_iff.mp hq₂
  suffices m ∈ p by
    exfalso
    apply hm₀
    rw [← Submodule.mem_bot (R := R), ← hq₁.eq_bot]
    exact ⟨this, hm₁⟩
  replace hm₁ : f m = 0 := by
    rw [← Submodule.mem_bot (R := R), ← hq₁.eq_bot]
    refine ⟨(?_ : f m ∈ p), hq₀ hm₁⟩
    rw [LinearMap.mem_ker, ← LinearMap.mul_apply, ← pow_succ', (by omega : k - 1 + 1 = k),
      pow_nilpotencyClass hn, LinearMap.zero_apply]
  rw [LinearMap.mem_ker]
  exact LinearMap.pow_map_zero_of_le (by omega : 1 ≤ k - 1) hm₁

end CommRing

section field

variable {K : Type*} [Field K] [Module K M] {f : End K M}

lemma IsSemisimple_smul_iff {t : K} (ht : t ≠ 0) :
    (t • f).IsSemisimple ↔ f.IsSemisimple := by
  simp [isSemisimple_iff, Submodule.comap_smul f (h := ht)]

lemma IsSemisimple_smul (t : K) (h : f.IsSemisimple) :
    (t • f).IsSemisimple := by
  wlog ht : t ≠ 0; · simp [not_not.mp ht]
  rwa [IsSemisimple_smul_iff ht]

open UniqueFactorizationMonoid in
theorem isSemisimple_of_squarefree_aeval_eq_zero [FiniteDimensional K M]
    {p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0) : f.IsSemisimple := by
  classical
  have := (Submodule.isInternal_prime_power_torsion_of_pid <|
    AEval.isTorsion_of_finiteDimensional K M f).submodule_iSup_eq_top
  rw [AEval.annihilator_top_eq_ker_aeval, minpoly.ker_aeval_eq_span_minpoly,
    Ideal.submodule_span_eq, factors_eq_normalizedFactors] at this
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (fun ⟨q, hq₁⟩ ↦ Submodule.isSemisimple_torsionBy_of_irreducible <| Prime.irreducible ?_) this
  simp only [Multiset.mem_toFinset] at hq₁
  simp only [prime_pow_iff]
  refine ⟨Ideal.prime_generator_of_prime (prime_of_normalized_factor q hq₁),
    Multiset.count_eq_one_of_mem ?_ hq₁⟩
  have hf : Ideal.span {minpoly K f} ≠ 0 := by simpa using minpoly.ne_zero_of_finite K f
  rw [← squarefree_iff_nodup_normalizedFactors hf, Ideal.squarefree_span_singleton]
  exact hp.squarefree_of_dvd (minpoly.dvd K f hpf)

end field

end Module.End
