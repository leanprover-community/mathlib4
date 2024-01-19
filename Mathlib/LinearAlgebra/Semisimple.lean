/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Polynomial.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.CompleteSublattice
import Mathlib.RingTheory.SimpleModule

/-!
# Semisimple linear endomorphisms

Given an `R`-module `M` together with an `R`-linear endomorphism `f : M → M`, the following two
conditions are equivalent:
 1. Every `f`-invariant submodule of `M` has an `f`-invariant complement.
 2. `M` is a semisimple `R[X]`-module, where the action of the polynomial ring is induced by `f`.

A linear endomorphism `f` satisfying these equivalent conditions is known as a semisimple
endomorphism. We provide basic definitions and results about such endomorphisms in this file.

## Main definitions / results:
 * `Module.End.IsSemisimple`: the definition that a linear endomorphism is semisimple
 * `Module.End.isSemisimple_iff`: the characterisation of semisimplicity in terms of invariant
   submodules.
 * `Module.End.eq_zero_of_isNilpotent_isSemisimple`: the collections of nilpotent and semisimple
   endomorphisms meet only in the zero endomorphism.

## TODO

In finite dimensions over a field:
 * Sum / product of commuting semisimple endomorphism is semisimple
 * If semisimple then generalized eigenspace is eigenspace
 * Semisimple iff minpoly is squarefree
 * Restriction of semisimple endomorphism is semisimple
 * Triangularizable iff diagonalisable for semisimple endomorphisms

-/

open Set Function Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

variable (f g : End R M)

/-- A linear endomorphism of an `R`-module `M` is called semisimple if the induced `R[X]`-module
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
  -- TODO tidy up this crazy proof
  set k := nilpotencyClass f
  wlog hk' : 2 ≤ k
  · replace hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with (hk₀ : nilpotencyClass f = 0) | (hk₁ : nilpotencyClass f = 1)
    · rw [← pos_nilpotencyClass_iff, hk₀] at hn; contradiction
    · exact eq_zero_of_nilpotencyClass_eq_one hk₁
  let p := LinearMap.ker (f ^ (k - 1))
  have hp : p ≤ p.comap f := fun x hx ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ← LinearMap.mul_apply, ← pow_succ', add_comm,
      pow_add, pow_one, LinearMap.mul_apply, hx, map_zero]
  have hk₁ : f ^ k = 0 := pow_nilpotencyClass hn
  have hk₂ : p < ⊤ :=
    lt_top_iff_ne_top.mpr fun contra ↦ pow_pred_nilpotencyClass hn <| LinearMap.ker_eq_top.mp contra
  obtain ⟨q, hq₀, hq₁, hq₂⟩ := isSemisimple_iff.mp hs p hp
  have hq₂' : q ≠ ⊥ := by
    -- Missing API for `Codisjoint`?
    rw [lt_top_iff_ne_top] at hk₂
    contrapose! hk₂
    simpa [hk₂] using hq₂
  obtain ⟨m, hm₁, hm₀⟩ := q.ne_bot_iff.mp hq₂'
  have hm₂ : f m ∈ p := by
    have foo : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.zero_lt_of_lt hk')
    rw [LinearMap.mem_ker, ← LinearMap.mul_apply, ← pow_succ', foo, hk₁, LinearMap.zero_apply]
  have hm₃ : f m ∈ q := hq₀ hm₁
  have hm₄ : f m = 0 := by
    rw [← Submodule.mem_bot (R := R), ← hq₁.eq_bot]
    exact ⟨hm₂, hm₃⟩
  have hm₅ : m ∈ p := by
    have foo : 1 ≤ k - 1 := by omega
    rw [LinearMap.mem_ker]
    exact LinearMap.pow_map_zero_of_le foo hm₄
  have hm₆ : m = 0 := by
    rw [← Submodule.mem_bot (R := R), ← hq₁.eq_bot]
    exact ⟨hm₅, hm₁⟩
  contradiction

section field

variable {K : Type*} [Field K] [Module K M] {f' : End K M}

lemma IsSemisimple_smul_iff {t : K} (ht : t ≠ 0) :
    (t • f').IsSemisimple ↔ f'.IsSemisimple := by
  simp [isSemisimple_iff, Submodule.comap_smul f' (h := ht)]

lemma IsSemisimple_smul (t : K) (h : f'.IsSemisimple) :
    (t • f').IsSemisimple := by
  wlog ht : t ≠ 0; · simp [not_not.mp ht]
  rwa [IsSemisimple_smul_iff ht]

end field

end Module.End
