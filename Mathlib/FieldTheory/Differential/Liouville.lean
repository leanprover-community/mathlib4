/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.FieldTheory.Differential.Basic

/-!
# Liouville field extension

This file defines Liouville field extensions, which are field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.
-/

open Differential algebraMap

/--
We say that a field extension `K / F` is Liouville if, whenever an element a ∈ F can be written as
`a = v + ∑ cᵢ * logd uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be written in that
way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] : Prop where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι' : Type) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0)
      (u' : ι' → F) (v' : F), a = ∑ x, c' x * logDeriv (u' x) + v'′

instance IsLiouville.rfl (F : Type*) [Field F] [Differential F] : IsLiouville F F where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

lemma IsLiouville.trans {F : Type*} {K : Type*} {A : Type*} [Field F]
    [Field K] [Field A] [Algebra F K] [Algebra K A] [Algebra F A]
    [Differential F] [Differential K] [Differential A]
    [DifferentialAlgebra F K] [DifferentialAlgebra K A] [DifferentialAlgebra F A]
    [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι'', _, c'', hc', u'', v', h'⟩ := inst2.is_liouville (a : K) ι
        ((↑) ∘ c)
        (fun _ ↦ by simp only [Function.comp_apply, ← coe_deriv, lift_map_eq_zero_iff, hc])
        ((↑) ∘ u) v
        (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι'') := mem_range_of_deriv_eq_zero F (hc' x)
    choose c' hc using hc
    apply inst1.is_liouville a ι'' c' _ u'' v'
    rw [h']
    · simp [hc]
    · intro
      apply_fun ((↑) : F → K)
      simp only [Function.comp_apply, coe_deriv, hc, algebraMap.coe_zero]
      apply hc'
      apply NoZeroSMulDivisors.algebraMap_injective
