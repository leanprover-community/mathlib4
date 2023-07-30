/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.SetTheory.Cardinal.CountableCover
import Mathlib.Data.Real.Cardinality
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cardinality of open subsets of vector spaces

Any nonempty open subset of a topological vector space over a nontrivially normed field has the same
cardinality as the whole space. This is proved in `cardinal_eq_of_is_open`.

We deduce that a countable set in a nontrivial real vector space has dense complement, in
`Set.Countable.dense_compl`.
-/
universe u v

open Filter Pointwise Set
open scoped Cardinal Topology

/-- In a topological vector space over a nontrivially normed field, any neighborhood of zero has
the same cardinality as the whole space. -/
lemma cardinal_eq_of_mem_nhds_zero
    {E : Type _} (𝕜 : Type _) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : s ∈ 𝓝 (0 : E)) : #s = #E := by
  /- As `s` is a neighborhood of `0`, the space is covered by the rescaled sets `c^n • s`,
  where `c` is any element of `𝕜` with norm `> 1`. All these sets are in bijection and have
  therefore the same cardinality. The conclusion follows. -/
  obtain ⟨c, hc⟩ : ∃ x : 𝕜 , 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : ∀ n, c^n ≠ 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : ∀ (x : E), ∀ᶠ n in (atTop : Filter ℕ), x ∈ c^n • s := by
    intro x
    have : Tendsto (fun n ↦ (c^n) ⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n ↦ (c^n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_0_of_norm_lt_1
        rw [norm_inv]
        exact inv_lt_one hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x ∈ s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : ∀ n, #(c^n • s) = #s := by
    intro n
    have : c^n • s ≃ s :=
    { toFun := fun x ↦ ⟨(c^n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x ↦ ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x ↦ by simp [smul_smul, mul_inv_cancel (cn_ne n)]
      right_inv := fun x ↦ by simp [smul_smul, inv_mul_cancel (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm

/-- In a topological vector space over a nontrivially normed field, any neighborhood of a point has
the same cardinality as the whole space. -/
theorem cardinal_eq_of_mem_nhds
    {E : Type _} (𝕜 : Type _) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} {x : E} (hs : s ∈ 𝓝 x) : #s = #E := by
  let g := Homeomorph.addLeft x
  let t := g ⁻¹' s
  have : t ∈ 𝓝 0 := g.continuous.continuousAt.preimage_mem_nhds (by simpa using hs)
  have A : #t = #E := cardinal_eq_of_mem_nhds_zero 𝕜 this
  have B : #t = #s := Cardinal.mk_subtype_of_equiv s g.toEquiv
  rwa [B] at A

/-- In a topological vector space over a nontrivially normed field, any nonempty open set has
the same cardinality as the whole space. -/
theorem cardinal_eq_of_is_open
    {E : Type _} (𝕜 : Type _) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsOpen s) (h's : s.Nonempty) : #s = #E := by
  rcases h's with ⟨x, hx⟩
  exact cardinal_eq_of_mem_nhds 𝕜 (hs.mem_nhds hx)

/-- In a nontrivial real topological vector space, a countable subset has dense complement. -/
theorem Set.Countable.dense_compl {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [Nontrivial E] (s : Set E) (hs : s.Countable) : Dense sᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  contrapose! hs
  intro H
  apply lt_irrefl (ℵ₀ : Cardinal.{u})
  calc
  ℵ₀ < Cardinal.lift.{u} (#ℝ) := by simp [Cardinal.mk_real, Cardinal.aleph0_lt_continuum]
  _  ≤ #E := by simpa using Cardinal.mk_le_of_module ℝ E
  _  = #(interior s) := (cardinal_eq_of_is_open ℝ isOpen_interior (nmem_singleton_empty.1 hs)).symm
  _  ≤ ℵ₀ := (H.mono interior_subset).le_aleph0
