/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Integral lattices

A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for all
`x, y ∈ L`.

## Main definitions

* `ZLattice.IsIntegral L`: the predicate that `⟪x, y⟫` is an integer for all `x, y ∈ L`.

## Main results

* `ZLattice.isIntegral_iff_le_dualSubmodule`: `L` is integral if and only if it is contained in
  its dual lattice with respect to the inner product.
* `ZLattice.isIntegral_span_iff`: the `ℤ`-span of a set `s` is integral if and only if `⟪x, y⟫` is
  an integer for all `x, y ∈ s`. See also `ZLattice.isIntegral_iff_of_basis`.
* `ZLattice.isIntegral_sup_iff`: `L₁ ⊔ L₂` is integral if and only if `L₁` and `L₂` are integral
  and `⟪x, y⟫` is an integer for all `x ∈ L₁` and `y ∈ L₂`.
* `ZLattice.isIntegral_span_of_orthonormal`: the `ℤ`-span of an orthonormal family is integral.
* `ZLattice.IsIntegral.one_le_norm`: every nonzero vector of an integral lattice has norm at least
  `1`.
* `ZLattice.IsIntegral.discreteTopology`: an integral lattice is discrete.
* `ZLattice.IsIntegral.comap`, `ZLattice.IsIntegral.map`: integrality is preserved under linear
  isometries.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {L L' : Submodule ℤ E}

/-- A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for
all `x, y ∈ L`. -/
def IsIntegral (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, ⟪x, y⟫_ℝ = n

lemma isIntegral_bot : IsIntegral (⊥ : Submodule ℤ E) := by
  intro x hx y hy
  rw [Submodule.mem_bot] at hx
  exact ⟨0, by simp [hx]⟩

/-- A lattice is integral if and only if it is contained in its dual lattice with respect to the
inner product. -/
lemma isIntegral_iff_le_dualSubmodule :
    IsIntegral L ↔ L ≤ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
  simp [IsIntegral, le_iff_mem_imp_mem, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    eq_comm]

/-- The `ℤ`-span of a set `s` is integral if and only if `⟪x, y⟫` is an integer for all
`x, y ∈ s`. -/
lemma isIntegral_span_iff {s : Set E} :
    IsIntegral (Submodule.span ℤ s) ↔ ∀ x ∈ s, ∀ y ∈ s, ∃ n : ℤ, ⟪x, y⟫_ℝ = n := by
  refine ⟨fun h x hx y hy ↦ h x (Submodule.subset_span hx) y (Submodule.subset_span hy),
    fun h x hx y hy ↦ ?_⟩
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact h x hx y hy
  | zero_left => exact ⟨0, by simp⟩
  | zero_right => exact ⟨0, by simp⟩
  | add_left x y z _ _ _ h₁ h₂ =>
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    exact ⟨a + b, by simp [inner_add_left, ha, hb]⟩
  | add_right x y z _ _ _ h₁ h₂ =>
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    exact ⟨a + b, by simp [inner_add_right, ha, hb]⟩
  | smul_left r x y _ _ h =>
    obtain ⟨a, ha⟩ := h
    exact ⟨r * a, by simp [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, ha]⟩
  | smul_right r x y _ _ h =>
    obtain ⟨a, ha⟩ := h
    exact ⟨r * a, by simp [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, ha]⟩

lemma isIntegral_span_range_iff {ι : Type*} {v : ι → E} :
    IsIntegral (Submodule.span ℤ (Set.range v)) ↔ ∀ i j, ∃ n : ℤ, ⟪v i, v j⟫_ℝ = n := by
  simp [isIntegral_span_iff]

lemma isIntegral_span_singleton_iff {v : E} : IsIntegral (ℤ ∙ v) ↔ ∃ n : ℤ, ⟪v, v⟫_ℝ = n := by
  simp [isIntegral_span_iff]

/-- A lattice is integral if and only if the inner products of its basis vectors are integers. -/
lemma isIntegral_iff_of_basis {ι : Type*} (b : Module.Basis ι ℤ L) :
    IsIntegral L ↔ ∀ i j, ∃ n : ℤ, ⟪(b i : E), b j⟫_ℝ = n := by
  have h : Submodule.span ℤ (Set.range fun i ↦ (b i : E)) = L :=
    (Submodule.span_range_subtype_eq_top_iff L fun i ↦ (b i).property).1 b.span_eq
  rw [← isIntegral_span_range_iff, h]

lemma isIntegral_sup_iff {L₁ L₂ : Submodule ℤ E} :
    IsIntegral (L₁ ⊔ L₂) ↔
      IsIntegral L₁ ∧ IsIntegral L₂ ∧ ∀ x ∈ L₁, ∀ y ∈ L₂, ∃ n : ℤ, ⟪x, y⟫_ℝ = n := by
  refine ⟨fun h ↦ ⟨fun x hx y hy ↦ h x (Submodule.mem_sup_left hx) y (Submodule.mem_sup_left hy),
    fun x hx y hy ↦ h x (Submodule.mem_sup_right hx) y (Submodule.mem_sup_right hy),
    fun x hx y hy ↦ h x (Submodule.mem_sup_left hx) y (Submodule.mem_sup_right hy)⟩,
    fun ⟨h₁, h₂, h₁₂⟩ ↦ ?_⟩
  rw [← Submodule.span_eq L₁, ← Submodule.span_eq L₂, ← Submodule.span_union, isIntegral_span_iff]
  rintro x (hx | hx) y (hy | hy)
  · exact h₁ x hx y hy
  · exact h₁₂ x hx y hy
  · simpa [real_inner_comm] using h₁₂ y hy x hx
  · exact h₂ x hx y hy

/-- The `ℤ`-span of an orthonormal family is integral. -/
lemma isIntegral_span_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) :
    IsIntegral (Submodule.span ℤ (Set.range v)) := by
  classical
  refine isIntegral_span_range_iff.2 fun i j ↦ ?_
  rw [orthonormal_iff_ite.1 hv i j]
  split_ifs
  exacts [⟨1, by simp⟩, ⟨0, by simp⟩]

namespace IsIntegral

lemma mono (hL : IsIntegral L) (h : L' ≤ L) : IsIntegral L' :=
  fun x hx y hy ↦ hL x (h hx) y (h hy)

/-- The norm squared of a vector in an integral lattice is a natural number. -/
lemma exists_norm_sq_eq (hL : IsIntegral L) {x : E} (hx : x ∈ L) : ∃ n : ℕ, ‖x‖ ^ 2 = n := by
  obtain ⟨n, hn⟩ := hL x hx x hx
  rw [real_inner_self_eq_norm_sq] at hn
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast hn ▸ sq_nonneg ‖x‖)
  exact ⟨m, by simpa using hn⟩

/-- Every nonzero vector of an integral lattice has norm at least `1`. -/
lemma one_le_norm (hL : IsIntegral L) {x : E} (hx : x ∈ L) (hx₀ : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨n, hn⟩ := hL.exists_norm_sq_eq hx
  rw [← one_le_sq_iff₀ (norm_nonneg x), hn, Nat.one_le_cast, Nat.one_le_iff_ne_zero]
  rintro rfl
  simp_all

/-- An integral lattice is discrete. -/
lemma discreteTopology (hL : IsIntegral L) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, one_pos, fun y hy ↦ by_contra fun hy₀ ↦ ?_⟩
  exact (hL.one_le_norm y.property (by simpa using hy₀)).not_gt (by simpa using hy)

/-- The preimage of an integral lattice under a linear isometry is integral. -/
lemma comap (hL : IsIntegral L) (e : F →ₗᵢ[ℝ] E) :
    IsIntegral (ZLattice.comap ℝ L e.toLinearMap) :=
  fun _ hx _ hy ↦ by simpa [LinearIsometry.inner_map_map] using hL _ hx _ hy

/-- The image of an integral lattice under a linear isometry is integral. -/
lemma map (hL : IsIntegral L) (e : E →ₗᵢ[ℝ] F) :
    IsIntegral (L.map (e.toLinearMap.restrictScalars ℤ)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simpa [LinearIsometry.inner_map_map] using hL x hx y hy

end IsIntegral

end ZLattice
