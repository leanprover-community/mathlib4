/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Integral
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Integral lattices in real inner product spaces

A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for all
`x, y ∈ L`. This is the special case of `LinearMap.BilinForm.IsIntegral` for the inner product,
see `Submodule.isIntegral_iff_isIntegral_innerₗ`.

## Main definitions

* `Submodule.IsIntegral L`: the predicate that `⟪x, y⟫` is an integer for all `x, y ∈ L`.

## Main results

* `Submodule.isIntegral_iff_le_dualSubmodule`: `L` is integral if and only if it is contained in
  its dual lattice with respect to the inner product.
* `Submodule.isIntegral_span_iff`: the `ℤ`-span of a set `s` is integral if and only if `⟪x, y⟫` is
  an integer for all `x, y ∈ s`. See also `Submodule.isIntegral_iff_of_basis`.
* `Submodule.isIntegral_sup_iff`: `L₁ ⊔ L₂` is integral if and only if `L₁` and `L₂` are integral
  and `⟪x, y⟫` is an integer for all `x ∈ L₁` and `y ∈ L₂`.
* `Submodule.isIntegral_span_of_orthonormal`: the `ℤ`-span of an orthonormal family is integral.
* `Submodule.IsIntegral.one_le_norm`: every nonzero vector of an integral lattice has norm at least
  `1`.
* `Submodule.IsIntegral.discreteTopology`: an integral lattice is discrete.
* `Submodule.IsIntegral.isLattice`: in finite dimension, an integral `ℤ`-submodule is a lattice in
  the sense of `Submodule.IsLattice`.
* `Submodule.IsIntegral.comap`, `Submodule.IsIntegral.map`: integrality is preserved under linear
  isometries.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {L L' : Submodule ℤ E}

/-- A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for
all `x, y ∈ L`. -/
def IsIntegral (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, ⟪x, y⟫_ℝ = n

/-- A `ℤ`-submodule is integral if and only if it is integral with respect to the inner product
as a bilinear form. -/
lemma isIntegral_iff_isIntegral_innerₗ :
    IsIntegral L ↔ LinearMap.BilinForm.IsIntegral (innerₗ E) L := by
  simp [IsIntegral, LinearMap.BilinForm.IsIntegral, mem_one, eq_comm]

lemma isIntegral_bot : IsIntegral (⊥ : Submodule ℤ E) :=
  isIntegral_iff_isIntegral_innerₗ.2 LinearMap.BilinForm.isIntegral_bot

/-- A lattice is integral if and only if it is contained in its dual lattice with respect to the
inner product. -/
lemma isIntegral_iff_le_dualSubmodule :
    IsIntegral L ↔ L ≤ LinearMap.BilinForm.dualSubmodule (innerₗ E) L :=
  isIntegral_iff_isIntegral_innerₗ

/-- The `ℤ`-span of a set `s` is integral if and only if `⟪x, y⟫` is an integer for all
`x, y ∈ s`. -/
lemma isIntegral_span_iff {s : Set E} :
    IsIntegral (span ℤ s) ↔ ∀ x ∈ s, ∀ y ∈ s, ∃ n : ℤ, ⟪x, y⟫_ℝ = n := by
  simp [isIntegral_iff_isIntegral_innerₗ, LinearMap.BilinForm.isIntegral_span_iff, mem_one,
    eq_comm]

lemma isIntegral_span_range_iff {ι : Type*} {v : ι → E} :
    IsIntegral (span ℤ (Set.range v)) ↔ ∀ i j, ∃ n : ℤ, ⟪v i, v j⟫_ℝ = n := by
  simp [isIntegral_span_iff]

lemma isIntegral_span_singleton_iff {v : E} : IsIntegral (ℤ ∙ v) ↔ ∃ n : ℤ, ⟪v, v⟫_ℝ = n := by
  simp [isIntegral_span_iff]

/-- A lattice is integral if and only if the inner products of its basis vectors are integers. -/
lemma isIntegral_iff_of_basis {ι : Type*} (b : Module.Basis ι ℤ L) :
    IsIntegral L ↔ ∀ i j, ∃ n : ℤ, ⟪(b i : E), b j⟫_ℝ = n := by
  simp [isIntegral_iff_isIntegral_innerₗ, LinearMap.BilinForm.isIntegral_iff_of_basis b, mem_one,
    eq_comm]

lemma isIntegral_sup_iff {L₁ L₂ : Submodule ℤ E} :
    IsIntegral (L₁ ⊔ L₂) ↔
      IsIntegral L₁ ∧ IsIntegral L₂ ∧ ∀ x ∈ L₁, ∀ y ∈ L₂, ∃ n : ℤ, ⟪x, y⟫_ℝ = n := by
  have h : (∀ x ∈ L₁, ∀ y ∈ L₂, ∃ n : ℤ, ⟪y, x⟫_ℝ = n) ↔
      ∀ x ∈ L₁, ∀ y ∈ L₂, ∃ n : ℤ, ⟪x, y⟫_ℝ = n := by
    simp only [real_inner_comm]
  simp [isIntegral_iff_isIntegral_innerₗ, LinearMap.BilinForm.isIntegral_sup_iff, mem_one,
    eq_comm, h]

/-- The `ℤ`-span of an orthonormal family is integral. -/
lemma isIntegral_span_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) :
    IsIntegral (span ℤ (Set.range v)) := by
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

/-- In finite dimension, an integral `ℤ`-submodule is a lattice: taking inner products with an
`ℝ`-basis of `span ℝ L` contained in `L` embeds `L` into `ℤ ^ r`. -/
lemma isLattice [FiniteDimensional ℝ E] (hL : IsIntegral L) : L.IsLattice ℝ := by
  classical
  obtain ⟨s, hsL, hs, hli⟩ := exists_linearIndependent ℝ (L : Set E)
  have := hli.setFinite.fintype
  let ψ : E →ₗ[ℝ] s → ℝ := LinearMap.pi fun v ↦ innerₗ E (v : E)
  have hψ : Set.InjOn ψ L := fun x hx y hy hxy ↦ by
    have h : span ℝ s ≤ LinearMap.ker (innerₗ E (x - y)) := span_le.2 fun v hv ↦ by
      simpa [ψ, inner_sub_left, sub_eq_zero, real_inner_comm] using congrFun hxy ⟨v, hv⟩
    exact sub_eq_zero.1 <| inner_self_eq_zero.1 <| h <| hs ▸ subset_span (sub_mem hx hy)
  have : (span ℤ (Set.range (Pi.basisFun ℝ s))).IsLattice ℝ :=
    IsLattice.span_of_linearIndependent ℝ (Pi.basisFun ℝ s).linearIndependent
  have hle : L.map (ψ.restrictScalars ℤ) ≤ span ℤ (Set.range (Pi.basisFun ℝ s)) := by
    rintro _ ⟨x, hx, rfl⟩
    choose n hn using fun v : s ↦ hL v (hsL v.property) x hx
    refine (mem_span_range_iff_exists_fun ℤ).2 ⟨n, funext fun v ↦ ?_⟩
    simp [ψ, hn, Pi.single_apply]
  have := IsLattice.mono ℝ hle
  exact IsLattice.of_map ℝ L hψ

/-- The preimage of an integral lattice under a linear isometry is integral. -/
lemma comap (hL : IsIntegral L) (e : F →ₗᵢ[ℝ] E) :
    IsIntegral (L.comap (e.toLinearMap.restrictScalars ℤ)) :=
  fun _ hx _ hy ↦ by simpa [LinearIsometry.inner_map_map] using hL _ hx _ hy

/-- The image of an integral lattice under a linear isometry is integral. -/
lemma map (hL : IsIntegral L) (e : E →ₗᵢ[ℝ] F) :
    IsIntegral (L.map (e.toLinearMap.restrictScalars ℤ)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simpa [LinearIsometry.inner_map_map] using hL x hx y hy

end IsIntegral

end Submodule
