/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.with_zero_topology
! leanprover-community/mathlib commit 3e0c4d76b6ebe9dfafb67d16f7286d2731ed6064
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.WithZero
import Mathbin.Topology.Algebra.Order.Field

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.
Then `Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{γ | γ < γ₀}` for some invertible element `γ₀`
and every invertible element is open.
In particular the topology is the following:
"a subset `U ⊆ Γ₀` is open if `0 ∉ U` or if there is an invertible
`γ₀ ∈ Γ₀` such that `{γ | γ < γ₀} ⊆ U`", see `linear_ordered_comm_group_with_zero.is_open_iff`.

We prove this topology is ordered and T₃ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is not defined as a global instance since it may not be the desired topology on a
linearly ordered commutative group with zero. You can locally activate this topology using
`open_locale with_zero_topology`.
-/


open Topology Filter

open TopologicalSpace Filter Set Function

namespace WithZeroTopology

variable {α Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : Filter α}
  {f : α → Γ₀}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ «expr ≠ » 0) -/
/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
protected def topologicalSpace : TopologicalSpace Γ₀ :=
  TopologicalSpace.mkOfNhds <| update pure 0 <| ⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ)
#align with_zero_topology.topological_space WithZeroTopology.topologicalSpace

attribute [scoped instance] WithZeroTopology.topologicalSpace

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ «expr ≠ » 0) -/
theorem nhds_eq_update : (𝓝 : Γ₀ → Filter Γ₀) = update pure 0 (⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ)) :=
  funext <| nhds_mkOfNhds_single <| le_infᵢ₂ fun γ h₀ => le_principal_iff.2 <| zero_lt_iff.2 h₀
#align with_zero_topology.nhds_eq_update WithZeroTopology.nhds_eq_update

/-!
### Neighbourhoods of zero
-/


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ «expr ≠ » 0) -/
theorem nhds_zero : 𝓝 (0 : Γ₀) = ⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ) := by rw [nhds_eq_update, update_same]
#align with_zero_topology.nhds_zero WithZeroTopology.nhds_zero

/-- In a linearly ordered group with zero element adjoined, `U` is a neighbourhood of `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`. -/
theorem hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ ≠ 0) Iio :=
  by
  rw [nhds_zero]
  refine' has_basis_binfi_principal _ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (directed_of_inf fun a b hab => Iio_subset_Iio hab)
#align with_zero_topology.has_basis_nhds_zero WithZeroTopology.hasBasis_nhds_zero

theorem Iio_mem_nhds_zero (hγ : γ ≠ 0) : Iio γ ∈ 𝓝 (0 : Γ₀) :=
  hasBasis_nhds_zero.mem_of_mem hγ
#align with_zero_topology.Iio_mem_nhds_zero WithZeroTopology.Iio_mem_nhds_zero

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`. -/
theorem nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ ∈ 𝓝 (0 : Γ₀) :=
  Iio_mem_nhds_zero γ.NeZero
#align with_zero_topology.nhds_zero_of_units WithZeroTopology.nhds_zero_of_units

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ₀ «expr ≠ » 0) -/
theorem tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ ∀ (γ₀) (_ : γ₀ ≠ 0), ∀ᶠ x in l, f x < γ₀ := by
  simp [nhds_zero]
#align with_zero_topology.tendsto_zero WithZeroTopology.tendsto_zero

/-!
### Neighbourhoods of non-zero elements
-/


/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp]
theorem nhds_of_ne_zero {γ : Γ₀} (h₀ : γ ≠ 0) : 𝓝 γ = pure γ := by
  rw [nhds_eq_update, update_noteq h₀]
#align with_zero_topology.nhds_of_ne_zero WithZeroTopology.nhds_of_ne_zero

/-- The neighbourhood filter of an invertible element consists of all sets containing that
element. -/
theorem nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  nhds_of_ne_zero γ.NeZero
#align with_zero_topology.nhds_coe_units WithZeroTopology.nhds_coe_units

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`{γ}` is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp
#align with_zero_topology.singleton_mem_nhds_of_units WithZeroTopology.singleton_mem_nhds_of_units

/-- If `γ` is a nonzero element of a linearly ordered group with zero element adjoined, then `{γ}`
is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_ne_zero (h : γ ≠ 0) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp [h]
#align with_zero_topology.singleton_mem_nhds_of_ne_zero WithZeroTopology.singleton_mem_nhds_of_ne_zero

theorem hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
    HasBasis (𝓝 x) (fun i : Unit => True) fun i => {x} :=
  by
  rw [nhds_of_ne_zero h]
  exact has_basis_pure _
#align with_zero_topology.has_basis_nhds_of_ne_zero WithZeroTopology.hasBasis_nhds_of_ne_zero

theorem hasBasis_nhds_units (γ : Γ₀ˣ) : HasBasis (𝓝 (γ : Γ₀)) (fun i : Unit => True) fun i => {γ} :=
  hasBasis_nhds_of_ne_zero γ.NeZero
#align with_zero_topology.has_basis_nhds_units WithZeroTopology.hasBasis_nhds_units

theorem tendsto_of_ne_zero {γ : Γ₀} (h : γ ≠ 0) : Tendsto f l (𝓝 γ) ↔ ∀ᶠ x in l, f x = γ := by
  rw [nhds_of_ne_zero h, tendsto_pure]
#align with_zero_topology.tendsto_of_ne_zero WithZeroTopology.tendsto_of_ne_zero

theorem tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ ∀ᶠ x in l, f x = γ₀ :=
  tendsto_of_ne_zero γ₀.NeZero
#align with_zero_topology.tendsto_units WithZeroTopology.tendsto_units

theorem Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ ∈ 𝓝 γ₁ := by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]
#align with_zero_topology.Iio_mem_nhds WithZeroTopology.Iio_mem_nhds

/-!
### Open/closed sets
-/


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ «expr ≠ » 0) -/
theorem isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ ∃ (γ : _)(_ : γ ≠ 0), Iio γ ⊆ s :=
  by
  rw [isOpen_iff_mem_nhds, ← and_forall_ne (0 : Γ₀)]
  simp (config := { contextual := true }) [nhds_of_ne_zero, imp_iff_not_or,
    has_basis_nhds_zero.mem_iff]
#align with_zero_topology.is_open_iff WithZeroTopology.isOpen_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (γ «expr ≠ » 0) -/
theorem isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) ∈ s ∨ ∃ (γ : _)(_ : γ ≠ 0), s ⊆ Ici γ :=
  by
  simp only [← isOpen_compl_iff, is_open_iff, mem_compl_iff, Classical.not_not, ← compl_Ici,
    compl_subset_compl]
#align with_zero_topology.is_closed_iff WithZeroTopology.isClosed_iff

theorem isOpen_Iio {a : Γ₀} : IsOpen (Iio a) :=
  isOpen_iff.mpr <| imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩
#align with_zero_topology.is_open_Iio WithZeroTopology.isOpen_Iio

/-!
### Instances
-/


/-- The topology on a linearly ordered group with zero element adjoined is compatible with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed. -/
protected theorem orderClosedTopology : OrderClosedTopology Γ₀ :=
  {
    isClosed_le' :=
      by
      simp only [← isOpen_compl_iff, compl_set_of, not_le, isOpen_iff_mem_nhds]
      rintro ⟨a, b⟩ (hab : b < a)
      rw [nhds_prod_eq, nhds_of_ne_zero (zero_le'.trans_lt hab).ne', pure_prod]
      exact Iio_mem_nhds hab }
#align with_zero_topology.order_closed_topology WithZeroTopology.orderClosedTopology

attribute [scoped instance] WithZeroTopology.orderClosedTopology

/-- The topology on a linearly ordered group with zero element adjoined is T₃. -/
theorem t3Space : T3Space Γ₀ :=
  {
    to_regularSpace :=
      RegularSpace.ofLift'_closure fun γ =>
        by
        rcases ne_or_eq γ 0 with (h₀ | rfl)
        ·
          rw [nhds_of_ne_zero h₀, lift'_pure (monotone_closure Γ₀), closure_singleton,
            principal_singleton]
        ·
          exact
            has_basis_nhds_zero.lift'_closure_eq_self fun x hx =>
              is_closed_iff.2 <| Or.inl <| zero_lt_iff.2 hx }
#align with_zero_topology.t3_space WithZeroTopology.t3Space

attribute [scoped instance] WithZeroTopology.t3Space

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
protected theorem continuousMul : ContinuousMul Γ₀ :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x, y⟩
    wlog hle : x ≤ y generalizing x y
    · have := tendsto.comp (this y x (le_of_not_le hle)) (continuous_swap.tendsto (x, y))
      simpa only [mul_comm, Function.comp, Prod.swap]
    rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy), skip]
    · rw [ContinuousAt, MulZeroClass.zero_mul]
      refine'
        ((has_basis_nhds_zero.prod_nhds has_basis_nhds_zero).tendsto_iffₓ has_basis_nhds_zero).2
          fun γ hγ => ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, _⟩
      rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩
      exact (mul_lt_mul₀ hx hy).trans_eq (mul_one γ)
    · rw [ContinuousAt, MulZeroClass.zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure,
        tendsto_map'_iff]
      refine' (has_basis_nhds_zero.tendsto_iff has_basis_nhds_zero).2 fun γ hγ => _
      refine' ⟨γ / y, div_ne_zero hγ hy, fun x hx => _⟩
      calc
        x * y < γ / y * y := mul_lt_right₀ _ hx hy
        _ = γ := div_mul_cancel _ hy
        
    · have hy : y ≠ 0 := ((zero_lt_iff.mpr hx).trans_le hle).ne'
      rw [ContinuousAt, nhds_prod_eq, nhds_of_ne_zero hx, nhds_of_ne_zero hy, prod_pure_pure]
      exact pure_le_nhds (x * y)⟩
#align with_zero_topology.has_continuous_mul WithZeroTopology.continuousMul

attribute [scoped instance] WithZeroTopology.continuousMul

protected theorem hasContinuousInv₀ : HasContinuousInv₀ Γ₀ :=
  ⟨fun γ h => by
    rw [ContinuousAt, nhds_of_ne_zero h]
    exact pure_le_nhds γ⁻¹⟩
#align with_zero_topology.has_continuous_inv₀ WithZeroTopology.hasContinuousInv₀

attribute [scoped instance] WithZeroTopology.hasContinuousInv₀

end WithZeroTopology

