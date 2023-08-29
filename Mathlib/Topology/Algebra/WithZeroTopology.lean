/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Algebra.Order.WithZero
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.with_zero_topology from "leanprover-community/mathlib"@"3e0c4d76b6ebe9dfafb67d16f7286d2731ed6064"

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.  Then
`Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{ γ | γ < γ₀ }` for some invertible element `γ₀` and
every invertible element is open.  In particular the topology is the following: "a subset `U ⊆ Γ₀`
is open if `0 ∉ U` or if there is an invertible `γ₀ ∈ Γ₀` such that `{ γ | γ < γ₀ } ⊆ U`", see
`WithZeroTopology.isOpen_iff`.

We prove this topology is ordered and T₅ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is defined as a scoped instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`open WithZeroTopology`.
-/

open Topology Filter TopologicalSpace Filter Set Function

namespace WithZeroTopology

variable {α Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : Filter α}
  {f : α → Γ₀}

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
scoped instance (priority := 100) topologicalSpace : TopologicalSpace Γ₀ :=
  TopologicalSpace.mkOfNhds <| update pure 0 <| ⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ)
#align with_zero_topology.topological_space WithZeroTopology.topologicalSpace

theorem nhds_eq_update : (𝓝 : Γ₀ → Filter Γ₀) = update pure 0 (⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ)) :=
  funext <| nhds_mkOfNhds_single <| le_iInf₂ fun _ h₀ => le_principal_iff.2 <| zero_lt_iff.2 h₀
#align with_zero_topology.nhds_eq_update WithZeroTopology.nhds_eq_update

/-!
### Neighbourhoods of zero
-/

theorem nhds_zero : 𝓝 (0 : Γ₀) = ⨅ (γ) (_ : γ ≠ 0), 𝓟 (Iio γ) := by
  rw [nhds_eq_update, update_same]
  -- 🎉 no goals
#align with_zero_topology.nhds_zero WithZeroTopology.nhds_zero

/-- In a linearly ordered group with zero element adjoined, `U` is a neighbourhood of `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`. -/
theorem hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ ≠ 0) Iio := by
  rw [nhds_zero]
  -- ⊢ HasBasis (⨅ (γ : Γ₀) (_ : γ ≠ 0), 𝓟 (Iio γ)) (fun γ => γ ≠ 0) Iio
  refine' hasBasis_biInf_principal _ ⟨1, one_ne_zero⟩
  -- ⊢ DirectedOn ((fun γ => Iio γ) ⁻¹'o fun x x_1 => x ≥ x_1) fun γ => γ = 0 → False
  exact directedOn_iff_directed.2 (directed_of_inf fun a b hab => Iio_subset_Iio hab)
  -- 🎉 no goals
#align with_zero_topology.has_basis_nhds_zero WithZeroTopology.hasBasis_nhds_zero

theorem Iio_mem_nhds_zero (hγ : γ ≠ 0) : Iio γ ∈ 𝓝 (0 : Γ₀) :=
  hasBasis_nhds_zero.mem_of_mem hγ
#align with_zero_topology.Iio_mem_nhds_zero WithZeroTopology.Iio_mem_nhds_zero

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`. -/
theorem nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ ∈ 𝓝 (0 : Γ₀) :=
  Iio_mem_nhds_zero γ.ne_zero
#align with_zero_topology.nhds_zero_of_units WithZeroTopology.nhds_zero_of_units

theorem tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ ∀ (γ₀) (_ : γ₀ ≠ 0), ∀ᶠ x in l, f x < γ₀ := by
  simp [nhds_zero]
  -- 🎉 no goals
#align with_zero_topology.tendsto_zero WithZeroTopology.tendsto_zero

/-!
### Neighbourhoods of non-zero elements
-/

/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp]
theorem nhds_of_ne_zero {γ : Γ₀} (h₀ : γ ≠ 0) : 𝓝 γ = pure γ := by
  rw [nhds_eq_update, update_noteq h₀]
  -- 🎉 no goals
#align with_zero_topology.nhds_of_ne_zero WithZeroTopology.nhds_of_ne_zero

/-- The neighbourhood filter of an invertible element consists of all sets containing that
element. -/
theorem nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  nhds_of_ne_zero γ.ne_zero
#align with_zero_topology.nhds_coe_units WithZeroTopology.nhds_coe_units

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`{γ}` is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({↑γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp
                                                                                   -- 🎉 no goals
#align with_zero_topology.singleton_mem_nhds_of_units WithZeroTopology.singleton_mem_nhds_of_units

/-- If `γ` is a nonzero element of a linearly ordered group with zero element adjoined, then `{γ}`
is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_ne_zero (h : γ ≠ 0) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp [h]
                                                                                      -- 🎉 no goals
#align with_zero_topology.singleton_mem_nhds_of_ne_zero WithZeroTopology.singleton_mem_nhds_of_ne_zero

theorem hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
    HasBasis (𝓝 x) (fun _ : Unit => True) fun _ => {x} := by
  rw [nhds_of_ne_zero h]
  -- ⊢ HasBasis (pure x) (fun x => True) fun x_1 => {x}
  exact hasBasis_pure _
  -- 🎉 no goals
#align with_zero_topology.has_basis_nhds_of_ne_zero WithZeroTopology.hasBasis_nhds_of_ne_zero

theorem hasBasis_nhds_units (γ : Γ₀ˣ) :
    HasBasis (𝓝 (γ : Γ₀)) (fun _ : Unit => True) fun _ => {↑γ} :=
  hasBasis_nhds_of_ne_zero γ.ne_zero
#align with_zero_topology.has_basis_nhds_units WithZeroTopology.hasBasis_nhds_units

theorem tendsto_of_ne_zero {γ : Γ₀} (h : γ ≠ 0) : Tendsto f l (𝓝 γ) ↔ ∀ᶠ x in l, f x = γ := by
  rw [nhds_of_ne_zero h, tendsto_pure]
  -- 🎉 no goals
#align with_zero_topology.tendsto_of_ne_zero WithZeroTopology.tendsto_of_ne_zero

theorem tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ ∀ᶠ x in l, f x = γ₀ :=
  tendsto_of_ne_zero γ₀.ne_zero
#align with_zero_topology.tendsto_units WithZeroTopology.tendsto_units

theorem Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ ∈ 𝓝 γ₁ := by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]
  -- ⊢ Iio γ₂ ∈ 𝓝 0
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align with_zero_topology.Iio_mem_nhds WithZeroTopology.Iio_mem_nhds

/-!
### Open/closed sets
-/

theorem isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ ∃ γ, γ ≠ 0 ∧ Iio γ ⊆ s := by
  rw [isOpen_iff_mem_nhds, ← and_forall_ne (0 : Γ₀)]
  -- ⊢ ((0 ∈ s → s ∈ 𝓝 0) ∧ ∀ (b : Γ₀), b ≠ 0 → b ∈ s → s ∈ 𝓝 b) ↔ ¬0 ∈ s ∨ ∃ γ, γ  …
  simp (config := { contextual := true }) [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]
#align with_zero_topology.is_open_iff WithZeroTopology.isOpen_iff

theorem isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) ∈ s ∨ ∃ γ, γ ≠ 0 ∧ s ⊆ Ici γ := by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
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
@[nolint defLemma]
scoped instance (priority := 100) orderClosedTopology : OrderClosedTopology Γ₀ where
  isClosed_le' := by
    simp only [← isOpen_compl_iff, compl_setOf, not_le, isOpen_iff_mem_nhds]
    -- ⊢ ∀ (a : Γ₀ × Γ₀), a ∈ {a | a.snd < a.fst} → {a | a.snd < a.fst} ∈ 𝓝 a
    rintro ⟨a, b⟩ (hab : b < a)
    -- ⊢ {a | a.snd < a.fst} ∈ 𝓝 (a, b)
    rw [nhds_prod_eq, nhds_of_ne_zero (zero_le'.trans_lt hab).ne', pure_prod]
    -- ⊢ {a | a.snd < a.fst} ∈ map (Prod.mk a) (𝓝 b)
    exact Iio_mem_nhds hab
    -- 🎉 no goals
#align with_zero_topology.order_closed_topology WithZeroTopology.orderClosedTopology

/-- The topology on a linearly ordered group with zero element adjoined is T₅. -/
@[nolint defLemma]
scoped instance (priority := 100) t5Space : T5Space Γ₀ where
  completely_normal := fun s t h₁ h₂ => by
    by_cases hs : 0 ∈ s
    -- ⊢ Disjoint (𝓝ˢ s) (𝓝ˢ t)
    · have ht : 0 ∉ t := fun ht => disjoint_left.1 h₁ (subset_closure hs) ht
      -- ⊢ Disjoint (𝓝ˢ s) (𝓝ˢ t)
      rwa [(isOpen_iff.2 (.inl ht)).nhdsSet_eq, disjoint_nhdsSet_principal]
      -- 🎉 no goals
    · rwa [(isOpen_iff.2 (.inl hs)).nhdsSet_eq, disjoint_principal_nhdsSet]
      -- 🎉 no goals

/-- The topology on a linearly ordered group with zero element adjoined is T₃. -/
@[deprecated t5Space] lemma t3Space : T3Space Γ₀ := inferInstance
#align with_zero_topology.t3_space WithZeroTopology.t3Space

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
@[nolint defLemma]
scoped instance (priority := 100) : ContinuousMul Γ₀ where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, ContinuousAt]
    -- ⊢ ∀ (x : Γ₀ × Γ₀), Tendsto (fun p => p.fst * p.snd) (𝓝 x) (𝓝 (x.fst * x.snd))
    rintro ⟨x, y⟩
    -- ⊢ Tendsto (fun p => p.fst * p.snd) (𝓝 (x, y)) (𝓝 ((x, y).fst * (x, y).snd))
    wlog hle : x ≤ y generalizing x y
    -- ⊢ Tendsto (fun p => p.fst * p.snd) (𝓝 (x, y)) (𝓝 ((x, y).fst * (x, y).snd))
    · have := (this y x (le_of_not_le hle)).comp (continuous_swap.tendsto (x, y))
      -- ⊢ Tendsto (fun p => p.fst * p.snd) (𝓝 (x, y)) (𝓝 ((x, y).fst * (x, y).snd))
      simpa only [mul_comm, Function.comp, Prod.swap] using this
      -- 🎉 no goals
    rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy); skip]
    · rw [zero_mul]
      -- ⊢ Tendsto (fun p => p.fst * p.snd) (𝓝 (0, 0)) (𝓝 0)
      refine ((hasBasis_nhds_zero.prod_nhds hasBasis_nhds_zero).tendsto_iff hasBasis_nhds_zero).2
        fun γ hγ => ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, ?_⟩
      rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩
      -- ⊢ (x, y).fst * (x, y).snd ∈ Iio γ
      exact (mul_lt_mul₀ hx hy).trans_eq (mul_one γ)
      -- 🎉 no goals
    · rw [zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure, tendsto_map'_iff]
      -- ⊢ Tendsto ((fun p => p.fst * p.snd) ∘ fun a => (a, y)) (𝓝 0) (𝓝 0)
      refine' (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun γ hγ => _
      -- ⊢ ∃ ia, ia ≠ 0 ∧ ∀ (x : Γ₀), x ∈ Iio ia → ((fun p => p.fst * p.snd) ∘ fun a => …
      refine' ⟨γ / y, div_ne_zero hγ hy, fun x hx => _⟩
      -- ⊢ ((fun p => p.fst * p.snd) ∘ fun a => (a, y)) x ∈ Iio γ
      calc x * y < γ / y * y := mul_lt_right₀ _ hx hy
      _ = γ := div_mul_cancel _ hy
    · have hy : y ≠ 0 := ((zero_lt_iff.mpr hx).trans_le hle).ne'
      -- ⊢ Tendsto (fun p => p.fst * p.snd) (𝓝 (x, y)) (𝓝 ((x, y).fst * (x, y).snd))
      rw [nhds_prod_eq, nhds_of_ne_zero hx, nhds_of_ne_zero hy, prod_pure_pure]
      -- ⊢ Tendsto (fun p => p.fst * p.snd) (pure (x, y)) (𝓝 ((x, y).fst * (x, y).snd))
      exact pure_le_nhds (x * y)
      -- 🎉 no goals

@[nolint defLemma]
scoped instance (priority := 100) : HasContinuousInv₀ Γ₀ :=
  ⟨fun γ h => by
    rw [ContinuousAt, nhds_of_ne_zero h]
    -- ⊢ Tendsto Inv.inv (pure γ) (𝓝 γ⁻¹)
    exact pure_le_nhds γ⁻¹⟩
    -- 🎉 no goals

end WithZeroTopology
