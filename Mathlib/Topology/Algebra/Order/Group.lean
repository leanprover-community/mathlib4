/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Topology on a linear ordered commutative group

In this file we prove that a linear ordered commutative group with order topology
is a topological group.
We also prove continuity of `abs : G → G` and provide convenience lemmas like `ContinuousAt.abs`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Set Filter Function

open scoped Topology

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [OrderTopology G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toIsTopologicalGroup :
    IsTopologicalGroup G where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, Prod.forall, ContinuousAt,
      LinearOrderedCommGroup.tendsto_nhds]
    intro a b ε hε
    rcases dense_or_discrete 1 ε with ⟨δ, hδ₁, hδε⟩ | ⟨-, hε_min⟩
    · filter_upwards [(eventually_mabs_div_lt _ hδ₁).prod_nhds
        (eventually_mabs_div_lt _ (one_lt_div'.mpr hδε))]
      rintro ⟨c, d⟩ ⟨hc, hd⟩
      calc
        |c * d / (a * b)|ₘ = |(c / a) * (d / b)|ₘ := by rw [div_mul_div_comm]
        _ ≤ |c / a|ₘ * |d / b|ₘ := mabs_mul_le ..
        _ < δ * (ε / δ) := mul_lt_mul_of_lt_of_lt hc hd
        _ = ε := mul_div_cancel ..
    · have (x : G) : ∀ᶠ y in 𝓝 x, y = x :=
        (eventually_mabs_div_lt _ hε).mono fun y hy ↦ mabs_div_le_one.mp <| hε_min _ hy
      filter_upwards [(this _).prod_nhds (this _)]
      simp [hε]
  continuous_inv := continuous_iff_continuousAt.2 fun a ↦
    LinearOrderedCommGroup.tendsto_nhds.2 fun ε ε0 ↦
      (eventually_mabs_div_lt a ε0).mono fun x hx ↦ by rwa [inv_div_inv, mabs_div_comm]

@[to_additive (attr := continuity)]
theorem continuous_mabs : Continuous (mabs : G → G) :=
  continuous_id.max continuous_inv

section Tendsto

variable {α : Type*} {l : Filter α} {f : α → G}

@[to_additive]
protected theorem Filter.Tendsto.mabs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => |f x|ₘ) l (𝓝 |a|ₘ) :=
  (continuous_mabs.tendsto _).comp h

@[to_additive (attr := simp)]
theorem comap_mabs_nhds_one : comap mabs (𝓝 (1 : G)) = 𝓝 1 := by
  simp [nhds_eq_iInf_mabs_div]

@[to_additive]
theorem tendsto_one_iff_mabs_tendsto_one (f : α → G) :
    Tendsto f l (𝓝 1) ↔ Tendsto (mabs ∘ f) l (𝓝 1) := by
  rw [← tendsto_comap_iff, comap_mabs_nhds_one]

end Tendsto

variable {X : Type*} [TopologicalSpace X] {f : X → G} {s : Set X} {x : X}

@[to_additive (attr := fun_prop)]
protected theorem Continuous.mabs (h : Continuous f) : Continuous fun x => |f x|ₘ :=
  continuous_mabs.comp h

@[to_additive (attr := fun_prop)]
protected theorem ContinuousAt.mabs (h : ContinuousAt f x) : ContinuousAt (fun x => |f x|ₘ) x :=
  Filter.Tendsto.mabs h

@[to_additive]
protected theorem ContinuousWithinAt.mabs (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => |f x|ₘ) s x :=
  Filter.Tendsto.mabs h

@[to_additive (attr := fun_prop)]
protected theorem ContinuousOn.mabs (h : ContinuousOn f s) : ContinuousOn (fun x => |f x|ₘ) s :=
  fun x hx => (h x hx).mabs

@[to_additive]
theorem tendsto_mabs_nhdsNE_one : Tendsto (mabs : G → G) (𝓝[≠] 1) (𝓝[>] 1) :=
  (continuous_mabs.tendsto' (1 : G) 1 mabs_one).inf <|
    tendsto_principal_principal.2 fun _x => one_lt_mabs.2

/-- In a linearly ordered multiplicative group, the integer powers of an element are dense
iff they are the whole group. -/
@[to_additive /-- In a linearly ordered additive group, the integer multiples of an element are
dense iff they are the whole group. -/]
theorem denseRange_zpow_iff_surjective {a : G} :
    DenseRange (a ^ · : ℤ → G) ↔ Surjective (a ^ · : ℤ → G) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.denseRange⟩
  wlog! ha₀ : 1 < a generalizing a
  · simp only [← range_eq_univ, DenseRange] at *
    rcases ha₀.eq_or_lt with rfl | hlt
    · simpa only [one_zpow, range_const, dense_iff_closure_eq, closure_singleton] using h
    · have H : range (a⁻¹ ^ · : ℤ → G) = range (a ^ · : ℤ → G) := by
        simpa only [← inv_zpow, zpow_neg, comp_def] using neg_surjective.range_comp (a ^ · : ℤ → G)
      rw [← H]
      apply this <;> simpa only [H, one_lt_inv']
  intro b
  obtain ⟨m, hm, hm'⟩ : ∃ m : ℤ, a ^ m ∈ Ioo b (b * a * a) := by
    have hne : (Ioo b (b * a * a)).Nonempty := ⟨b * a, by simpa⟩
    simpa using h.exists_mem_open isOpen_Ioo hne
  rcases eq_or_ne b (a ^ (m - 1)) with rfl | hne; · simp
  suffices (Ioo (a ^ m) (a ^ (m + 1))).Nonempty by
    rcases h.exists_mem_open isOpen_Ioo this with ⟨l, hl⟩
    have : m < l ∧ l < m + 1 := by simpa [zpow_lt_zpow_iff_right ha₀] using hl
    lia
  rcases hne.lt_or_gt with hlt | hlt
  · refine ⟨b * a * a, hm', ?_⟩
    simpa only [zpow_add, zpow_sub, zpow_one, ← div_eq_mul_inv, lt_div_iff_mul_lt,
      mul_lt_mul_iff_right] using hlt
  · use b * a
    simp only [mem_Ioo, zpow_add, zpow_sub, zpow_one, ← div_eq_mul_inv,
      mul_lt_mul_iff_right] at hlt ⊢
    exact ⟨div_lt_iff_lt_mul.1 hlt, hm⟩

/-- In a nontrivial densely linearly ordered commutative group,
the integer powers of an element can't be dense. -/
@[to_additive /-- In a nontrivial densely linearly ordered additive group,
the integer multiples of an element can't be dense. -/]
theorem not_denseRange_zpow [Nontrivial G] [DenselyOrdered G] {a : G} :
    ¬DenseRange (a ^ · : ℤ → G) :=
  denseRange_zpow_iff_surjective.not.mpr fun h ↦
    not_isCyclic_of_denselyOrdered G ⟨⟨a, h⟩⟩
