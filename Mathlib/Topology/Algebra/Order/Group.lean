/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Topology on a linear ordered additive commutative group

In this file we prove that a linear ordered additive commutative group with order topology is a
topological group. We also prove continuity of `abs : G → G` and provide convenience lemmas like
`ContinuousAt.abs`.
-/


open Set Filter Function

open scoped Topology

variable {α G : Type*} [TopologicalSpace G] [LinearOrderedAddCommGroup G] [OrderTopology G]
variable {l : Filter α} {f g : α → G}

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommGroup.topologicalAddGroup :
    TopologicalAddGroup G where
  continuous_add := by
    refine continuous_iff_continuousAt.2 ?_
    rintro ⟨a, b⟩
    refine LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 => ?_
    rcases dense_or_discrete 0 ε with (⟨δ, δ0, δε⟩ | ⟨_h₁, h₂⟩)
    · -- If there exists `δ ∈ (0, ε)`, then we choose `δ`-nhd of `a` and `(ε-δ)`-nhd of `b`
      filter_upwards [(eventually_abs_sub_lt a δ0).prod_nhds
          (eventually_abs_sub_lt b (sub_pos.2 δε))]
      rintro ⟨x, y⟩ ⟨hx : |x - a| < δ, hy : |y - b| < ε - δ⟩
      rw [add_sub_add_comm]
      calc
        |x - a + (y - b)| ≤ |x - a| + |y - b| := abs_add _ _
        _ < δ + (ε - δ) := add_lt_add hx hy
        _ = ε := add_sub_cancel _ _
    · -- Otherwise `ε`-nhd of each point `a` is `{a}`
      have hε : ∀ {x y}, |x - y| < ε → x = y := by
        intro x y h
        simpa [sub_eq_zero] using h₂ _ h
      filter_upwards [(eventually_abs_sub_lt a ε0).prod_nhds (eventually_abs_sub_lt b ε0)]
      rintro ⟨x, y⟩ ⟨hx : |x - a| < ε, hy : |y - b| < ε⟩
      simpa [hε hx, hε hy]
  continuous_neg :=
    continuous_iff_continuousAt.2 fun a =>
      LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 =>
        (eventually_abs_sub_lt a ε0).mono fun x hx => by rwa [neg_sub_neg, abs_sub_comm]

@[continuity]
theorem continuous_abs : Continuous (abs : G → G) :=
  continuous_id.max continuous_neg

protected theorem Filter.Tendsto.abs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x ↦ |f x|) l (𝓝 |a|) :=
  (continuous_abs.tendsto _).comp h

theorem tendsto_zero_iff_abs_tendsto_zero (f : α → G) :
    Tendsto f l (𝓝 0) ↔ Tendsto (abs ∘ f) l (𝓝 0) := by
  refine ⟨fun h ↦ (abs_zero : |(0 : G)| = 0) ▸ h.abs, fun h ↦ ?_⟩
  have : Tendsto (fun a ↦ -|f a|) l (𝓝 0) := (neg_zero : -(0 : G) = 0) ▸ h.neg
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le this h (fun x ↦ neg_abs_le <| f x) fun x =>
      le_abs_self <| f x

variable [TopologicalSpace α] {a : α} {s : Set α}

@[fun_prop]
protected theorem Continuous.abs (h : Continuous f) : Continuous fun x ↦ |f x| :=
  continuous_abs.comp h

@[fun_prop]
protected theorem ContinuousAt.abs (h : ContinuousAt f a) : ContinuousAt (fun x ↦ |f x|) a :=
  Filter.Tendsto.abs h

protected theorem ContinuousWithinAt.abs (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x ↦ |f x|) s a :=
  Filter.Tendsto.abs h

@[fun_prop]
protected theorem ContinuousOn.abs (h : ContinuousOn f s) : ContinuousOn (fun x ↦ |f x|) s :=
  fun x hx => (h x hx).abs

theorem tendsto_abs_nhdsWithin_zero : Tendsto (abs : G → G) (𝓝[≠] 0) (𝓝[>] 0) :=
  (continuous_abs.tendsto' (0 : G) 0 abs_zero).inf <|
    tendsto_principal_principal.2 fun _x => abs_pos.2

/-- In a linearly ordered additive group, the integer multiples of an element are dense
iff they are the whole group. -/
theorem denseRange_zsmul_iff_surjective {a : G} :
    DenseRange (· • a : ℤ → G) ↔ Surjective (· • a : ℤ → G) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.denseRange⟩
  wlog ha₀ : 0 < a generalizing a
  · simp only [← range_eq_univ, DenseRange] at *
    rcases (not_lt.1 ha₀).eq_or_lt with rfl | hlt
    · simpa only [smul_zero, range_const, dense_iff_closure_eq, closure_singleton] using h
    · have H : range (· • -a : ℤ → G) = range (· • a : ℤ → G) := by
        simpa only [smul_neg, ← neg_smul] using neg_surjective.range_comp (· • a)
      rw [← H]
      apply this <;> simpa only [H, neg_pos]
  intro b
  obtain ⟨m, hm, hm'⟩ : ∃ m : ℤ, m • a ∈ Ioo b (b + a + a) := by
    have hne : (Ioo b (b + a + a)).Nonempty := ⟨b + a, by simpa⟩
    simpa using h.exists_mem_open isOpen_Ioo hne
  rcases eq_or_ne b ((m - 1) • a) with rfl | hne; · simp
  suffices (Ioo (m • a) ((m + 1) • a)).Nonempty by
    rcases h.exists_mem_open isOpen_Ioo this with ⟨l, hl⟩
    have : m < l ∧ l < m + 1 := by simpa [zsmul_lt_zsmul_iff_left ha₀] using hl
    omega
  rcases hne.lt_or_lt with hlt | hlt
  · refine ⟨b + a + a, hm', ?_⟩
    simpa only [add_smul, sub_smul, one_smul, lt_sub_iff_add_lt, add_lt_add_iff_right] using hlt
  · use b + a
    simp only [mem_Ioo, add_smul, sub_smul, one_smul, add_lt_add_iff_right] at hlt ⊢
    exact ⟨sub_lt_iff_lt_add.1 hlt, hm⟩

/-- In a nontrivial densely linearly ordered additive group,
the integer multiples of an element can't be dense. -/
theorem not_denseRange_zsmul [Nontrivial G] [DenselyOrdered G] {a : G} :
    ¬DenseRange (· • a : ℤ → G) :=
  denseRange_zsmul_iff_surjective.not.mpr fun h ↦
    not_isAddCyclic_of_denselyOrdered G ⟨⟨a, h⟩⟩
