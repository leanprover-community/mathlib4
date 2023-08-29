/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Group.Basic

#align_import topology.algebra.order.group from "leanprover-community/mathlib"@"84dc0bd6619acaea625086d6f53cb35cdd554219"

/-!
# Topology on a linear ordered additive commutative group

In this file we prove that a linear ordered additive commutative group with order topology is a
topological group. We also prove continuity of `abs : G → G` and provide convenience lemmas like
`ContinuousAt.abs`.
-/


open Set Filter

open Topology Filter

variable {α G : Type*} [TopologicalSpace G] [LinearOrderedAddCommGroup G] [OrderTopology G]

variable {l : Filter α} {f g : α → G}

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommGroup.topologicalAddGroup : TopologicalAddGroup G
    where
  continuous_add := by
    refine' continuous_iff_continuousAt.2 _
    -- ⊢ ∀ (x : G × G), ContinuousAt (fun p => p.fst + p.snd) x
    rintro ⟨a, b⟩
    -- ⊢ ContinuousAt (fun p => p.fst + p.snd) (a, b)
    refine' LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 => _
    -- ⊢ ∀ᶠ (b_1 : G × G) in 𝓝 (a, b), |b_1.fst + b_1.snd - (fun p => p.fst + p.snd)  …
    rcases dense_or_discrete 0 ε with (⟨δ, δ0, δε⟩ | ⟨_h₁, h₂⟩)
    -- ⊢ ∀ᶠ (b_1 : G × G) in 𝓝 (a, b), |b_1.fst + b_1.snd - (fun p => p.fst + p.snd)  …
    · -- If there exists `δ ∈ (0, ε)`, then we choose `δ`-nhd of `a` and `(ε-δ)`-nhd of `b`
      filter_upwards [(eventually_abs_sub_lt a δ0).prod_nhds
          (eventually_abs_sub_lt b (sub_pos.2 δε))]
      rintro ⟨x, y⟩ ⟨hx : |x - a| < δ, hy : |y - b| < ε - δ⟩
      -- ⊢ |(x, y).fst + (x, y).snd - (a + b)| < ε
      rw [add_sub_add_comm]
      -- ⊢ |(x, y).fst - a + ((x, y).snd - b)| < ε
      calc
        |x - a + (y - b)| ≤ |x - a| + |y - b| := abs_add _ _
        _ < δ + (ε - δ) := add_lt_add hx hy
        _ = ε := add_sub_cancel'_right _ _
    · -- Otherwise `ε`-nhd of each point `a` is `{a}`
      have hε : ∀ {x y}, |x - y| < ε → x = y := by
        intro x y h
        simpa [sub_eq_zero] using h₂ _ h
      filter_upwards [(eventually_abs_sub_lt a ε0).prod_nhds (eventually_abs_sub_lt b ε0)]
      -- ⊢ ∀ (a_1 : G × G), |a_1.fst - a| < ε ∧ |a_1.snd - b| < ε → |a_1.fst + a_1.snd  …
      rintro ⟨x, y⟩ ⟨hx : |x - a| < ε, hy : |y - b| < ε⟩
      -- ⊢ |(x, y).fst + (x, y).snd - (a + b)| < ε
      simpa [hε hx, hε hy]
      -- 🎉 no goals
  continuous_neg :=
    continuous_iff_continuousAt.2 fun a =>
      LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 =>
        (eventually_abs_sub_lt a ε0).mono fun x hx => by rwa [neg_sub_neg, abs_sub_comm]
                                                         -- 🎉 no goals
#align linear_ordered_add_comm_group.topological_add_group LinearOrderedAddCommGroup.topologicalAddGroup

@[continuity]
theorem continuous_abs : Continuous (abs : G → G) :=
  continuous_id.max continuous_neg
#align continuous_abs continuous_abs

protected theorem Filter.Tendsto.abs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => |f x|) l (𝓝 |a|) :=
  (continuous_abs.tendsto _).comp h
#align filter.tendsto.abs Filter.Tendsto.abs

theorem tendsto_zero_iff_abs_tendsto_zero (f : α → G) :
    Tendsto f l (𝓝 0) ↔ Tendsto (abs ∘ f) l (𝓝 0) := by
  refine' ⟨fun h => (abs_zero : |(0 : G)| = 0) ▸ h.abs, fun h => _⟩
  -- ⊢ Tendsto f l (𝓝 0)
  have : Tendsto (fun a => -|f a|) l (𝓝 0) := (neg_zero : -(0 : G) = 0) ▸ h.neg
  -- ⊢ Tendsto f l (𝓝 0)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le this h (fun x => neg_abs_le_self <| f x) fun x =>
      le_abs_self <| f x
#align tendsto_zero_iff_abs_tendsto_zero tendsto_zero_iff_abs_tendsto_zero

variable [TopologicalSpace α] {a : α} {s : Set α}

protected theorem Continuous.abs (h : Continuous f) : Continuous fun x => |f x| :=
  continuous_abs.comp h
#align continuous.abs Continuous.abs

protected theorem ContinuousAt.abs (h : ContinuousAt f a) : ContinuousAt (fun x => |f x|) a :=
  Filter.Tendsto.abs h
#align continuous_at.abs ContinuousAt.abs

protected theorem ContinuousWithinAt.abs (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => |f x|) s a :=
  Filter.Tendsto.abs h
#align continuous_within_at.abs ContinuousWithinAt.abs

protected theorem ContinuousOn.abs (h : ContinuousOn f s) : ContinuousOn (fun x => |f x|) s :=
  fun x hx => (h x hx).abs
#align continuous_on.abs ContinuousOn.abs

theorem tendsto_abs_nhdsWithin_zero : Tendsto (abs : G → G) (𝓝[≠] 0) (𝓝[>] 0) :=
  (continuous_abs.tendsto' (0 : G) 0 abs_zero).inf <|
    tendsto_principal_principal.2 fun _x => abs_pos.2
#align tendsto_abs_nhds_within_zero tendsto_abs_nhdsWithin_zero
