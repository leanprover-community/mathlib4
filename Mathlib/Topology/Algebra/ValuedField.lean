/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Valuation
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Topology.Algebra.UniformField

#align_import topology.algebra.valued_field from "leanprover-community/mathlib"@"3e0c4d76b6ebe9dfafb67d16f7286d2731ed6064"

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, ie inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/


open Filter Set

open Topology

section DivisionRing

variable {K : Type*} [DivisionRing K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable (v : Valuation K Γ₀)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (i.e. the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
theorem Valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y ≠ 0)
    (h : v (x - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) < γ := by
  have hyp1 : v (x - y) < γ * (v y * v y) := lt_of_lt_of_le h (min_le_left _ _)
  -- ⊢ ↑v (x⁻¹ - y⁻¹) < ↑γ
  have hyp1' : v (x - y) * (v y * v y)⁻¹ < γ := mul_inv_lt_of_lt_mul₀ hyp1
  -- ⊢ ↑v (x⁻¹ - y⁻¹) < ↑γ
  have hyp2 : v (x - y) < v y := lt_of_lt_of_le h (min_le_right _ _)
  -- ⊢ ↑v (x⁻¹ - y⁻¹) < ↑γ
  have key : v x = v y := Valuation.map_eq_of_sub_lt v hyp2
  -- ⊢ ↑v (x⁻¹ - y⁻¹) < ↑γ
  have x_ne : x ≠ 0 := by
    intro h
    apply y_ne
    rw [h, v.map_zero] at key
    exact v.zero_iff.1 key.symm
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹ := by
    rw [mul_sub_left_distrib, sub_mul, mul_assoc, show y * y⁻¹ = 1 from mul_inv_cancel y_ne,
      show x⁻¹ * x = 1 from inv_mul_cancel x_ne, mul_one, one_mul]
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) := by rw [decomp]
    _ = v x⁻¹ * (v <| y - x) * v y⁻¹ := by repeat' rw [Valuation.map_mul]
    _ = (v x)⁻¹ * (v <| y - x) * (v y)⁻¹ := by rw [map_inv₀, map_inv₀]
    _ = (v <| y - x) * (v y * v y)⁻¹ := by rw [mul_assoc, mul_comm, key, mul_assoc, mul_inv_rev]
    _ = (v <| y - x) * (v y * v y)⁻¹ := rfl
    _ = (v <| x - y) * (v y * v y)⁻¹ := by rw [Valuation.map_sub_swap]
    _ < γ := hyp1'
#align valuation.inversion_estimate Valuation.inversion_estimate

end InversionEstimate

open Valued

/-- The topology coming from a valuation on a division ring makes it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100) Valued.topologicalDivisionRing [Valued K Γ₀] :
    TopologicalDivisionRing K :=
  { (by infer_instance : TopologicalRing K) with
        -- 🎉 no goals
    continuousAt_inv₀ := by
      intro x x_ne s s_in
      -- ⊢ s ∈ map Inv.inv (𝓝 x)
      cases' Valued.mem_nhds.mp s_in with γ hs; clear s_in
      -- ⊢ s ∈ map Inv.inv (𝓝 x)
                                                -- ⊢ s ∈ map Inv.inv (𝓝 x)
      rw [mem_map, Valued.mem_nhds]
      -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ Inv.inv ⁻¹' s
      change ∃ γ : Γ₀ˣ, { y : K | (v (y - x) : Γ₀) < γ } ⊆ { x : K | x⁻¹ ∈ s }
      -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ {x | x⁻¹ ∈ s}
      have vx_ne := (Valuation.ne_zero_iff <| v).mpr x_ne
      -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ {x | x⁻¹ ∈ s}
      let γ' := Units.mk0 _ vx_ne
      -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ {x | x⁻¹ ∈ s}
      use min (γ * (γ' * γ')) γ'
      -- ⊢ {y | ↑v (y - x) < ↑(min (γ * (γ' * γ')) γ')} ⊆ {x | x⁻¹ ∈ s}
      intro y y_in
      -- ⊢ y ∈ {x | x⁻¹ ∈ s}
      apply hs
      -- ⊢ y⁻¹ ∈ {y | ↑v (y - x⁻¹) < ↑γ}
      simp only [mem_setOf_eq] at y_in
      -- ⊢ y⁻¹ ∈ {y | ↑v (y - x⁻¹) < ↑γ}
      rw [Units.min_val, Units.val_mul, Units.val_mul] at y_in
      -- ⊢ y⁻¹ ∈ {y | ↑v (y - x⁻¹) < ↑γ}
      exact Valuation.inversion_estimate _ x_ne y_in }
      -- 🎉 no goals
#align valued.topological_division_ring Valued.topologicalDivisionRing

/-- A valued division ring is separated. -/
instance (priority := 100) ValuedRing.separated [Valued K Γ₀] : SeparatedSpace K := by
  rw [separated_iff_t2]
  -- ⊢ T2Space K
  apply TopologicalAddGroup.t2Space_of_zero_sep
  -- ⊢ ∀ (x : K), x ≠ 0 → ∃ U, U ∈ 𝓝 0 ∧ ¬x ∈ U
  intro x x_ne
  -- ⊢ ∃ U, U ∈ 𝓝 0 ∧ ¬x ∈ U
  refine' ⟨{ k | v k < v x }, _, fun h => lt_irrefl _ h⟩
  -- ⊢ {k | ↑v k < ↑v x} ∈ 𝓝 0
  rw [Valued.mem_nhds]
  -- ⊢ ∃ γ, {y | ↑v (y - 0) < ↑γ} ⊆ {k | ↑v k < ↑v x}
  have vx_ne := (Valuation.ne_zero_iff <| v).mpr x_ne
  -- ⊢ ∃ γ, {y | ↑v (y - 0) < ↑γ} ⊆ {k | ↑v k < ↑v x}
  let γ' := Units.mk0 _ vx_ne
  -- ⊢ ∃ γ, {y | ↑v (y - 0) < ↑γ} ⊆ {k | ↑v k < ↑v x}
  exact ⟨γ', fun y hy => by simpa using hy⟩
  -- 🎉 no goals
#align valued_ring.separated ValuedRing.separated

section

open WithZeroTopology

open Valued

theorem Valued.continuous_valuation [Valued K Γ₀] : Continuous (v : K → Γ₀) := by
  rw [continuous_iff_continuousAt]
  -- ⊢ ∀ (x : K), ContinuousAt (↑v) x
  intro x
  -- ⊢ ContinuousAt (↑v) x
  rcases eq_or_ne x 0 with (rfl | h)
  -- ⊢ ContinuousAt (↑v) 0
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    -- ⊢ ∀ (γ₀ : Γ₀), γ₀ ≠ 0 → ∀ᶠ (x : K) in 𝓝 0, ↑v x < γ₀
    intro γ hγ
    -- ⊢ ∀ᶠ (x : K) in 𝓝 0, ↑v x < γ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    -- ⊢ ∃ γ_1, {x | ↑v x < ↑γ_1} ⊆ {x | ↑v x < γ}
    use Units.mk0 γ hγ; rfl
    -- ⊢ {x | ↑v x < ↑(Units.mk0 γ hγ)} ⊆ {x | ↑v x < γ}
                        -- 🎉 no goals
  · have v_ne : (v x : Γ₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    -- ⊢ ContinuousAt (↑v) x
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
    -- ⊢ ∀ᶠ (x_1 : K) in 𝓝 x, ↑v x_1 = ↑v x
    apply Valued.loc_const v_ne
    -- 🎉 no goals
#align valued.continuous_valuation Valued.continuous_valuation

end

end ValuationTopologicalDivisionRing

end DivisionRing

namespace Valued

open UniformSpace

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

local notation "hat " => Completion

/-- A valued field is completable. -/
instance (priority := 100) completable : CompletableTopField K :=
  { ValuedRing.separated with
    nice := by
      rintro F hF h0
      -- ⊢ Cauchy (map (fun x => x⁻¹) F)
      have : ∃ γ₀ : Γ₀ˣ, ∃ M ∈ F, ∀ x ∈ M, (γ₀ : Γ₀) ≤ v x := by
        rcases Filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
        rcases Valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
        exists γ₀, M, M_in
        intro x xM
        apply le_of_not_lt _
        intro hyp
        have : x ∈ U ∩ M := ⟨hU hyp, xM⟩
        rwa [H] at this
      rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
      -- ⊢ Cauchy (map (fun x => x⁻¹) F)
      rw [Valued.cauchy_iff] at hF ⊢
      -- ⊢ NeBot (map (fun x => x⁻¹) F) ∧ ∀ (γ : Γ₀ˣ), ∃ M, M ∈ map (fun x => x⁻¹) F ∧  …
      refine' ⟨hF.1.map _, _⟩
      -- ⊢ ∀ (γ : Γ₀ˣ), ∃ M, M ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ M → ∀ (y : K), y …
      replace hF := hF.2
      -- ⊢ ∀ (γ : Γ₀ˣ), ∃ M, M ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ M → ∀ (y : K), y …
      intro γ
      -- ⊢ ∃ M, M ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ M → ∀ (y : K), y ∈ M → ↑v (y  …
      rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
      -- ⊢ ∃ M, M ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ M → ∀ (y : K), y ∈ M → ↑v (y  …
      clear hF
      -- ⊢ ∃ M, M ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ M → ∀ (y : K), y ∈ M → ↑v (y  …
      use (fun x : K => x⁻¹) '' (M₀ ∩ M₁)
      -- ⊢ (fun x => x⁻¹) '' (M₀ ∩ M₁) ∈ map (fun x => x⁻¹) F ∧ ∀ (x : K), x ∈ (fun x = …
      constructor
      -- ⊢ (fun x => x⁻¹) '' (M₀ ∩ M₁) ∈ map (fun x => x⁻¹) F
      · rw [mem_map]
        -- ⊢ (fun x => x⁻¹) ⁻¹' ((fun x => x⁻¹) '' (M₀ ∩ M₁)) ∈ F
        apply mem_of_superset (Filter.inter_mem M₀_in M₁_in)
        -- ⊢ M₀ ∩ M₁ ⊆ (fun x => x⁻¹) ⁻¹' ((fun x => x⁻¹) '' (M₀ ∩ M₁))
        exact subset_preimage_image _ _
        -- 🎉 no goals
      · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩
        -- ⊢ ↑v ((fun x => x⁻¹) y - (fun x => x⁻¹) x) < ↑γ
        simp only [mem_setOf_eq]
        -- ⊢ ↑v (y⁻¹ - x⁻¹) < ↑γ
        specialize H₁ x x_in₁ y y_in₁
        -- ⊢ ↑v (y⁻¹ - x⁻¹) < ↑γ
        replace x_in₀ := H₀ x x_in₀
        -- ⊢ ↑v (y⁻¹ - x⁻¹) < ↑γ
        replace  := H₀ y y_in₀
        -- ⊢ ↑v (y⁻¹ - x⁻¹) < ↑γ
        clear H₀
        -- ⊢ ↑v (y⁻¹ - x⁻¹) < ↑γ
        apply Valuation.inversion_estimate
        -- ⊢ x ≠ 0
        · have : (v x : Γ₀) ≠ 0 := by
            intro h
            rw [h] at x_in₀
            simp at x_in₀
          exact (Valuation.ne_zero_iff _).mp this
          -- 🎉 no goals
        · refine' lt_of_lt_of_le H₁ _
          -- ⊢ ↑(min (γ * γ₀ * γ₀) γ₀) ≤ min (↑γ * (↑v x * ↑v x)) (↑v x)
          rw [Units.min_val]
          -- ⊢ min ↑(γ * γ₀ * γ₀) ↑γ₀ ≤ min (↑γ * (↑v x * ↑v x)) (↑v x)
          apply min_le_min _ x_in₀
          -- ⊢ ↑(γ * γ₀ * γ₀) ≤ ↑γ * (↑v x * ↑v x)
          rw [mul_assoc]
          -- ⊢ ↑(γ * (γ₀ * γ₀)) ≤ ↑γ * (↑v x * ↑v x)
          have : ((γ₀ * γ₀ : Γ₀ˣ) : Γ₀) ≤ v x * v x :=
            calc
              ↑γ₀ * ↑γ₀ ≤ ↑γ₀ * v x := mul_le_mul_left' x_in₀ ↑γ₀
              _ ≤ _ := mul_le_mul_right' x_in₀ (v x)
          rw [Units.val_mul]
          -- ⊢ ↑γ * ↑(γ₀ * γ₀) ≤ ↑γ * (↑v x * ↑v x)
          exact mul_le_mul_left' this γ }
          -- 🎉 no goals
#align valued.completable Valued.completable

open WithZeroTopology

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def extension : hat K → Γ₀ :=
  Completion.denseInducing_coe.extend (v : K → Γ₀)
#align valued.extension Valued.extension

theorem continuous_extension : Continuous (Valued.extension : hat K → Γ₀) := by
  refine' Completion.denseInducing_coe.continuous_extend _
  -- ⊢ ∀ (b : hat K), ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 b)) (𝓝 c)
  intro x₀
  -- ⊢ ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 x₀)) (𝓝 c)
  rcases eq_or_ne x₀ 0 with (rfl | h)
  -- ⊢ ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 0)) (𝓝 c)
  · refine' ⟨0, _⟩
    -- ⊢ Tendsto (↑v) (Filter.comap (↑K) (𝓝 0)) (𝓝 0)
    erw [← Completion.denseInducing_coe.toInducing.nhds_eq_comap]
    -- ⊢ Tendsto (↑v) (𝓝 0) (𝓝 0)
    exact Valued.continuous_valuation.tendsto' 0 0 (map_zero v)
    -- 🎉 no goals
  · have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K) := by
      have : (v (1 : K) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert Valued.loc_const this
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → (v x : Γ₀) = 1 := by
      rwa [Completion.denseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 (1 : hat K), (0 : hat K) ∉ V' ∧ ∀ (x) (_ : x ∈ V') (y) (_ : y ∈ V'),
      x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : hat K × hat K => p.1 * p.2⁻¹) ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : hat K)]
        refine'
          Tendsto.mul continuous_fst.continuousAt (Tendsto.comp _ continuous_snd.continuousAt)
        -- Porting note: Added `ContinuousAt.tendsto`
        convert (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| hat K)
      have : hatKstar ∈ 𝓝 (1 : hat K) := compl_singleton_mem_nhds zero_ne_one.symm
      use U ∩ hatKstar, Filter.inter_mem U_in this
      constructor
      · rintro ⟨_, h'⟩
        rw [mem_compl_singleton_iff] at h'
        exact h' rfl
      · rintro x ⟨hx, _⟩ y ⟨hy, _⟩
        apply hU <;> assumption
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    -- ⊢ ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 x₀)) (𝓝 c)
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel h, mul_one]
      have r : Function.RightInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel h, mul_one]
      have c : Continuous fun x : hat K => x * x₀⁻¹ := continuous_id.mul continuous_const
      rw [image_eq_preimage_of_inverse l r]
      rw [← mul_inv_cancel h] at V'_in
      exact c.continuousAt V'_in
    have : ∃ z₀ : K, ∃ y₀ ∈ V', ↑z₀ = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine' ⟨z₀, y₀, y₀_in, ⟨H.symm, _⟩⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h H
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    -- ⊢ ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 x₀)) (𝓝 c)
    have vz₀_ne : (v z₀ : Γ₀) ≠ 0 := by rwa [Valuation.ne_zero_iff]
    -- ⊢ ∃ c, Tendsto (↑v) (Filter.comap (↑K) (𝓝 x₀)) (𝓝 c)
    refine' ⟨v z₀, _⟩
    -- ⊢ Tendsto (↑v) (Filter.comap (↑K) (𝓝 x₀)) (𝓝 (↑v z₀))
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    -- ⊢ ∀ᶠ (b : hat K) in 𝓝 x₀, ∀ (a : K), ↑K a = b → ↑v a = ↑v z₀
    filter_upwards [nhds_right]with x x_in a ha
    -- ⊢ ↑v a = ↑v z₀
    rcases x_in with ⟨y, y_in, rfl⟩
    -- ⊢ ↑v a = ↑v z₀
    have : (v (a * z₀⁻¹) : Γ₀) = 1 := by
      apply hV
      have : (z₀⁻¹ : K) = (z₀ : hat K)⁻¹ := map_inv₀ (Completion.coeRingHom : K →+* hat K) z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel h, mul_one]
      solve_by_elim
    calc
      v a = v (a * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel z₀_ne, mul_one]
      _ = v (a * z₀⁻¹) * v z₀ := (Valuation.map_mul _ _ _)
      _ = v z₀ := by rw [this, one_mul]
#align valued.continuous_extension Valued.continuous_extension

@[simp, norm_cast]
theorem extension_extends (x : K) : extension (x : hat K) = v x := by
  refine' Completion.denseInducing_coe.extend_eq_of_tendsto _
  -- ⊢ Tendsto (↑v) (Filter.comap (↑K) (𝓝 (↑K x))) (𝓝 (↑v x))
  rw [← Completion.denseInducing_coe.nhds_eq_comap]
  -- ⊢ Tendsto (↑v) (𝓝 x) (𝓝 (↑v x))
  exact Valued.continuous_valuation.continuousAt
  -- 🎉 no goals
#align valued.extension_extends Valued.extension_extends

/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def extensionValuation : Valuation (hat K) Γ₀ where
  toFun := Valued.extension
  map_zero' := by
    rw [← v.map_zero (R := K), ← Valued.extension_extends (0 : K)]
    -- ⊢ extension 0 = extension (↑K 0)
    rfl
    -- 🎉 no goals
  map_one' := by
    simp
    -- ⊢ extension 1 = 1
    rw [← Completion.coe_one, Valued.extension_extends (1 : K)]
    -- ⊢ ↑v 1 = 1
    exact Valuation.map_one _
    -- 🎉 no goals
  map_mul' x y := by
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x * y) = extension x * extension y)
    · have c1 : Continuous fun x : hat K × hat K => Valued.extension (x.1 * x.2) :=
        Valued.continuous_extension.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : hat K × hat K => Valued.extension x.1 * Valued.extension x.2 :=
        (Valued.continuous_extension.comp continuous_fst).mul
          (Valued.continuous_extension.comp continuous_snd)
      exact isClosed_eq c1 c2
      -- 🎉 no goals
    · intro x y
      -- ⊢ extension (↑K x * ↑K y) = extension (↑K x) * extension (↑K y)
      norm_cast
      -- ⊢ ↑v (x * y) = ↑v x * ↑v y
      exact Valuation.map_mul _ _ _
      -- 🎉 no goals
  map_add_le_max' x y := by
    rw [le_max_iff]
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := extension, map_zero' := (_ : exten …
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x + y) ≤ extension x ∨ extension (x + y) ≤ extension y)
    · have cont : Continuous (Valued.extension : hat K → Γ₀) := Valued.continuous_extension
      -- ⊢ IsClosed {x | extension (x.fst + x.snd) ≤ extension x.fst ∨ extension (x.fst …
      exact
        (isClosed_le (cont.comp continuous_add) <| cont.comp continuous_fst).union
          (isClosed_le (cont.comp continuous_add) <| cont.comp continuous_snd)
    · intro x y
      -- ⊢ extension (↑K x + ↑K y) ≤ extension (↑K x) ∨ extension (↑K x + ↑K y) ≤ exten …
      norm_cast
      -- ⊢ ↑v (x + y) ≤ ↑v x ∨ ↑v (x + y) ≤ ↑v y
      rw [← le_max_iff]
      -- ⊢ ↑v (x + y) ≤ max (↑v x) (↑v y)
      exact v.map_add x y
      -- 🎉 no goals
#align valued.extension_valuation Valued.extensionValuation

-- Bourbaki CA VI §5 no.3 Proposition 5 (d)
theorem closure_coe_completion_v_lt {γ : Γ₀ˣ} :
    closure ((↑) '' { x : K | v x < (γ : Γ₀) }) =
    { x : hat K | extensionValuation x < (γ : Γ₀) } := by
  ext x
  -- ⊢ x ∈ closure (↑K '' {x | ↑v x < ↑γ}) ↔ x ∈ {x | ↑extensionValuation x < ↑γ}
  let γ₀ := extensionValuation x
  -- ⊢ x ∈ closure (↑K '' {x | ↑v x < ↑γ}) ↔ x ∈ {x | ↑extensionValuation x < ↑γ}
  suffices γ₀ ≠ 0 → (x ∈ closure ((↑) '' { x : K | v x < (γ : Γ₀) }) ↔ γ₀ < (γ : Γ₀)) by
    cases' eq_or_ne γ₀ 0 with h h
    · simp only [h, (Valuation.zero_iff _).mp h, mem_setOf_eq, Valuation.map_zero, Units.zero_lt,
        iff_true_iff]
      apply subset_closure
      exact ⟨0, by simp only [mem_setOf_eq, Valuation.map_zero, Units.zero_lt, true_and_iff]; rfl ⟩
    · exact this h
  intro h
  -- ⊢ x ∈ closure (↑K '' {x | ↑v x < ↑γ}) ↔ γ₀ < ↑γ
  have hγ₀ : extension ⁻¹' {γ₀} ∈ 𝓝 x :=
    continuous_extension.continuousAt.preimage_mem_nhds
      (WithZeroTopology.singleton_mem_nhds_of_ne_zero h)
  rw [mem_closure_iff_nhds']
  -- ⊢ (∀ (t : Set (hat K)), t ∈ 𝓝 x → ∃ y, ↑y ∈ t) ↔ γ₀ < ↑γ
  refine' ⟨fun hx => _, fun hx s hs => _⟩
  -- ⊢ γ₀ < ↑γ
  · obtain ⟨⟨-, y, hy₁ : v y < (γ : Γ₀), rfl⟩, hy₂⟩ := hx _ hγ₀
    -- ⊢ γ₀ < ↑γ
    replace hy₂ : v y = γ₀
    -- ⊢ ↑v y = γ₀
    · simpa using hy₂
      -- 🎉 no goals
    rwa [← hy₂]
    -- 🎉 no goals
  · obtain ⟨y, hy₁, hy₂⟩ := Completion.denseRange_coe.mem_nhds (inter_mem hγ₀ hs)
    -- ⊢ ∃ y, ↑y ∈ s
    replace hy₁ : v y = γ₀
    -- ⊢ ↑v y = γ₀
    · simpa using hy₁
      -- 🎉 no goals
    rw [← hy₁] at hx
    -- ⊢ ∃ y, ↑y ∈ s
    exact ⟨⟨y, ⟨y, hx, rfl⟩⟩, hy₂⟩
    -- 🎉 no goals
#align valued.closure_coe_completion_v_lt Valued.closure_coe_completion_v_lt

noncomputable instance valuedCompletion : Valued (hat K) Γ₀ where
  v := extensionValuation
  is_topological_valuation s := by
    suffices
      HasBasis (𝓝 (0 : hat K)) (fun _ => True) fun γ : Γ₀ˣ => { x | extensionValuation x < γ } by
      rw [this.mem_iff]
      exact exists_congr fun γ => by simp
    simp_rw [← closure_coe_completion_v_lt]
    -- ⊢ HasBasis (𝓝 0) (fun x => True) fun γ => closure (↑K '' {x | ↑v x < ↑γ})
    exact (hasBasis_nhds_zero K Γ₀).hasBasis_of_denseInducing Completion.denseInducing_coe
    -- 🎉 no goals
#align valued.valued_completion Valued.valuedCompletion

-- Porting note: removed @[norm_cast] attribute due to error:
-- norm_cast: badly shaped lemma, rhs can't start with coe
@[simp]
theorem valuedCompletion_apply (x : K) : Valued.v (x : hat K) = v x :=
  extension_extends x
#align valued.valued_completion_apply Valued.valuedCompletion_apply

end Valued
