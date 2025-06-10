/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is nontrivial cyclic, a
valuation `v : A → Γ` on a ring `A` is *discrete*, if `genLTOne Γˣ` belongs to the image, where
`genLTOne Γˣ` is the generator of `Γˣ` that is `< 1`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `genLTOne Γˣ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.


## Main Definitions
* `IsDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if `Γˣ` is cyclic and
  `genLTOne Γˣ` belongs to the image of `v`.

## TODO
* Define (pre)uniformizers for nontrivial discrete valuations.
* Relate discrete valuations and discrete valuation rings.
-/

namespace Valuation

open Function Set LinearOrderedCommGroup MonoidHomWithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ = (range₀ v)ˣ ∧ γ < 1 ∧ ↑γ ∈ range v

lemma exists_generator_lt_one [IsDiscrete v] :
    ∃ (γ : Γˣ), Subgroup.zpowers γ = (range₀ v)ˣ ∧ γ < 1 ∧ ↑γ ∈ range v :=
  IsDiscrete.exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsDiscrete.generator` is a generator of the value
group that is `< 1`. -/
noncomputable def generator [IsDiscrete v] : Γˣ := v.exists_generator_lt_one.choose

lemma generator_zpowers_eq_range₀ [IsDiscrete v] :
    (Subgroup.zpowers (generator v) : Subgroup Γˣ) =
      Subgroup.map (Units.map (range₀ v).subtype) ⊤ :=
  sorry --v.exists_generator_lt_one.choose_spec.1

lemma generator_lt_one [IsDiscrete v] : (generator v) < 1 :=
  v.exists_generator_lt_one.choose_spec.2.1

lemma generator_mem_range [IsDiscrete v] : ↑(generator v) ∈ range v :=
  v.exists_generator_lt_one.choose_spec.2.2

lemma generator_ne_zero [IsDiscrete v] : (generator v : Γ) ≠ 0 :=
  sorry

noncomputable def gen₀ [v.IsDiscrete] : range₀ v := by
  have h := v.generator_mem_range
  let a := h.choose
  have ha : v a = v.generator := h.choose_spec
  use generator v
  rw [← ha]
  apply mem_range₀

noncomputable def gen₀' [v.IsDiscrete] : (range₀ v)ˣ := by
  apply Units.mk0 (v.gen₀)
  sorry

lemma gen₀_coe_eq_generator [v.IsDiscrete] :
    Units.map (range₀ v).subtype (v.gen₀') = v.generator := by
  simp only [gen₀', gen₀]
  exact Units.eq_iff.mp rfl

lemma IsDiscrete.cyclic_value_group' [IsDiscrete v] : IsCyclic (range₀ v)ˣ := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  use v.gen₀'
  let H := Subgroup.map (Units.map (range₀ v).subtype) ⊤
  have : IsCyclic H := by
    rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
    use v.generator
    rw [v.generator_zpowers_eq_range₀]
  sorry

lemma IsDiscrete.cyclic_value_group [IsDiscrete v] : IsCyclic (range₀ v)ˣ := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  -- obtain ⟨a, ha⟩ := v.generator_mem_range
  set γ := v.generator with hγ
  rcases γ  with ⟨x, _, _, _⟩
  have hx : x ∈ range v := sorry
  rcases hx with ⟨b, hb⟩
  set y : range₀ v := by
    refine ⟨x, ?_⟩
    rw [← hb]
    apply mem_range₀ with hy
  refine ⟨Units.mk0 y ?_, ?_⟩
  · sorry
  ext d
  simp
  have hd := d.2
  rw [hy]


  rw [generator_zpowers_eq_range₀ v]






  -- set x : (range₀ v)ˣ := by
  --   rw [← generator_zpowers_eq_range₀]
  --   use v.generator.1
  --   simp with hx
  -- -- use x
  -- -- rw [hx]
  -- refine ⟨x.1, ?_⟩
  -- convert generator_zpowers_eq_range₀ v
  -- simp at hx



  -- rw [generator_zpowers_eq_range₀]



lemma IsDiscrete.nontrivial_value_group [IsDiscrete v] : Nontrivial Γˣ :=
  ⟨1, generator v, ne_of_gt <| generator_lt_one v⟩

variable {K : Type*} [Field K]

/-- A discrete valuation on a field `K` is surjective. -/
-- lemma IsDiscrete.surj (w : Valuation K Γ) [IsDiscrete w] : Surjective w := by
--   intro c
--   by_cases hc : c = 0
--   · exact ⟨0, by simp [hc]⟩
--   obtain ⟨π, hπ_gen, hπ_lt_one, a, ha⟩ := w.exists_generator_lt_one
--   set u : Γˣ := Units.mk0 c hc with hu
--   obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hπ_gen ▸ Subgroup.mem_top u)
--   use a^k
--   rw [map_zpow₀, ha]
--   norm_cast
--   rw [hk, hu, Units.val_mk0]
--
-- /-- A valuation on a field `K` is discrete if and only if it is surjective. -/
-- lemma isDiscrete_iff_surjective (w : Valuation K Γ) [IsCyclic Γˣ] [Nontrivial Γˣ] :
--     IsDiscrete w ↔ Surjective w := by
--   refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨LinearOrderedCommGroup.genLTOne Γˣ,
--     by simp, ?_, by apply h⟩⟩
--   simpa using (⊤ : Subgroup Γˣ).genLTOne_lt_one

instance [hv : IsDiscrete v] : IsNontrivial v where
  exists_val_nontrivial := by
    obtain ⟨γ, _, _, x, hx_v⟩ := hv
    exact ⟨x, hx_v ▸ ⟨Units.ne_zero γ, ne_of_lt (by norm_cast)⟩⟩

end Valuation
