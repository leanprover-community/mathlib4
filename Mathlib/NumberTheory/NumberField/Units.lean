/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import number_theory.number_field.units from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main results
* `isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if `|norm ℚ x| = 1`.
* `mem_torsion`: a unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite places of `K`.

## Tags
number field, units
 -/

set_option autoImplicit true


open scoped NumberField

noncomputable section

open NumberField Units

section Rat

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
                                   -- 🎉 no goals
#align rat.ring_of_integers.is_unit_iff Rat.RingOfIntegers.isUnit_iff

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

theorem isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  -- ⊢ |↑(↑(RingOfIntegers.norm ℚ) x)| = 1 ↔ IsUnit (↑(RingOfIntegers.norm ℚ) x)
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
  -- 🎉 no goals
#align is_unit_iff_norm isUnit_iff_norm

end IsUnit

namespace NumberField.Units

section coe

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  fun _ _ h => by rwa [SetLike.coe_eq_coe, Units.eq_iff] at h
                  -- 🎉 no goals

variable {K}

theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl

theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : (x ^ n : K) = (x : K) ^ n := by
  rw [← SubmonoidClass.coe_pow, ← val_pow_eq_pow_val]
  -- 🎉 no goals

theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (x ^ n : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  -- ⊢ ↑(MonoidHom.comp (coeHom K) (map ↑(algebraMap { x // x ∈ 𝓞 K } K))) (x ^ n)  …
  exact map_zpow _ x n
  -- 🎉 no goals

theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl

theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

open NumberField.InfinitePlace

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  -- ⊢ (∃ n, 0 < n ∧ x ^ n = 1) ↔ ∀ (φ : K →+* ℂ), ‖↑φ ↑↑x‖ = 1
  refine ⟨fun ⟨n, h_pos, h_eq⟩ φ => ?_, fun h => ?_⟩
  -- ⊢ ‖↑φ ↑↑x‖ = 1
  · refine norm_map_one_of_pow_eq_one φ.toMonoidHom (k := ⟨n, h_pos⟩) ?_
    -- ⊢ ↑↑x ^ ↑{ val := n, property := h_pos } = 1
    rw [PNat.mk_coe, ← coe_pow, h_eq, coe_one]
    -- 🎉 no goals
  · obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
    -- ⊢ ∃ n, 0 < n ∧ x ^ n = 1
    exact ⟨n, hn, by ext; rw [coe_pow, hx, coe_one]⟩
    -- 🎉 no goals

/-- Shortcut instance because Lean tends to time out before finding the general instance. -/
instance : Nonempty (torsion K) := One.nonempty

/-- The torsion subgroup is finite. -/
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  -- ⊢ Set.Finite ↑(torsion K)
  refine Set.Finite.of_finite_image ?_ ((coe_injective K).injOn _)
  -- ⊢ Set.Finite ((fun x => ↑↑x) '' ↑(torsion K))
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    -- ⊢ IsIntegral ℤ ((fun x => ↑↑x) u)
    exact u.val.prop
    -- 🎉 no goals
  · rw [← h_ua]
    -- ⊢ ‖↑φ ((fun x => ↑↑x) u)‖ ≤ 1
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)
    -- 🎉 no goals

-- a shortcut instance to stop the next instance from timing out
instance [NumberField K] : Finite (torsion K) := inferInstance

/-- The torsion subgroup is cylic. -/
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion subgroup as positive integer. -/
def torsion_order [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩

/-- If `k` does not divide `torsion_order` then there are no nontrivial roots of unity of
  order dividing `k`. -/
theorem rootsOfUnity_eq_one [NumberField K] {k : ℕ+} (hc : Nat.coprime k (torsion_order K)) :
    ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  -- ⊢ ζ ^ ↑k = 1 ↔ ζ = 1
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  -- ⊢ ζ = 1
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  -- ⊢ orderOf ζ ∣ ↑k
  · exact orderOf_dvd_of_pow_eq_one h
    -- 🎉 no goals
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    -- ⊢ orderOf { val := ζ, property := hζ } ∣ ↑(torsion_order K)
    exact orderOf_dvd_card_univ
    -- 🎉 no goals

/-- The group of roots of unity of order dividing `torsion_order` is equal to the torsion
group. -/
theorem rootsOfUnity_eq_torsion [NumberField K] :
    rootsOfUnity (torsion_order K) (𝓞 K) = torsion K := by
  ext ζ
  -- ⊢ ζ ∈ rootsOfUnity (torsion_order K) { x // x ∈ 𝓞 K } ↔ ζ ∈ torsion K
  rw [torsion, mem_rootsOfUnity]
  -- ⊢ ζ ^ ↑(torsion_order K) = 1 ↔ ζ ∈ CommGroup.torsion { x // x ∈ 𝓞 K }ˣ
  refine ⟨fun h => ?_, fun h => ?_⟩
  -- ⊢ ζ ∈ CommGroup.torsion { x // x ∈ 𝓞 K }ˣ
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    -- ⊢ ∃ n, 0 < n ∧ ζ ^ n = 1
    exact ⟨↑(torsion_order K), (torsion_order K).prop, h⟩
    -- 🎉 no goals
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) _ ⟨ζ, h⟩ _)
    -- 🎉 no goals

end torsion

end NumberField.Units
