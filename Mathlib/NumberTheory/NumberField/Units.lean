/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot

! This file was ported from Lean 3 source module number_theory.number_field.units
! leanprover-community/mathlib commit 00f91228655eecdcd3ac97a7fd8dbcb139fe990a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main results
* `isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if `|norm ℚ x| = 1`

## Tags
number field, units
 -/


open scoped NumberField

noncomputable section

open NumberField Units

section Rat

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
#align rat.ring_of_integers.is_unit_iff Rat.RingOfIntegers.isUnit_iff

end Rat

variable (K : Type _) [Field K]

section IsUnit

attribute [local instance] NumberField.ringOfIntegersAlgebra

variable {K}

theorem isUnit_iff_norm [NumberField K] (x : 𝓞 K) :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
#align is_unit_iff_norm isUnit_iff_norm

end IsUnit

namespace NumberField.units

section coe

/-- The `MonoidHom` from the group of units `(𝓞 K)ˣ` to the field `K`. -/
def coe_to_field : (𝓞 K)ˣ →* K := (Units.coeHom K).comp (map (algebraMap (𝓞 K) K))

theorem coe_to_field_injective : Function.Injective (coe_to_field K) :=
  fun _ _ h => Units.eq_iff.mp (SetCoe.ext h)

/-- There is a natural coercion from `(𝓞 K)ˣ` to `(𝓞 K)` and then from `(𝓞 K)` to `K` but it is
useful to also have a direct one from `(𝓞 K)ˣ` to `K`. -/
instance : Coe (𝓞 K)ˣ K := ⟨coe_to_field K⟩

@[ext]
theorem ext {x y : (𝓞 K)ˣ} (h : (x : K) = y) : x = y := (coe_to_field_injective K).eq_iff.mp h

end coe

open NumberField.InfinitePlace

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, h_pos, h_eq⟩ φ => ?_, fun h => ?_⟩
  · refine norm_map_one_of_pow_eq_one φ.toMonoidHom (k := ⟨n, h_pos⟩) ?_
    rw [PNat.mk_coe, ← map_pow, h_eq, map_one]
  · obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
    exact ⟨n, hn, by ext; rwa [map_pow, map_one]⟩
end torsion

instance : Nonempty (torsion K) := ⟨1⟩

/-- The torsion subgroup is finite. -/
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ ((coe_to_field_injective K).injOn _)
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/-- The torsion subgroup is cylic. -/
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion subgroup as positive integer. -/
def torsion_order [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩

/-- If `k` does not divide `torsion_order` then there are no nontrivial roots of unity of
  order dividing `k`. -/
theorem rootsOfUnity_eq_one [NumberField K] {k : ℕ+} (hc : Nat.coprime k (torsion_order K)) :
    ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    exact orderOf_dvd_card_univ

/-- The group of roots of unity of order dividing `torsion_order` is equal to the torsion
group. -/
theorem rootsOfUnity_eq_torsion [NumberField K] :
    rootsOfUnity (torsion_order K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨↑(torsion_order K), (torsion_order K).prop, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) ⟨ζ, h⟩ _ _)

end NumberField.units
