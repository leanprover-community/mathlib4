/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Valuation.Basic

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/


universe u v w

namespace Valuation

section Ring

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)

/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
def integer : Subring R where
  carrier := { x | v x ≤ 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, _root_.map_mul, mul_le_one' hx hy]
  zero_mem' := by simp only [Set.mem_setOf_eq, _root_.map_zero, zero_le']
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_setOf_eq] at hx; simpa only [Set.mem_setOf_eq, map_neg]

lemma mem_integer_iff (r : R) : r ∈ v.integer ↔ v r ≤ 1 := by rfl

end Ring

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
variable (O : Type w) [CommRing O] [Algebra O R]

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r

-- typeclass shortcut
instance : Algebra v.integer R :=
  Algebra.ofSubring v.integer

theorem integer.integers : v.Integers v.integer :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

namespace Integers

variable {v O}

theorem one_of_isUnit' {x : O} (hx : IsUnit x) (H : ∀ x, v (algebraMap O R x) ≤ 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
  le_antisymm (H _) <| by
    rw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul]
    exact mul_le_mul_left' (H (u⁻¹ : Units O)) _

theorem one_of_isUnit (hv : Integers v O) {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  one_of_isUnit' hx hv.map_le_one

/--
Let `O` be the integers of the valuation `v` on some commutative ring `R`. For every element `x` in
`O`, `x` is a unit in `O` if and only if the image of `x` in `R` is a unit and has valuation 1.
-/
theorem isUnit_of_one (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
    (hvx : v (algebraMap O R x) = 1) : IsUnit x :=
  let ⟨u, hu⟩ := hx
  have h1 : v u ≤ 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) ≤ 1 := by
    rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
  ⟨⟨r1, r2, hv.1 <| by rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.mul_inv],
      hv.1 <| by rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.inv_mul]⟩,
    hv.1 <| hr1.trans hu⟩

theorem le_of_dvd (hv : Integers v O) {x y : O} (h : x ∣ y) :
    v (algebraMap O R y) ≤ v (algebraMap O R x) := by
  let ⟨z, hz⟩ := h
  rw [← mul_one (v (algebraMap O R x)), hz, RingHom.map_mul, v.map_mul]
  exact mul_le_mul_left' (hv.2 z) _

end Integers

end CommRing

section Field

variable {F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {O : Type w} [CommRing O] [Algebra O F]

namespace Integers

theorem dvd_of_le (hv : Integers v O) {x y : O}
    (h : v (algebraMap O F x) ≤ v (algebraMap O F y)) : y ∣ x :=
  by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
        hv.1 <|
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y ≠ 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) ≤ 1 := by
      rw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul]
      exact mul_le_mul_left' h _
    let ⟨z, hz⟩ := hv.3 this
    ⟨z, hv.1 <| ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

theorem dvd_iff_le (hv : Integers v O) {x y : O} :
    x ∣ y ↔ v (algebraMap O F y) ≤ v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩

theorem le_iff_dvd (hv : Integers v O) {x y : O} :
    v (algebraMap O F x) ≤ v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩

/--
This is the special case of `Valuation.Integers.isUnit_of_one` when the valuation is defined
over a field. Let `v` be a valuation on some field `F` and `O` be its integers. For every element
`x` in `O`, `x` is a unit in `O` if and only if the image of `x` in `F` has valuation 1.
-/
theorem isUnit_of_one' (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1) : IsUnit x := by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]

theorem eq_algebraMap_or_inv_eq_algebraMap (hv : Integers v O) (x : F) :
    ∃ a : O, x = algebraMap O F a ∨ x⁻¹ = algebraMap O F a := by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]

lemma isPrincipal_iff_exists_isGreatest (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ ∃ x, IsGreatest ((v ∘ algebraMap O F) '' I) x := by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx, Ideal.mem_span_singleton_self]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    constructor <;> intro hb
    · exact dvd_of_le hv (hx.right <| Set.mem_image_of_mem _ hb)
    · obtain ⟨c, rfl⟩ := hb
      exact Ideal.mul_mem_right c I ha

lemma not_denselyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : Integers v O) :
    ¬ DenselyOrdered (Set.range v) := by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := (v ∘ algebraMap O F) ⁻¹' Set.Iio (1 : Γ₀)
    add_mem' := by
      intro a b ha hb
      simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Iio, smul_eq_mul, _root_.map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  } with hI
  obtain ⟨x, hx⟩ : ∃ x, IsGreatest ((v ∘ algebraMap O F) '' I) x := by
    rw [← hv.isPrincipal_iff_exists_isGreatest]
    exact IsPrincipalIdealRing.principal I
  simp only [hI, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk,
    AddSubsemigroup.coe_set_mk, Set.image_preimage_eq_inter_range] at hx
  have := hx.left
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_range, Function.comp_apply] at this
  obtain ⟨hx', y, rfl⟩ := this
  rw [← v.map_one] at hx'
  obtain ⟨⟨z, hzv⟩, hz, hz'⟩ := H.dense ⟨v (algebraMap O F y), Set.mem_range_self _⟩
    ⟨v 1, Set.mem_range_self _⟩ hx'
  simp only [Set.mem_range] at hzv
  obtain ⟨z, rfl⟩ := hzv
  have := hx.right
  rw [mem_upperBounds] at this
  refine (this _ ?_).not_lt hz
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_range, Function.comp_apply, and_imp,
    forall_exists_index] at this
  specialize this (v z) (by simpa using hz')
  refine ⟨?_, ?_⟩
  · simpa using hz'
  · obtain ⟨a, rfl⟩ := hv.exists_of_le_one (by simpa using hz'.le)
    simp

-- TODO: isPrincipalIdealRing_iff_not_denselyOrdered when MulArchimedean

end Integers

end Field

end Valuation
