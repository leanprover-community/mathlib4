/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Units of restricted products

This file contains results about the units of a restricted product. The restricted
product `Πʳ i : ι, [R i, B i]_[𝓕]` of a family of types `R` with respect to a family of
subsets `B` along a filter `𝓕` is defined in `Mathlib.Topology.Algebra.RestrictedProduct.Basic`.
Here, we give conditions that characterize when an element of the restricted product is a unit,
and provide an isomorphism between the units of the restricted product and the restricted product
of the units.

## Main definitions

* `RestrictedProduct.unitsEquiv`: the (monoid) isomorphism between `(Πʳ i, [R i, B i]_[𝓕])ˣ`
  and `Πʳ i, [(R i)ˣ, (B i).units]_[𝓕]`.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} [∀ i, Monoid (R i)]
variable {S : ι → Type*} [Π i, SetLike (S i) (R i)] [∀ (i : ι), SubmonoidClass (S i) (R i)]
variable {B : Π i, S i}
variable {𝓕 : Filter ι}

theorem isUnit_of_eventually_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : ∀ i, IsUnit (x i))
    (hxr : ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i)) :
    IsUnit x := by
  rw [isUnit_iff_exists]
  use .mk (fun i ↦ (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]

theorem eventualy_isUnit_of_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) :
    (∀ i, IsUnit (x i)) ∧ ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i) := by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb ↦ ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩

theorem isUnit_iff {x : Πʳ i, [R i, B i]_[𝓕]} :
    IsUnit x ↔ (∀ i, IsUnit (x i)) ∧ ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i)  :=
  ⟨eventualy_isUnit_of_isUnit, fun h ↦ isUnit_of_eventually_isUnit h.1 h.2⟩

/-- The homomorphism from the units of a restricted product to the regular product of unit. -/
def coeUnits : Πʳ i, [R i, B i]_[𝓕]ˣ →* (i : ι) → (R i)ˣ :=
  MulEquiv.piUnits.toMonoidHom.comp <| Units.map coeMonoidHom

/-- Constructs a unit in a restricted product `Πʳ i, [R i, B i]_[𝓕]` given an element `x` of
the usual product and the condition that `x` is eventually in the units of `B i` along `𝓕`. -/
def mkUnit (x : Π i, (R i)ˣ) (hx : ∀ᶠ i in 𝓕, x i ∈ (Submonoid.ofClass (B i)).units) :
    Πʳ i, [R i, B i]_[𝓕]ˣ where
  val := ⟨fun i ↦ (x i).1, by filter_upwards [hx] using fun i hi ↦ hi.1⟩
  inv := ⟨fun i ↦ (x i)⁻¹.1, by filter_upwards [hx] using fun i hi ↦ hi.2⟩
  val_inv := by ext; simp
  inv_val := by ext; simp

variable (R) in
/-- The ring isomorphism between the units of a restricted product `Πʳ i, [R i, B i]_[𝓕]` and
the restricted product of `(R i)ˣ` with respect to `(B i)ˣ`. -/
def unitsEquiv : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓕] where
  toFun x := ⟨coeUnits x, by filter_upwards [x.val.2, x.inv.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
  invFun y := mkUnit y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma unitsEquiv_apply (i : ι) (x : Πʳ i, [R i, B i]_[𝓕]ˣ) :
    (unitsEquiv R x i) = x.1 i := rfl

@[simp] lemma coe_unitsEquiv_apply (x : Πʳ i, [R i, B i]_[𝓕]ˣ) (i : ι) :
    (unitsEquiv R x).1 i = unitsEquiv R x i := rfl

end RestrictedProduct
