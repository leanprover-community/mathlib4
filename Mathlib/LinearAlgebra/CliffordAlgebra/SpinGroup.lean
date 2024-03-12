/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Utensil Song, Eric Wieser
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-!
# The Pin group and the Spin group

In this file we define `lipschitzGroup`, `pinGroup` and `spinGroup` and show they form a group.

## Main definitions

* `lipschitzGroup`: the Lipschitz group with a quadratic form.
* `pinGroup`: the Pin group defined as the infimum of `lipschitzGroup` and `unitary`.
* `spinGroup`: the Spin group defined as the infimum of `pinGroup` and `CliffordAlgebra.even`.

## Implementation Notes

Here are some discussion about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

The definition of the Lipschitz group `{𝑥 ∈ 𝐶𝑙(𝑉,𝑞) │ 𝑥 𝑖𝑠 𝑖𝑛𝑣𝑒𝑟𝑡𝑖𝑏𝑙𝑒 𝑎𝑛𝑑 𝑥𝑣𝑥⁻¹∈ 𝑉}` is given by:
• [fulton2004][], Chapter 20.
• https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group
But they presumably form a group only in finite dimensions. So we define `lipschitzGroup` with
closure of all the invertible elements in the form of `ι Q m`, and we show this definition is
at least as large as the other definition (See `lipschitzGroup.mem_conjAct_le` and
`lipschitzGroup.mem_involute_le`). The reverse statement presumably being true only in finite
dimensions.

## TODO

Try to show the reverse statement is true in finite dimensions.
-/

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `lipschitzGroup` is the subgroup closure of all the invertible elements in the form of `ι Q m`
where `ι` is the canonical linear map `M →ₗ[R] CliffordAlgebra Q`. -/
def lipschitzGroup (Q : QuadraticForm R M) : Subgroup (CliffordAlgebra Q)ˣ :=
  Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)
#align lipschitz lipschitzGroup

namespace lipschitzGroup

/-- If x is in `lipschitzGroup Q`, then `(ι Q).range` is closed under twisted conjugation.
The reverse statement presumably being true only in finite dimensions.-/
theorem mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    [Invertible (2 : R)] :
    ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | Hk x hx =>
    obtain ⟨a, ha⟩ := hx
    rintro y ⟨z, ⟨⟨b, rfl⟩, hz⟩⟩
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    rw [LinearMap.mem_range]
    rw [DistribMulAction.toLinearMap_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct] at hz
    suffices ∃ y : M, ι Q y = ι Q a * ι Q b * ⅟ (ι Q a) by simp_all only [invOf_units]
    rw [ι_mul_ι_mul_invOf_ι Q a b]
    use ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b)
  | Hk_inv x hx =>
    obtain ⟨a, ha⟩ := hx
    rintro y ⟨z, ⟨⟨b, rfl⟩, hz⟩⟩
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    rw [LinearMap.mem_range]
    rw [DistribMulAction.toLinearMap_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hz
    suffices ∃ y : M, ι Q y = ⅟ (ι Q a) * ι Q b * ι Q a by simp_all only [invOf_units]
    rw [invOf_ι_mul_ι_mul_ι Q a b]
    use ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b)
  | H1 => simp only [ConjAct.toConjAct_one, (one_smul _ (LinearMap.range (ι Q))), le_refl]
  | Hmul x y _ _ hx1 hy1 =>
    rw [ConjAct.toConjAct_mul]
    rintro m ⟨a, ⟨b, rfl⟩, ha⟩
    simp only [ConjAct.units_smul_def, DistribMulAction.toLinearMap_apply, Units.val_mul,
      mul_inv_rev] at ha
    have hb : ↑x * (↑y * (ι Q b) * ↑y⁻¹) * ↑x⁻¹ = m := by
      simp only [mul_assoc, ← ha, map_mul, ConjAct.ofConjAct_toConjAct, Units.val_mul, mul_inv_rev]
    have hy2 : ↑y * (ι Q) b * ↑y⁻¹ ∈ ConjAct.toConjAct y • LinearMap.range (ι Q) := by
      simp only [HSMul.hSMul, SMul.smul, exists_exists_eq_and, exists_apply_eq_apply,
        Submodule.mem_map, LinearMap.mem_range, DistribMulAction.toLinearMap_apply,
        ConjAct.ofConjAct_toConjAct]
    specialize hy1 hy2
    have hx2 : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ ∈ ConjAct.toConjAct x • LinearMap.range (ι Q) := by
      simp only [HSMul.hSMul, SMul.smul, Units.mul_left_inj, Units.mul_right_inj,
        exists_exists_eq_and, Submodule.mem_map, LinearMap.mem_range,
        DistribMulAction.toLinearMap_apply, ConjAct.ofConjAct_toConjAct]
      exact hy1
    specialize hx1 hx2
    rwa [hb] at hx1
#align mem_lipschitz_conj_act_le lipschitzGroup.mem_conjAct_le

/-- This is another version of `lipschitzGroup.mem_conj_act_le` which uses `involute`.-/
theorem mem_involute_le [Invertible (2 : R)]
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (b : M) :
      involute (Q := Q) ↑x * ι Q b * ↑x⁻¹ ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | Hk x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    rw [LinearMap.mem_range, ← invOf_units x]
    simp_rw [← ha, involute_ι]
    refine ⟨-((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b), ?_⟩
    simp only [map_neg, neg_mul, ι_mul_ι_mul_invOf_ι Q a b]
  | Hk_inv x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    letI := invertibleNeg (ι Q a)
    letI := Invertible.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q) (ι Q a)
    rw [LinearMap.mem_range, ← invOf_units x, inv_inv]
    simp_rw [← ha, map_invOf, involute_ι, invOf_neg]
    refine ⟨-((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b), ?_⟩
    simp only [map_neg, neg_mul, invOf_ι_mul_ι_mul_ι Q a b]
  | H1 => simp only [Units.val_one, map_one, one_mul, inv_one, mul_one, LinearMap.mem_range,
      exists_apply_eq_apply, forall_const]
  | Hmul y z _ _ hy hz =>
    simp only [Units.val_mul, map_mul, mul_inv_rev, LinearMap.mem_range]
    let ⟨z', hz'⟩ := hz b
    let ⟨y', hy'⟩ := hy z'
    suffices
        ∃ c : M, (ι Q) c = involute (Q := Q) ↑y * (involute (Q := Q) ↑z * (ι Q) b * ↑z⁻¹) * ↑y⁻¹ by
      obtain ⟨p, hp⟩ := this
      refine' ⟨p, by simp only [hp, mul_assoc]⟩
    rw [← hz']
    use y'

#align mem_lipschitz_involute_le lipschitzGroup.mem_involute_le

theorem coe_mem_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔
    x ∈ lipschitzGroup Q := by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply, exists_prop]
  norm_cast
  exact exists_eq_right
#align coe_mem_lipschitz_iff_mem lipschitzGroup.coe_mem_iff_mem

end lipschitzGroup

/-- `pinGroup Q` is defined as the infimum of `lipschitzGroup Q` and `unitary (CliffordAlgebra Q)`.
See `mem_iff`. -/
def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _
#align pin_group pinGroup

namespace pinGroup

/-- An element is in `pinGroup Q` if and only if it is in `lipschitzGroup Q` and `unitary`. -/
theorem mem_iff {x : CliffordAlgebra Q} :
    x ∈ pinGroup Q ↔
      x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧
        x ∈ unitary (CliffordAlgebra Q) :=
  Iff.rfl
#align pin_group.mem_iff pinGroup.mem_iff

theorem mem_lipschitzGroup {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1
#align pin_group.mem_lipschitz pinGroup.mem_lipschitzGroup

theorem mem_unitary {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ unitary (CliffordAlgebra Q) :=
  hx.2
#align pin_group.mem_unitary pinGroup.mem_unitary

theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ pinGroup Q ↔ x ∈ lipschitzGroup Q ∧ ↑x ∈ unitary (CliffordAlgebra Q) := by
  rw [mem_iff, lipschitzGroup.coe_mem_iff_mem]
#align pin_group.units_mem_iff pinGroup.units_mem_iff

theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q) :
    x ∈ lipschitzGroup Q :=
  (units_mem_iff.1 hx).1
#align pin_group.units_mem_lipschitz pinGroup.units_mem_lipschitzGroup

/-- If x is in `pinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) :=
  lipschitzGroup.mem_conjAct_le (units_mem_lipschitzGroup hx)
#align pin_group.units_mem_conj_act_le pinGroup.units_mem_conjAct_le

/-- This is another version of `units_mem_conjAct_le` which uses `involute`. -/
theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.mem_involute_le (units_mem_lipschitzGroup hx) y
#align pin_group.units_mem_involute_act_le pinGroup.units_mem_involute_act_le

@[simp]
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x * x = 1 :=
  hx.2.1
#align pin_group.star_mul_self_of_mem pinGroup.star_mul_self_of_mem

@[simp]
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : x * star x = 1 :=
  hx.2.2
#align pin_group.mul_star_self_of_mem pinGroup.mul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x ∈ pinGroup Q := by
  rw [mem_iff] at hx ⊢
  refine' ⟨_, unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, _hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply, exists_prop]
  refine' ⟨star y, _, by simp only [hy₂, Units.coe_star]⟩
  rw [← hy₂] at hx₃
  have hy₃ : y * star y = 1 := by
    rw [← Units.eq_iff]
    simp only [hx₃, Units.val_mul, Units.coe_star, Units.val_one]
  apply_fun fun x => y⁻¹ * x at hy₃
  simp only [inv_mul_cancel_left, mul_one] at hy₃
  simp only [hy₃, hy₁, inv_mem_iff]
#align pin_group.star_mem pinGroup.star_mem

/-- An element is in `pinGroup Q` if and only if `star x` is in `pinGroup Q`.
See `star_mem` for only one direction. -/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ pinGroup Q ↔ x ∈ pinGroup Q := by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align pin_group.star_mem_iff pinGroup.star_mem_iff

instance : Star (pinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align pin_group.coe_star pinGroup.coe_star

theorem coe_star_mul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop
#align pin_group.coe_star_mul_self pinGroup.coe_star_mul_self

theorem coe_mul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop
#align pin_group.coe_mul_star_self pinGroup.coe_mul_star_self

@[simp]
theorem star_mul_self (x : pinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_mul_self x
#align pin_group.star_mul_self pinGroup.star_mul_self

@[simp]
theorem mul_star_self (x : pinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_mul_star_self x
#align pin_group.mul_star_self pinGroup.mul_star_self

/-- `pinGroup Q` forms a group where the inverse is `star`. -/
instance : Group (pinGroup Q) where
  __ : Monoid (pinGroup Q) := inferInstance
  inv := star
  mul_left_inv := star_mul_self

instance : StarMul (pinGroup Q) where
  star_involutive _ := Subtype.ext <| star_involutive _
  star_mul _ _ := Subtype.ext <| star_mul _ _

instance : Inhabited (pinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : pinGroup Q) : star x = x⁻¹ :=
  rfl
#align pin_group.star_eq_inv pinGroup.star_eq_inv

theorem star_eq_inv' : (star : pinGroup Q → pinGroup Q) = Inv.inv :=
  rfl
#align pin_group.star_eq_inv' pinGroup.star_eq_inv'

/-- The elements in `pinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
def toUnits : pinGroup Q →* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl
#align pin_group.to_units pinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : pinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun _x _y h => Subtype.ext <| Units.ext_iff.mp h
#align pin_group.to_units_injective pinGroup.toUnits_injective

end pinGroup

end Pin

section Spin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`.
See `mem_iff`. -/
def spinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid
#align spin_group spinGroup

namespace spinGroup

/-- An element is in `spinGroup Q` if and only if it is in `pinGroup Q` and `even Q`. -/
theorem mem_iff {x : CliffordAlgebra Q} : x ∈ spinGroup Q ↔ x ∈ pinGroup Q ∧ x ∈ even Q :=
  Iff.rfl
#align spin_group.mem_iff spinGroup.mem_iff

theorem mem_pin {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ pinGroup Q :=
  hx.1
#align spin_group.mem_pin spinGroup.mem_pin

theorem mem_even {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ even Q :=
  hx.2
#align spin_group.mem_even spinGroup.mem_even

theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) :
    x ∈ lipschitzGroup Q :=
  pinGroup.units_mem_lipschitzGroup (mem_pin hx)
#align spin_group.units_mem_lipschitz spinGroup.units_mem_lipschitzGroup

/-- If x is in `spinGroup Q`, then `involute x` is equal to x.-/
theorem mem_involute_eq {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : involute x = x :=
  involute_eq_of_mem_even (mem_even hx)
#align spin_group.mem_involute_eq spinGroup.mem_involute_eq

theorem units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) (y : M) :
    involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ = ConjAct.toConjAct x • (ι Q y) := by
  rw [mem_involute_eq hx, @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct]
#align spin_group.units_involute_act_eq_conj_act spinGroup.units_involute_act_eq_conjAct

/- If x is in `spinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) :=
  lipschitzGroup.mem_conjAct_le (units_mem_lipschitzGroup hx)
#align spin_group.units_mem_conj_act_le spinGroup.units_mem_conjAct_le

/- This is another version of `units_mem_conjAct_le` which uses `involute`.-/
theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.mem_involute_le (units_mem_lipschitzGroup hx) y
#align spin_group.units_mem_involute_act_le spinGroup.units_mem_involute_act_le

@[simp]
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x * x = 1 :=
  hx.1.2.1
#align spin_group.star_mul_self_of_mem spinGroup.star_mul_self_of_mem

@[simp]
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x * star x = 1 :=
  hx.1.2.2
#align spin_group.mul_star_self_of_mem spinGroup.mul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x ∈ spinGroup Q := by
  rw [mem_iff] at hx ⊢
  cases' hx with hx₁ hx₂
  refine' ⟨pinGroup.star_mem hx₁, _⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]
#align spin_group.star_mem spinGroup.star_mem

/-- An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`.
See `star_mem` for only one direction.
-/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ spinGroup Q ↔ x ∈ spinGroup Q := by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align spin_group.star_mem_iff spinGroup.star_mem_iff

instance : Star (spinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
theorem coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align spin_group.coe_star spinGroup.coe_star

theorem coe_star_mul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop
#align spin_group.coe_star_mul_self spinGroup.coe_star_mul_self

theorem coe_mul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop
#align spin_group.coe_mul_star_self spinGroup.coe_mul_star_self

@[simp]
theorem star_mul_self (x : spinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_mul_self x
#align spin_group.star_mul_self spinGroup.star_mul_self

@[simp]
theorem mul_star_self (x : spinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_mul_star_self x
#align spin_group.mul_star_self spinGroup.mul_star_self

/-- `spinGroup Q` forms a group where the inverse is `star`. -/
instance : Group (spinGroup Q) where
  __ : Monoid _ := inferInstance
  inv := star
  mul_left_inv := star_mul_self

instance : StarMul (spinGroup Q) where
  star_involutive _ := Subtype.ext <| star_involutive _
  star_mul _ _ := Subtype.ext <| star_mul _ _

instance : Inhabited (spinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : spinGroup Q) : star x = x⁻¹ :=
  rfl
#align spin_group.star_eq_inv spinGroup.star_eq_inv

theorem star_eq_inv' : (star : spinGroup Q → spinGroup Q) = Inv.inv :=
  rfl
#align spin_group.star_eq_inv' spinGroup.star_eq_inv'

/-- The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
def toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl
#align spin_group.to_units spinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : spinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun _x _y h => Subtype.ext <| Units.ext_iff.mp h
#align spin_group.to_units_injective spinGroup.toUnits_injective

end spinGroup

end Spin
