/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/
-- This file is mathported from https://github.com/leanprover-community/mathlib/pull/16040/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

#align_import main

/-!
# The Pin group and the Spin group

In this file we define `lipschitz`, `pin_group` and `spin_group` and show they form a group.

## Main definitions

* `lipschitz`: the Lipschitz group with a quadratic form.
* `pin_group`: the Pin group defined as the infimum of `lipschitz` and `unitary`.
* `spin_group`: the Spin group defined as the infimum of `pin_group` and `clifford.even`.

## Implementation Notes

Here are some discussion about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

The definition of the Lipschitz group `{𝑥 ∈ 𝐶𝑙(𝑉,𝑞) │ 𝑥 𝑖𝑠 𝑖𝑛𝑣𝑒𝑟𝑡𝑖𝑏𝑙𝑒 𝑎𝑛𝑑 𝑥𝑣𝑥⁻¹∈ 𝑉}` is given by:
• Fulton, W. and Harris, J., 2004. Representation theory. New York: Springer, p.chapter 20.
• https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group
But they presumably form a group only in finite dimensions. So we define `lipschitz` with closure of
all the elements in the form of `ι Q m`, and we show this definition is at least as large as the
other definition (See `mem_lipschitz_conj_act_le` and `mem_lipschitz_involute_le`). The reverse
statement presumably being true only in finite dimensions.

## TODO

Try to show the reverse statement is true in finite dimensions.
-/


variable {R : Type _} [CommRing R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

def invertibleOfInvertibleι (m : M) [Invertible (ι Q m)] [Invertible (2 : R)] : Invertible (Q m) :=
  sorry
#align invertible_of_invertible_ι invertibleOfInvertibleι

/-- `lipschitz` is the subgroup closure of all the elements in the form of `ι Q m` where `ι`
is the canonical linear map `M →ₗ[R] clifford_algebra Q`. -/
def lipschitz (Q : QuadraticForm R M) :=
  Subgroup.closure (coe ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)
#align lipschitz lipschitz

/-- If x is in `lipschitz Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem mem_lipschitz_conjAct_le {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)]
    (hx : x ∈ lipschitz Q) : ConjAct.toConjAct x • (ι Q).range ≤ (ι Q).range :=
  by
  refine' @Subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _
  · rintro x ⟨z, hz⟩ y ⟨a, ha⟩
    simp only [SMul.smul, SetLike.mem_coe, LinearMap.mem_range, DistribMulAction.toLinearMap_apply,
      ConjAct.ofConjAct_toConjAct] at ha
    rcases ha with ⟨⟨b, hb⟩, ha1⟩
    subst hb
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz]
    rw [LinearMap.mem_range, ← ha1, ← invOf_units x]
    suffices ∃ y : M, (ι Q) y = ι Q z * (ι Q) b * ⅟ (ι Q z)
      by
      convert this
      ext1
      congr <;> simp only [hz.symm, Subsingleton.helim (congr_arg Invertible hz.symm)]
    letI := invertibleOfInvertibleι Q z
    refine' ⟨(⅟ (Q z) * QuadraticForm.polar Q z b) • z - b, (ι_mul_ι_mul_inv_of_ι Q z b).symm⟩
  · rintro x ⟨z, hz1⟩ y ⟨a, ⟨b, hb⟩, ha2⟩
    simp only [ConjAct.toConjAct_inv, DistribMulAction.toLinearMap_apply, SMul.smul,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at ha2
    subst hb
    subst ha2
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz1]
    rw [LinearMap.mem_range, ← invOf_units x]
    suffices ∃ y : M, (ι Q) y = ⅟ (ι Q z) * (ι Q) b * ι Q z
      by
      convert this
      ext1
      congr <;> simp only [hz1.symm, Subsingleton.helim (congr_arg Invertible hz1.symm)]
    letI := invertibleOfInvertibleι Q z
    refine' ⟨(⅟ (Q z) * QuadraticForm.polar Q z b) • z - b, (inv_of_ι_mul_ι_mul_ι Q z b).symm⟩
  · simp only [ConjAct.toConjAct_one, one_smul, le_refl]
  · intro x y hx1 hy1 z hz1
    simp only [ConjAct.toConjAct_mul] at hz1
    suffices (ConjAct.toConjAct x * ConjAct.toConjAct y) • (ι Q).range ≤ (ι Q).range by
      exact this hz1
    · rintro m ⟨a, ⟨b, hb⟩, ha⟩
      simp only [DistribMulAction.toLinearMap_apply, SMul.smul, ConjAct.ofConjAct_mul,
        ConjAct.ofConjAct_toConjAct, Units.val_mul, mul_inv_rev] at ha
      subst hb
      have hb : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ = m := by simp_rw [← ha, mul_assoc]
      have hy2 : ↑y * (ι Q) b * ↑y⁻¹ ∈ ConjAct.toConjAct y • (ι Q).range := by
        simp only [SMul.smul, exists_exists_eq_and, exists_apply_eq_apply, Submodule.mem_map,
          LinearMap.mem_range, DistribMulAction.toLinearMap_apply, ConjAct.ofConjAct_toConjAct]
      specialize hy1 hy2
      have hx2 : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ ∈ ConjAct.toConjAct x • (ι Q).range :=
        by
        simp only [SMul.smul, Units.mul_left_inj, Units.mul_right_inj, exists_exists_eq_and,
          Submodule.mem_map, LinearMap.mem_range, DistribMulAction.toLinearMap_apply,
          ConjAct.ofConjAct_toConjAct]
        exact hy1
      specialize hx1 hx2
      rwa [hb] at hx1
#align mem_lipschitz_conj_act_le mem_lipschitz_conjAct_le

/-- This is another version of `mem_lipschitz_conj_act_le` which uses `involute`.-/
theorem mem_lipschitz_involute_le {x : (CliffordAlgebra Q)ˣ} [Invertible (2 : R)]
    (hx : x ∈ lipschitz Q) (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ (ι Q).range :=
  by
  revert y
  refine' @Subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _
  · rintro x ⟨z, hz⟩ y
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz]
    rw [LinearMap.mem_range, ← invOf_units x]
    suffices ∃ y_1 : M, (ι Q) y_1 = -ι Q z * (ι Q) y * ⅟ (ι Q z)
      by
      convert this
      ext1
      congr
      · rw [← hz, involute_ι]
      · exact hz.symm
      · exact Subsingleton.helim (congr_arg Invertible hz.symm) _ _
    letI := invertibleOfInvertibleι Q z
    refine'
      ⟨-((⅟ (Q z) * QuadraticForm.polar Q z y) • z - y), by
        simp only [map_neg, neg_mul, ι_mul_ι_mul_inv_of_ι Q z y]⟩
  · rintro x ⟨z, hz⟩ y
    letI := x.invertible
    letI : Invertible (ι Q z) := by rwa [hz]
    letI := invertibleNeg (ι Q z)
    letI := Invertible.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q) ↑x
    rw [inv_inv, LinearMap.mem_range, ← invOf_units x, map_invOf]
    suffices ∃ y_1 : M, (ι Q) y_1 = -⅟ (ι Q z) * (ι Q) y * ι Q z
      by
      convert this
      ext1
      congr
      · rw [← invOf_neg]
        apply invertible_unique
        rw [← hz, involute_ι]
      · exact hz.symm
    letI := invertibleOfInvertibleι Q z
    refine'
      ⟨-((⅟ (Q z) * QuadraticForm.polar Q z y) • z - y), by
        simp only [map_neg, neg_mul, inv_of_ι_mul_ι_mul_ι Q z y]⟩
  ·
    simp only [Units.val_one, map_one, one_mul, inv_one, mul_one, LinearMap.mem_range,
      exists_apply_eq_apply, forall_const]
  · intro a b ha hb y
    simp only [Units.val_mul, map_mul, mul_inv_rev, LinearMap.mem_range]
    cases' hb y with c hc
    suffices ∃ y_1 : M, (ι Q) y_1 = involute ↑a * (involute ↑b * (ι Q) y * ↑b⁻¹) * ↑a⁻¹
      by
      cases' this with p hp
      refine' ⟨p, by simp only [hp, mul_assoc]⟩
    rw [← hc]
    exact ha c
#align mem_lipschitz_involute_le mem_lipschitz_involute_le

theorem coe_mem_lipschitz_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔ x ∈ lipschitz Q :=
  by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply, exists_prop]
  norm_cast
  exact exists_eq_right
#align coe_mem_lipschitz_iff_mem coe_mem_lipschitz_iff_mem

/-- `pin_group Q` is defined as the infimum of `lipschitz Q` and `unitary (clifford_algebra Q)`.
See `mem_iff`. -/
def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _
#align pin_group pinGroup

namespace pinGroup

/-- An element is in `pin_group Q` if and only if it is in `lipschitz Q` and `unitary`. -/
theorem mem_iff {x : CliffordAlgebra Q} :
    x ∈ pinGroup Q ↔
      x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧
        x ∈ unitary (CliffordAlgebra Q) :=
  Iff.rfl
#align pin_group.mem_iff pinGroup.mem_iff

theorem mem_lipschitz {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ (lipschitz Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1
#align pin_group.mem_lipschitz pinGroup.mem_lipschitz

theorem mem_unitary {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ unitary (CliffordAlgebra Q) :=
  hx.2
#align pin_group.mem_unitary pinGroup.mem_unitary

theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ pinGroup Q ↔ x ∈ lipschitz Q ∧ ↑x ∈ unitary (CliffordAlgebra Q) := by
  rw [mem_iff, coe_mem_lipschitz_iff_mem]
#align pin_group.units_mem_iff pinGroup.units_mem_iff

theorem units_mem_lipschitz {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q) : x ∈ lipschitz Q :=
  (units_mem_iff.1 hx).1
#align pin_group.units_mem_lipschitz pinGroup.units_mem_lipschitz

/-- If x is in `pin_group Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • (ι Q).range ≤ (ι Q).range :=
  mem_lipschitz_conjAct_le (units_mem_lipschitz hx)
#align pin_group.units_mem_conj_act_le pinGroup.units_mem_conjAct_le

/-- This is another version of `units_mem_conj_act_le` which uses `involute`. -/
theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ (ι Q).range :=
  mem_lipschitz_involute_le (units_mem_lipschitz hx) y
#align pin_group.units_mem_involute_act_le pinGroup.units_mem_involute_act_le

@[simp]
theorem star_hMul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x * x = 1 :=
  hx.2.1
#align pin_group.star_mul_self_of_mem pinGroup.star_hMul_self_of_mem

@[simp]
theorem hMul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : x * star x = 1 :=
  hx.2.2
#align pin_group.mul_star_self_of_mem pinGroup.hMul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x ∈ pinGroup Q :=
  by
  rw [mem_iff] at hx ⊢
  refine' ⟨_, unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, hx₂, hx₃⟩
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

/-- An element is in `pin_group Q` if and only if `star x` is in `pin_group Q`.
See `star_mem` for only one direction. -/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ pinGroup Q ↔ x ∈ pinGroup Q :=
  by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align pin_group.star_mem_iff pinGroup.star_mem_iff

instance : Star (pinGroup Q) :=
  ⟨fun x => ⟨star x, star_mem x.Prop⟩⟩

@[simp, norm_cast]
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align pin_group.coe_star pinGroup.coe_star

theorem coe_star_hMul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_hMul_self_of_mem x.Prop
#align pin_group.coe_star_mul_self pinGroup.coe_star_hMul_self

theorem coe_hMul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  hMul_star_self_of_mem x.Prop
#align pin_group.coe_mul_star_self pinGroup.coe_hMul_star_self

@[simp]
theorem star_hMul_self (x : pinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_hMul_self x
#align pin_group.star_mul_self pinGroup.star_hMul_self

@[simp]
theorem hMul_star_self (x : pinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_hMul_star_self x
#align pin_group.mul_star_self pinGroup.hMul_star_self

/-- `pin_group Q` forms a group where the inverse is `star`. -/
instance : Group (pinGroup Q) :=
  { Submonoid.toMonoid _ with
    inv := star
    hMul_left_inv := star_hMul_self }

instance : InvolutiveStar (pinGroup Q) :=
  ⟨fun _ => by ext; simp only [coe_star, star_star]⟩

instance : StarMul (pinGroup Q) :=
  ⟨fun _ _ => by ext; simp only [coe_star, Submonoid.coe_mul, star_mul]⟩

instance : Inhabited (pinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : pinGroup Q) : star x = x⁻¹ :=
  rfl
#align pin_group.star_eq_inv pinGroup.star_eq_inv

theorem star_eq_inv' : (star : pinGroup Q → pinGroup Q) = Inv.inv :=
  rfl
#align pin_group.star_eq_inv' pinGroup.star_eq_inv'

/-- The elements in `pin_group Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def toUnits : pinGroup Q →* (CliffordAlgebra Q)ˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_hMul_star_self x, coe_star_hMul_self x⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align pin_group.to_units pinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : pinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun x y h => Subtype.ext <| Units.ext_iff.mp h
#align pin_group.to_units_injective pinGroup.toUnits_injective

end pinGroup

end Pin

section Spin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `spin_group Q` is defined as the infimum of `pin_group Q` and `clifford_algebra.even Q`.
See `mem_iff`. -/
def spinGroup (Q : QuadraticForm R M) :=
  pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid
#align spin_group spinGroup

namespace spinGroup

/-- An element is in `spin_group Q` if and only if it is in `pin_group Q` and `even Q`. -/
theorem mem_iff {x : CliffordAlgebra Q} : x ∈ spinGroup Q ↔ x ∈ pinGroup Q ∧ x ∈ Even Q :=
  Iff.rfl
#align spin_group.mem_iff spinGroup.mem_iff

theorem mem_pin {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ pinGroup Q :=
  hx.1
#align spin_group.mem_pin spinGroup.mem_pin

theorem mem_even {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ Even Q :=
  hx.2
#align spin_group.mem_even spinGroup.mem_even

theorem units_mem_lipschitz {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) : x ∈ lipschitz Q :=
  pinGroup.units_mem_lipschitz (mem_pin hx)
#align spin_group.units_mem_lipschitz spinGroup.units_mem_lipschitz

/-- If x is in `spin_group Q`, then `involute x` is equal to x.-/
theorem mem_involute_eq {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : involute x = x :=
  involute_eq_of_mem_even (mem_even hx)
#align spin_group.mem_involute_eq spinGroup.mem_involute_eq

theorem units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ = ConjAct.toConjAct x • ι Q y := by
  simp_rw [SMul.smul, ConjAct.ofConjAct_toConjAct, Units.mul_left_inj, mem_involute_eq hx]
#align spin_group.units_involute_act_eq_conj_act spinGroup.units_involute_act_eq_conjAct

/-- If x is in `spin_group Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
theorem units_mem_conjAct_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • (ι Q).range ≤ (ι Q).range :=
  mem_lipschitz_conjAct_le (units_mem_lipschitz hx)
#align spin_group.units_mem_conj_act_le spinGroup.units_mem_conjAct_le

/-- This is another version of `units_mem_conj_act_le` which uses `involute`.-/
theorem units_mem_involute_act_le {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute ↑x * ι Q y * ↑x⁻¹ ∈ (ι Q).range :=
  mem_lipschitz_involute_le (units_mem_lipschitz hx) y
#align spin_group.units_mem_involute_act_le spinGroup.units_mem_involute_act_le

@[simp]
theorem star_hMul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x * x = 1 :=
  hx.1.2.1
#align spin_group.star_mul_self_of_mem spinGroup.star_hMul_self_of_mem

@[simp]
theorem hMul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x * star x = 1 :=
  hx.1.2.2
#align spin_group.mul_star_self_of_mem spinGroup.hMul_star_self_of_mem

/-- See `star_mem_iff` for both directions. -/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x ∈ spinGroup Q :=
  by
  rw [mem_iff] at hx ⊢
  cases' hx with hx₁ hx₂
  refine' ⟨pinGroup.star_mem hx₁, _⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_even_odd_iff, involute_mem_even_odd_iff, hx₂]
#align spin_group.star_mem spinGroup.star_mem

/-- An element is in `spin_group Q` if and only if `star x` is in `spin_group Q`.
See `star_mem` for only one direction.
-/
@[simp]
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ spinGroup Q ↔ x ∈ spinGroup Q :=
  by
  refine' ⟨_, star_mem⟩
  intro hx
  convert star_mem hx
  exact (star_star x).symm
#align spin_group.star_mem_iff spinGroup.star_mem_iff

instance : Star (spinGroup Q) :=
  ⟨fun x => ⟨star x, star_mem x.Prop⟩⟩

@[simp, norm_cast]
theorem coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
#align spin_group.coe_star spinGroup.coe_star

theorem coe_star_hMul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_hMul_self_of_mem x.Prop
#align spin_group.coe_star_mul_self spinGroup.coe_star_hMul_self

theorem coe_hMul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  hMul_star_self_of_mem x.Prop
#align spin_group.coe_mul_star_self spinGroup.coe_hMul_star_self

@[simp]
theorem star_hMul_self (x : spinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_hMul_self x
#align spin_group.star_mul_self spinGroup.star_hMul_self

@[simp]
theorem hMul_star_self (x : spinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_hMul_star_self x
#align spin_group.mul_star_self spinGroup.hMul_star_self

/-- `spin_group Q` forms a group where the inverse is `star`. -/
instance : Group (spinGroup Q) :=
  { Submonoid.toMonoid _ with
    inv := star
    hMul_left_inv := star_hMul_self }

instance : InvolutiveStar (spinGroup Q) :=
  ⟨fun _ => by ext; simp only [coe_star, star_star]⟩

instance : StarMul (spinGroup Q) :=
  ⟨fun _ _ => by ext; simp only [coe_star, Submonoid.coe_mul, star_mul]⟩

instance : Inhabited (spinGroup Q) :=
  ⟨1⟩

theorem star_eq_inv (x : spinGroup Q) : star x = x⁻¹ :=
  rfl
#align spin_group.star_eq_inv spinGroup.star_eq_inv

theorem star_eq_inv' : (star : spinGroup Q → spinGroup Q) = Inv.inv :=
  rfl
#align spin_group.star_eq_inv' spinGroup.star_eq_inv'

/-- The elements in `spin_group Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_hMul_star_self x, coe_star_hMul_self x⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align spin_group.to_units spinGroup.toUnits

theorem toUnits_injective : Function.Injective (toUnits : spinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun x y h => Subtype.ext <| Units.ext_iff.mp h
#align spin_group.to_units_injective spinGroup.toUnits_injective

end spinGroup

end Spin
