/-
Copyright (c) 2025 Antoine Chambert-Loir and Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Filippo A. E. Nuccio
-/

-- import Mathlib.Algebra.Group.Submonoid.Defs
-- import Mathlib.Algebra.Group.WithOne.Basic
-- import Mathlib.Algebra.GroupWithZero.Units.Basic
-- import Mathlib.Tactic.NthRewrite
-- import Mathlib.Tactic.Abel
-- import Mathlib.Algebra.Group.Submonoid.Basic
-- import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Range of MonoidHomWithZero
Given a function `f : A → B` whose codomain `B` is a `GroupWithZero`, we define the
type `range₀`, by endowing the invertible elements in the range of `f` (i.e., all non-zero elements)
with a `0` (inherited from that of `B`): it is a `GroupWithZero` and if `B` is commutative, then
`range₀ f` is also commutative and can be described more explicitly
(see `MonoidHomWithZero.mem_range₀_iff_of_comm`).

## Main Results
* `range₀ f` is the smallest submonoid with zero containing the range of `f`;
* `range₀ f` is a `CancelCommMonoidWithZero`;
* `range₀ f` is a `GroupWithZero`;
* When `A` is a monoid with zero and `f` is a homomorphism of monoids with zero, `range₀ f` can be
explicitely descibed as the elements that are ratios of terms in `range f` , see
`MonoidHomWithZero.mem_range₀_iff_of_comm`.

## Implementation details
The definition of `range₀` (as a `Submonoid B`) simply requires that `B` be a nontrivial
`CancelMonoidWithZero`, and no assumption neither on `A` nor on `f` is needed; that `B` is a
`GroupWithZero` would only be needed to provide an instance of `GroupWithZero (range₀ f)`, yet
we choose to assume `GroupWithZero B` instead of `MonoidWithZero B` from the start, because
otherwise it would *not* be true that `range f` is contained in `range₀ f`, potentially leading to
some confusion.

Commutativity of `B` and compatiblity of `f` with the monoidal structures is only required to
provide the explicit description of `range₀ f` in `MonoidHomWithZero.mem_range₀_iff_of_comm`.
-/

namespace MonoidHomWithZero

open Set

variable {A B F : Type*} [FunLike F A B] (f : F)

section GroupWithZero

variable  [GroupWithZero B]

variable [MonoidWithZero A] /- [Nontrivial A]  -/[MonoidWithZeroHomClass F A B]

/-- For a map with codomain a `MonoidWithZero`, this is a smallest
`GroupWithZero`, that contains the invertible elements in the image. See
`MonoidHomWithZero.mem_range₀_iff_of_comm` for another characterization of `range₀ f` when `B` is
commutative. -/
def Valuation.valueMonoid :
  Submonoid Bˣ where
  carrier := ((↑)⁻¹' (range f))
  mul_mem' {b b'} hb hb' := by
    simp at hb hb' ⊢
    obtain ⟨y, hy⟩ := hb
    obtain ⟨y', hy'⟩ := hb'
    use y * y'
    rw [map_mul]
    rw [hy, hy']
  one_mem' := ⟨1, by simp⟩

def Valuation.valueGroup : Subgroup Bˣ := Subgroup.closure (Valuation.valueMonoid f)

abbrev Valuation.valueMonoid₀ := WithZero (Valuation.valueMonoid f)

abbrev Valuation.valueGroup₀ := WithZero (Valuation.valueGroup f)

open Valuation

lemma foo {b : Bˣ} {H : Set Bˣ} (hb : b ∈ H) : b ∈ Subgroup.closure H := by
  exact Subgroup.mem_closure.mpr fun K a ↦ a hb

lemma mem_valueMonoid
    {b : Bˣ} (hb : b.1 ∈ range f) : b ∈ valueMonoid f := by
  rcases hb with ⟨c, _⟩
  simp only [valueMonoid, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_preimage, mem_range]
  use c
--
-- theorem inv_mem_valueGroup {b : Bˣ} (hb : b ∈ (valueGroup f)) : b⁻¹ ∈ valueGroup f := by
--   simp only [range₀, union_singleton, inv_zero, Submonoid.mem_mk, Subsemigroup.mem_mk,
--     mem_insert_iff, mem_image, Units.ne_zero, and_false, exists_const, or_false] at hb ⊢
--   rcases hb with hb | ⟨b, hb, rfl⟩
--   · simp [hb]
--   exact Or.inr ⟨b⁻¹, by simpa⟩

instance : MonoidWithZero (valueMonoid₀ f) := inferInstance


instance : GroupWithZero (valueGroup₀ f) := inferInstance
  -- toMonoidWithZero := inferInstance
  -- inv a := by
  --   rcases a with ⟨a, ha⟩
  --   exact ⟨a⁻¹, inv_mem_range₀ _ ha⟩
  -- exists_pair_ne := by
  --   use 1, ⟨0, by simp [range₀]⟩
  --   simp [← Subtype.coe_inj]
  -- inv_zero := Subtype.coe_inj.symm.mpr inv_zero
  -- mul_inv_cancel a ha₀ := by
  --   rw [Submonoid.mk_mul_mk, Submonoid.mk_eq_one, mul_inv_cancel₀]
  --   rwa [← Subtype.coe_ne_coe] at ha₀

-- theorem inv_mem_range₀_iff {b : B} : b⁻¹ ∈ range₀ f ↔ b ∈ range₀ f := by
--   by_cases h : b = 0
--   · simp only [h, inv_zero, zero_mem_range₀]
--   exact ⟨fun h ↦ ((inv_inv b).symm ▸ (inv_mem_range₀ f)) h, inv_mem_range₀ _⟩

-- **START HERE**

-- variable{f}
-- variable (h : ∀ {a}, f a ≠ 0 ↔ a ≠ 0) -- IS THIS A TYPECLASS?
--
-- def nonZeroDivisors_map : (nonZeroDivisors A) →* (nonZeroDivisors B) where
--   toFun := fun a ↦ ⟨f a, by simp [h]⟩
--   map_one' := by simp
--   map_mul' x y := by simp
--
-- @[simp]
-- lemma nonZeroDivisors_map_apply (a : nonZeroDivisors A) : nonZeroDivisors_map h a = f a := rfl
--
-- noncomputable
-- def nonZeroDivisors_mrange : Submonoid Bˣ := MonoidHom.mrange
--   (nonZeroDivisorsEquivUnits.toMonoidHom.comp (nonZeroDivisors_map h))
--
-- lemma mem_nonZeroDivisors_mrange [NoZeroDivisors A]
--     {b : Bˣ} (hb : b.1 ∈ range f) : b ∈ nonZeroDivisors_mrange h := by
--   simp only [nonZeroDivisors_mrange, MonoidHom.mem_mrange, MulEquiv.toMonoidHom_eq_coe,
--     MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, nonZeroDivisorsEquivUnits_apply,
--     nonZeroDivisors_map_apply, Subtype.exists, mem_nonZeroDivisors_iff_ne_zero]
--   rcases hb with ⟨c, hc⟩
--   exact ⟨c, h.mp <| hc ▸ b.ne_zero, by simp [hc, Units.mk0_val]⟩
--
-- lemma mem_nonZeroDivisors_mrange_old [NoZeroDivisors A]
--     {b : Bˣ} (hb : b.1 ∈ range f) : b ∈ nonZeroDivisors_mrange h := by
--   simp only [nonZeroDivisors_mrange, MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_mrange,
--     MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, nonZeroDivisorsEquivUnits_apply,
--     nonZeroDivisors_map_apply, Subtype.exists]
--   simp only [mem_range] at hb
--   obtain ⟨a, ha⟩ := hb
--   refine ⟨a, ?_, by ext; rw [← ha]; rfl⟩
--   rw [mem_nonZeroDivisors_iff]
--   intro x hx
--   rw [mul_eq_zero] at hx
--   rcases hx with _ | hx
--   · assumption
--   · simp [hx, Eq.comm] at ha
--
-- def nonZeroDivisors_range : Subgroup Bˣ := Subgroup.closure (nonZeroDivisors_mrange h)
--
-- lemma nonZeroDivisors_mrange_eq_nonZeroDivisors_range {X W : Type*} [GroupWithZero X]
--     [FunLike W X B] [MonoidWithZeroHomClass W X B] {φ : W} :
--     (nonZeroDivisors_mrange (map_ne_zero φ)) =
--       (nonZeroDivisors_range (map_ne_zero φ)).toSubmonoid := by
--   simp [nonZeroDivisors_range]
--   rw [Subgroup.closure_toSubmonoid]
--   rw [Eq.comm]
--   apply Submonoid.closure_eq_of_le
--   · simp only [union_subset_iff, subset_refl, true_and]
--     intro x hx
--     rcases hx with ⟨y, hy⟩
--     simp at hy
--     set z : nonZeroDivisors X := by
--       use y⁻¹
--       simp with hz
--     use z
--     rw [hz]
--     simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
--       Function.comp_apply, nonZeroDivisorsEquivUnits_apply, nonZeroDivisors_map_apply, map_inv₀]
--     rw [← inv_inv (a := Units.mk0 _ _)] at hy
--     simp at hy
--     apply_fun (fun b : Bˣ ↦ b⁻¹)
--     · simp only
--       rw [← hy]
--       sorry
--       -- rw [Units.mk0_inv_eq_inv]
--       -- simp
--     exact inv_injective
--   · rw [Submonoid.closure_union]
--     simp

lemma Units.mk0_inv_eq_inv {b : B} (hb : b ≠ 0) :
    (Units.mk0 b hb)⁻¹ = Units.mk0 (b⁻¹) (inv_ne_zero hb) := Units.eq_iff.mp rfl

-- theorem inv_mem_valueMonoid {b : Bˣ} : b⁻¹ ∈ valueMonoid f ↔ b ∈ valueMonoid f := by
  -- by_cases h : b = 0
  -- · simp only [h, inv_zero, zero_mem_range₀]

  -- exact ⟨fun h ↦ ((inv_inv b).symm ▸ (inv_mem_range₀ f)) h, inv_mem_range₀ _⟩

lemma valueMonoid_eq_valueGroup {X W : Type*} [GroupWithZero X] [FunLike W X B]
    [MonoidWithZeroHomClass W X B] {w : W} : (valueMonoid w) = (valueGroup w).toSubmonoid := by
  simp [valueGroup]
  rw [Subgroup.closure_toSubmonoid]
  rw [Eq.comm]
  apply Submonoid.closure_eq_of_le
  · simp [union_subset_iff, subset_refl, true_and, valueMonoid]
    intro x ⟨y, hy⟩
    simp at hy
    use y⁻¹
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
      Function.comp_apply, nonZeroDivisorsEquivUnits_apply, map_inv₀]
    rw [hy]
    simp
  · rw [Submonoid.closure_union]
    simp

lemma valueMonoid_eq_valueGroup' {X W : Type*} [GroupWithZero X] [FunLike W X B]
    [MonoidWithZeroHomClass W X B] {w : W} : ((valueMonoid w) : Set Bˣ)= (valueGroup w) := by
  rw [valueMonoid_eq_valueGroup]
  rfl

lemma valueGroup_eq_range {X W : Type*} [GroupWithZero X] [FunLike W X B]
    [MonoidWithZeroHomClass W X B] {w : W} :
    Units.val '' (valueGroup w) = (range w \ {0}) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← valueMonoid_eq_valueGroup'] at h
    obtain ⟨y, ⟨hy, rfl⟩⟩  := h
    simp only [Subgroup.coe_toSubmonoid, Subgroup.closure_eq, SetLike.mem_coe] at hy
    simp
    simp [valueMonoid] at hy
    obtain ⟨a, ha⟩ := hy
    use a
  · rw [← valueMonoid_eq_valueGroup']
    simp only [mem_diff, mem_range, mem_singleton_iff] at h
    obtain ⟨⟨y, hy⟩, hx₀⟩ := h
    set u : Bˣ := Units.mk0 x hx₀ with hu
    simp
    use u
    constructor
    · apply mem_valueMonoid
      rw [hu]
      simp
      use y
    · rfl
--
-- lemma nonZeroDivisors_mrange_eq_nonZeroDivisors_range' {X W : Type*} [GroupWithZero X]
--     [FunLike W X B] [MonoidWithZeroHomClass W X B] {φ : W} :
--     ((nonZeroDivisors_mrange (map_ne_zero φ)) : Set Bˣ) =
--       (nonZeroDivisors_range (map_ne_zero φ)) := by
--   rw [nonZeroDivisors_mrange_eq_nonZeroDivisors_range]
--   rfl


-- lemma nonZeroDivisors_range_eq_range {X W : Type*} [GroupWithZero X] [FunLike W X B]
--     [MonoidWithZeroHomClass W X B] {φ : W} :
--     Units.val '' (nonZeroDivisors_range (map_ne_zero φ)) = (range φ \ {0}) := by
--   ext x
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · rw [← nonZeroDivisors_mrange_eq_nonZeroDivisors_range'] at h
--     obtain ⟨y, ⟨hy, rfl⟩⟩  := h
--     simp only [Subgroup.coe_toSubmonoid, Subgroup.closure_eq, SetLike.mem_coe] at hy
--     simp
--     simp [nonZeroDivisors_mrange] at hy
--     obtain ⟨a, ha0, ha⟩ := hy
--     use a
--     rw [← ha]
--     rfl
--   · rw [← nonZeroDivisors_mrange_eq_nonZeroDivisors_range']
--     simp only [mem_diff, mem_range, mem_singleton_iff] at h
--     obtain ⟨⟨y, hy⟩, hx₀⟩ := h
--     set u : Bˣ := Units.mk0 x hx₀ with hu
--     simp
--     use u
--     constructor
--     · apply mem_nonZeroDivisors_mrange
--       rw [hu]
--       simp
--       use y
--     · rfl

-- abbrev NZDRange₀ := WithZero (nonZeroDivisors_range h)

-- instance : GroupWithZero (NZDRange₀ h) where
--   toMonoidWithZero := inferInstance
--   inv_zero := sorry
--   mul_inv_cancel := sorry
--   div_eq_mul_inv := sorry

open Subgroup in
theorem mem_valueMonoid_iff_of_comm (y : Bˣ) :
    y ∈ valueMonoid f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by sorry


#exit
end GroupWithZero
section CommGroupWithZero

variable [MonoidWithZero A] [Nontrivial A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]
variable{f}
variable (h : ∀ {a}, f a ≠ 0 ↔ a ≠ 0) -- IS THIS A TYPECLASS?

open Subgroup in
theorem mem_NZDRange₀_iff_of_comm (y : Bˣ) :
    y ∈ (nonZeroDivisors_range h) ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by
  refine ⟨fun hy ↦ ?_, fun ⟨a, ha, ⟨x, hy⟩⟩ ↦ ?_⟩
  · simp only [union_singleton, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_insert_iff,
    mem_image, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid] at hy
    rcases hy with hy | ⟨u, hu, huy⟩
    · exact ⟨1, by simp, 0, by simp [hy]⟩
    induction hu using closure_induction generalizing y with
    | mem c hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨1, by simp [← huy], a, by simp [ha, huy]⟩
    | one => exact ⟨1, by simp, 1, by simp [← huy]⟩
    | mul c d hc hd hcy hdy =>
      obtain ⟨u, hu, ⟨a, ha⟩⟩ := hcy c (refl _)
      obtain ⟨v, hv, ⟨b, hb⟩⟩ := hdy d (refl _)
      exact ⟨u * v, by simp [hu, hv], a * b,
        by simpa [map_mul, ← huy, Units.val_mul, ← ha, ← hb] using mul_mul_mul_comm ..⟩
    | inv c hc hcy  =>
      obtain ⟨u, hu, ⟨a, ha⟩⟩ := hcy _ (refl _)
      exact ⟨a, by simp [← ha, hu], u, by simp [← huy, ← ha]⟩
  · simp only [range₀, union_singleton, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_insert_iff,
    mem_image, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
    rcases GroupWithZero.eq_zero_or_unit y with h | h
    · simp [h]
    · right
      refine ⟨h.choose, ?_, h.choose_spec.symm⟩
      set u := (Ne.isUnit ha).unit with hu
      have hv : IsUnit (f x) := by
        simp only [← hy, hu, isUnit_iff_ne_zero, ne_eq, mul_eq_zero, Units.ne_zero, false_or]
        rw [h.choose_spec]
        simp [ha]
      set v := hv.unit
      have hv : f x = v := by simp [v]
      suffices h.choose = v / u by
        rw [this]
        apply Subgroup.div_mem
        · apply subset_closure
          simp [← hv]
        · apply subset_closure
          simp [hu]
      rw [eq_div_iff_mul_eq', mul_comm, ← Units.eq_iff,
        Units.val_mul, h.choose_spec.symm, ← hv, ← hy]
      rfl



/-- `MonoidHomWithZero.range₀' f` is a `CommGroupWithZero`  when the codomain is commutative. -/
instance : CommGroupWithZero (range₀ f) where
  toGroupWithZero := inferInstance
  mul_comm := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [mem_range₀_iff_of_comm] at ha hb
    obtain ⟨x, hx, ⟨c, hc⟩⟩ := ha; obtain ⟨y, hy, ⟨d, hd⟩⟩ := hb
    simp
    rw [← eq_inv_mul_iff_mul_eq₀] at hc hd
    · rw [hc, hd, mul_comm]
    exacts [hy, hx]


end CommGroupWithZero

end MonoidHomWithZero

#min_imports
