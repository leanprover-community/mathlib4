/-
Copyright (c) 2025 Antoine Chambert-Loir and Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Edison Xie
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup.Units
public import Mathlib.Algebra.GroupWithZero.Submonoid.Instances

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a group with zero, we define
`MonoidWithZeroHom.valueGroup₀ f` as the smallest `SubgroupWithZero` of `B` containing the range
of `f`, and `MonoidWithZeroHom.valueGroup₀ f` as the corresponding type. For example, if `A = ℕ`
and `f` is the natural cast to `B` where `B` is
* `ℝ≥0`, then `valueGroup₀ f` is the set of nonnegative rationals;
* `WithZero ℤ`, then `valueGroup₀ f = {0, 1}`.

`MonoidWithZeroHom.valueGroup f` is the corresponding subgroup of `Bˣ`, obtained by taking units.

## Main declarations

* `valueGroup₀ f` is the smallest subgroup with zero of `B` containing the range of `f`;
* `valueGroup f` is the group of units of `valueGroup₀ f`, a subgroup of `Bˣ`;
* `rangeRestrict f` is `f` viewed as a map into `valueGroup₀ f`;
* when `B` is a commutative group with zero, `valueGroup₀ f` is exactly the set of ratios of
  elements of the range of `f`: see `MonoidWithZeroHom.mem_valueGroup₀_iff_of_comm`.

## Implementation notes

Beware that `⊥ = {0, 1}` for `SubgroupWithZero`, so `Nontrivial (valueGroup₀ f)` holds for every
`f` and is useless as a non-degeneracy hypothesis; use `Nontrivial (valueGroup₀ f)ˣ`.
-/

@[expose] public section

namespace MonoidWithZeroHom

open Set

section mrange

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H] [Nontrivial H] (f : G →*₀ H)

lemma mrange_nontrivial :
    Nontrivial (MonoidHom.mrange f) :=
  ⟨1, 0, by simp [Subtype.ext_iff]⟩

lemma range_nontrivial :
    (Set.range f).Nontrivial :=
  Set.nontrivial_coe_sort.mp f.mrange_nontrivial

end mrange

variable {A B : Type*}

section GroupWithZero

variable [MonoidWithZero A] [GroupWithZero B] (f : A →*₀ B)

/-- For a morphism of monoids with zero `f`, this is the smallest subgroup with zero of the
codomain containing the range of `f`. -/
def valueGroup₀ : SubgroupWithZero B := SubgroupWithZero.closure (Set.range f)

/-- For a morphism of monoids with zero `f`, this is the smallest subgroup of the invertible
elements in the codomain containing the range of `f`.

It is the group of units of `valueGroup₀ f`. -/
def valueGroup : Subgroup Bˣ := (valueGroup₀ f).units

variable {f}

lemma subset_valueGroup₀ : Set.range f ⊆ valueGroup₀ f := SubgroupWithZero.subset_closure

@[simp]
lemma apply_mem_valueGroup₀ (a : A) : f a ∈ valueGroup₀ f := subset_valueGroup₀ ⟨a, rfl⟩

lemma mem_valueGroup₀ {b : B} (hb : b ∈ Set.range f) : b ∈ valueGroup₀ f := subset_valueGroup₀ hb

@[simp]
lemma mem_valueGroup_iff {u : Bˣ} : u ∈ valueGroup f ↔ (u : B) ∈ valueGroup₀ f := Iff.rfl

lemma mem_valueGroup {b : Bˣ} (hb : (b : B) ∈ Set.range f) : b ∈ valueGroup f := mem_valueGroup₀ hb

lemma inv_mem_valueGroup {b : Bˣ} (hb : (b : B) ∈ Set.range f) : b⁻¹ ∈ valueGroup f :=
  Subgroup.inv_mem _ (mem_valueGroup hb)

variable (f)

@[simp]
lemma units_valueGroup₀ : (valueGroup₀ f).units = valueGroup f := rfl

lemma valueGroup₀_eq_withZero : valueGroup₀ f = (valueGroup f).withZero :=
  (SubgroupWithZero.withZero_units _).symm

/-- The old description of `valueGroup` as a `Subgroup.closure`. -/
lemma valueGroup_eq_closure : valueGroup f = Subgroup.closure (Units.val ⁻¹' Set.range f) :=
  SubgroupWithZero.units_closure _

lemma valueGroup₀_eq_closure : valueGroup₀ f = SubgroupWithZero.closure (Set.range f) := rfl

/-- Precomposing with a surjection does not change the value group with zero. -/
lemma valueGroup₀_comp_of_surjective {C : Type*} [MonoidWithZero C] {g : C →*₀ A}
    (hg : Function.Surjective g) : valueGroup₀ (f.comp g) = valueGroup₀ f := by
  rw [valueGroup₀_eq_closure, valueGroup₀_eq_closure]
  congr 1
  exact hg.range_comp f

/-- Precomposing with a surjection does not change the value group. -/
lemma valueGroup_comp_of_surjective {C : Type*} [MonoidWithZero C] {g : C →*₀ A}
    (hg : Function.Surjective g) : valueGroup (f.comp g) = valueGroup f := by
  rw [valueGroup, valueGroup, valueGroup₀_comp_of_surjective f hg]

/-- The restriction of `f` to its value group with zero. -/
def rangeRestrict : A →*₀ valueGroup₀ f where
  toFun a := ⟨f a, apply_mem_valueGroup₀ a⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_mul' _ _ := Subtype.ext (map_mul f _ _)

@[deprecated (since := "2026-08-23")] alias ValueGroup₀.restrict₀ := rangeRestrict

variable {f}

lemma rangeRestrict_apply (a : A) : rangeRestrict f a = ⟨f a, apply_mem_valueGroup₀ a⟩ := rfl

@[simp]
lemma coe_rangeRestrict (a : A) : ((rangeRestrict f a : valueGroup₀ f) : B) = f a := rfl

@[simp]
lemma rangeRestrict_eq_zero_iff {a : A} : rangeRestrict f a = 0 ↔ f a = 0 := by
  rw [← Subtype.coe_inj, coe_rangeRestrict, ZeroMemClass.coe_zero]

@[simp]
lemma rangeRestrict_eq_one_iff {a : A} : rangeRestrict f a = 1 ↔ f a = 1 := by
  rw [← Subtype.coe_inj, coe_rangeRestrict, OneMemClass.coe_one]

lemma rangeRestrict_ne_zero_iff {a : A} : rangeRestrict f a ≠ 0 ↔ f a ≠ 0 :=
  rangeRestrict_eq_zero_iff.ne

variable (f)

end GroupWithZero

section DomainGroupWithZero

variable [GroupWithZero A] [GroupWithZero B] (f : A →*₀ B)

/-- When the domain is a group with zero, the range of `f` is closed under inverses, so
`MonoidWithZeroHom.mrange f` upgrades to a subgroup with zero. -/
def range : SubgroupWithZero B where
  __ := mrange f
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ f a⟩

@[simp]
lemma coe_range : (range f : Set B) = Set.range f := rfl

@[simp]
lemma coe_valueGroup₀_eq_range : (valueGroup₀ f : Set B) = Set.range f :=
  subset_antisymm
    (SubgroupWithZero.closure_le (s := range f) |>.2 (subset_refl _))
    subset_valueGroup₀

/-- When the domain is a group with zero, the value group with zero *is* the range. -/
lemma valueGroup₀_eq_range : valueGroup₀ f = range f :=
  SetLike.ext' (coe_valueGroup₀_eq_range f)

/-- When the domain is a group with zero, the value group with zero and the range agree as
submonoids with zero. -/
lemma toSubmonoidWithZero_valueGroup₀ : (valueGroup₀ f).toSubmonoidWithZero = mrange f :=
  SetLike.ext' (coe_valueGroup₀_eq_range f)

lemma valueGroup_eq_range : Units.val '' (valueGroup f) = Set.range f \ {0} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (u : B) ∈ valueGroup₀ f := hu
    rw [← SetLike.mem_coe, coe_valueGroup₀_eq_range] at hu'
    exact ⟨hu', u.ne_zero⟩
  · rintro ⟨hx, hx0⟩
    refine ⟨Units.mk0 x hx0, ?_, rfl⟩
    have : x ∈ valueGroup₀ f := by rw [← SetLike.mem_coe, coe_valueGroup₀_eq_range]; exact hx
    exact this

@[simp]
lemma rangeRestrict_range_eq_top : Set.range (rangeRestrict f) = ⊤ := by
  rw [top_eq_univ, Set.range_eq_univ]
  rintro ⟨x, hx⟩
  rw [← SetLike.mem_coe, coe_valueGroup₀_eq_range] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

lemma rangeRestrict_surjective : Function.Surjective (rangeRestrict f) :=
  fun _ ↦ Set.mem_range.mp (by simp [rangeRestrict_range_eq_top])

@[deprecated (since := "2026-08-23")]
alias ValueGroup₀.restrict₀_range_eq_top := rangeRestrict_range_eq_top
@[deprecated (since := "2026-08-23")]
alias ValueGroup₀.restrict₀_surjective := rangeRestrict_surjective

end DomainGroupWithZero

section CommGroupWithZero

variable [MonoidWithZero A] [CommGroupWithZero B] (f : A →*₀ B)

/-- The elements of `valueGroup₀ f` are exactly `0` and the ratios of elements of `range f`. -/
theorem mem_valueGroup₀_iff_of_comm {y : B} :
    y ∈ valueGroup₀ f ↔ y = 0 ∨ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by
  constructor
  · intro hy
    induction hy using SubgroupWithZero.closure_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      rcases eq_or_ne (f a) 0 with h | h
      · exact .inl h
      · exact .inr ⟨1, by simp, a, by simp⟩
    | zero => exact .inl rfl
    | one => exact .inr ⟨1, by simp, 1, by simp⟩
    | mul c d _ _ hc hd =>
      rcases hc with rfl | ⟨u, hu, a, ha⟩
      · exact .inl (by simp)
      rcases hd with rfl | ⟨v, hv, b, hb⟩
      · exact .inl (by simp)
      refine .inr ⟨u * v, by simp [hu, hv], a * b, ?_⟩
      rw [map_mul, map_mul, ← ha, ← hb]
      exact mul_mul_mul_comm ..
    | inv c _ hc =>
      rcases hc with rfl | ⟨u, hu, a, ha⟩
      · exact .inl (by simp)
      rcases eq_or_ne c 0 with rfl | hc0
      · exact .inl (by simp)
      have ha0 : f a ≠ 0 := by rw [← ha]; exact mul_ne_zero hu hc0
      refine .inr ⟨a, ha0, u, ?_⟩
      rw [← ha, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  · rintro (rfl | ⟨a, ha, x, hax⟩)
    · exact zero_mem _
    · have hy : y = (f a)⁻¹ * f x := by
        rw [← hax, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      rw [hy]
      exact mul_mem (inv_mem (apply_mem_valueGroup₀ a)) (apply_mem_valueGroup₀ x)

/-- See also `mem_valueGroup_iff_of_comm'` for a version proving that `f x ≠ 0`. -/
theorem mem_valueGroup_iff_of_comm {y : Bˣ} :
    y ∈ valueGroup f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by
  rw [mem_valueGroup_iff, mem_valueGroup₀_iff_of_comm]
  simp only [Units.ne_zero, false_or]

theorem mem_valueGroup_iff_of_comm' {y : Bˣ} :
    y ∈ valueGroup f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f x ≠ 0 ∧ f a * y = f x := by
  rw [mem_valueGroup_iff_of_comm]
  exact ⟨fun ⟨a, ha, x, hax⟩ ↦ ⟨a, ha, x, by aesop, hax⟩, fun ⟨a, ha, x, hx, hax⟩ ↦ ⟨a, ha, x, hax⟩⟩

namespace valueGroup₀

variable {r₁ s₁ r₂ s₂ : A}

/-- The element `(f r)⁻¹ * f s` of `valueGroup₀ f`.

No nonvanishing hypotheses are needed: the formula is already correct when `f r = 0` or
`f s = 0`, since `0⁻¹ = 0`. -/
def mk (r s : A) : valueGroup₀ f :=
  ⟨(f r)⁻¹ * f s, mul_mem (inv_mem (apply_mem_valueGroup₀ r)) (apply_mem_valueGroup₀ s)⟩

@[simp]
lemma coe_mk (r s : A) : (mk f r s : B) = (f r)⁻¹ * f s := rfl

@[simp]
lemma mk_eq_zero_iff {r s : A} : mk f r s = 0 ↔ f r = 0 ∨ f s = 0 := by
  rw [← Subtype.coe_inj, coe_mk, ZeroMemClass.coe_zero, mul_eq_zero, inv_eq_zero]

@[simp] theorem mk_inj (hr₁ : f r₁ ≠ 0) (hr₂ : f r₂ ≠ 0) :
    mk f r₁ s₁ = mk f r₂ s₂ ↔ f (r₁ * s₂) = f (r₂ * s₁) := by
  rw [← Subtype.coe_inj, coe_mk, coe_mk, map_mul, map_mul,
    inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hr₁ hr₂, mul_comm (f s₁), mul_comm (f s₂),
    eq_comm]

@[simp] theorem mk_mul (r₁ s₁ r₂ s₂ : A) :
    mk f r₁ s₁ * mk f r₂ s₂ = mk f (r₁ * r₂) (s₁ * s₂) := by
  rw [← Subtype.coe_inj, Submonoid.coe_mul, coe_mk, coe_mk, coe_mk, map_mul, map_mul,
    mul_mul_mul_comm, mul_inv]

theorem exists_mk (x : valueGroup₀ f) : ∃ r s, x = mk f r s := by
  obtain ⟨y, hy⟩ := x
  rw [mem_valueGroup₀_iff_of_comm] at hy
  rcases hy with rfl | ⟨a, ha, r, har⟩
  · exact ⟨0, 0, by simp [Subtype.ext_iff]⟩
  · refine ⟨a, r, ?_⟩
    rw [Subtype.ext_iff, coe_mk, ← har, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end valueGroup₀

end CommGroupWithZero

end MonoidWithZeroHom
