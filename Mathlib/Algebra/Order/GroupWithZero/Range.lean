/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Edison Xie
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.Cyclic
public import Mathlib.Algebra.Order.GroupWithZero.Subgroup

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of `MonoidWithZeroHom.valueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.
-/

@[expose] public section

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

namespace valueGroup₀

lemma coe_unit_ne_zero (a : (valueGroup₀ f)ˣ) : (a.1 : B) ≠ 0 :=
  ZeroMemClass.coe_eq_zero.not.2 a.ne_zero

lemma coe_unit_pos (a : (valueGroup₀ f)ˣ) : 0 < (a.1 : B) := zero_lt_iff.2 (coe_unit_ne_zero a)

variable {r₁ s₁ r₂ s₂ : A}

/-- Comparing two ratios, when the denominators do not vanish. -/
theorem mk_le_mk_iff (f : A →*₀ B) (hr₁ : f r₁ ≠ 0) (hr₂ : f r₂ ≠ 0) :
    mk f r₁ s₁ ≤ mk f r₂ s₂ ↔ f (s₁ * r₂) ≤ f (s₂ * r₁) := by
  rw [← Subtype.coe_le_coe, coe_mk, coe_mk, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ (zero_lt_iff.2 hr₁) (zero_lt_iff.2 hr₂), map_mul, map_mul]

end valueGroup₀

/-! ### Bridging the with-zero hypotheses to the `Subgroup Bˣ` API

`valueGroup f` is by definition `(valueGroup₀ f).units`, but instance search does not unfold it,
so the transfers are declared explicitly. The canonical form for a non-degeneracy or cyclicity
hypothesis is `valueGroup f`; the with-zero forms are derived from it. -/

instance [Nontrivial (valueGroup f)] : Nontrivial (valueGroup₀ f)ˣ := by
  have : Nontrivial ↥(valueGroup₀ f).units := by rw [units_valueGroup₀]; infer_instance
  exact (SubgroupWithZero.unitsMulEquiv (valueGroup₀ f)).symm.toEquiv.injective.nontrivial

instance [Subsingleton (valueGroup f)] : Subsingleton (valueGroup₀ f)ˣ := by
  have : Subsingleton ↥(valueGroup₀ f).units := by rw [units_valueGroup₀]; infer_instance
  exact (SubgroupWithZero.unitsMulEquiv (valueGroup₀ f)).toEquiv.subsingleton

instance [IsCyclicWithZero (valueGroup₀ f)] : IsCyclic (valueGroup f) :=
  SubgroupWithZero.isCyclic_units (valueGroup₀ f)

end MonoidWithZeroHom
