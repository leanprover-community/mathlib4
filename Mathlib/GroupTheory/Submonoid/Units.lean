/-
Copyright (c) 2023 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.GroupTheory.Submonoid.MulOpposite
import Mathlib.GroupTheory.Subgroup.Basic

/-!

# Submonoid of units

Given a submonoid `S` of a monoid `M`, we define the submonoid `S.units` as the largest subgroup of
`Mˣ` contained within `S`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`. This is multiplicatively equivalent to `Sˣ` and also to
`IsUnit.submonoid S`, but crucially it is as a `Subgroup Mˣ` rather than as a type in and of itself
or as a `Submonoid M`.

-/

variable {M : Type*} {G : Type*}

variable [Monoid M] [Group G]

@[to_additive]
lemma unitsTypeUnitsTypeEquivUnitsType {M : Type*} [Monoid M] : Mˣˣ ≃* Mˣ := toUnits.symm

namespace Submonoid

/-- The greatest subgroup of the type of units of `M` contained within `S`.  -/
@[to_additive " The greatest additive subgroup of the type of additive units of `M` contained within
`S`. "]
def units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (Units.coeHom M) ⊓ (S.comap ((Units.coeHom M).comp
    (MulEquiv.inv' Mˣ).symm.toMonoidHom)).unop
  inv_mem' ha := ⟨ha.2, ha.1⟩

section Units

@[to_additive (attr := simp)]
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl

@[to_additive]
lemma mem_units_iff_coe_mem (S : Submonoid M) (h : ∀ (x : Mˣ), ↑x ∈ S ↔ ↑x⁻¹ ∈ S)
    (x : Mˣ) : x ∈ S.units ↔ ((x : M) ∈ S) := by rw [S.mem_units_iff, h, and_self]

@[to_additive]
lemma coe_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (x : M) ∈ S := ((S.mem_units_iff _).mp h).1

@[to_additive]
lemma coe_coe_mem (S : Submonoid M) (x : S.units) :
    ((x : Mˣ) : M) ∈ S := S.coe_mem_of_mem_units (SetLike.coe_mem _)

@[to_additive]
lemma coe_inv_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := ((S.mem_units_iff _).mp h).2

@[to_additive]
lemma coe_coe_inv_mem (S : Submonoid M) (x : S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := S.coe_inv_mem_of_mem_units (SetLike.coe_mem _)

@[to_additive]
lemma mem_units_of_coe_mem_coe_inv_mem (S : Submonoid M) {x : Mˣ}
    (h₁ : (x : M) ∈ S) (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units :=
    ((S.mem_units_iff _).mpr ⟨h₁, h₂⟩)

@[to_additive]
lemma coe_coe_inv_mul_coe_coe (S : Submonoid M) (x : Sˣ) :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := congrArg ((↑) : S → M) (Units.inv_mul _)

@[to_additive]
lemma coe_coe_mul_coe_coe_inv (S : Submonoid M) (x : Sˣ) :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := congrArg ((↑) : S → M)  (Units.mul_inv _)

@[to_additive]
lemma coe_inv_coe_mul_coe_coe (S : Submonoid M) (x : S.units) :
    ((x⁻¹ : Mˣ) : M) * ((x : Mˣ) : M) = 1 := Units.inv_mul _

@[to_additive]
lemma coe_coe_mul_coe_inv_coe (S : Submonoid M) (x : S.units) :
    ((x : Mˣ) : M) * ((x⁻¹ : Mˣ) : M) = 1 := Units.mul_inv _

@[to_additive]
lemma units_top : (⊤ : Submonoid M).units = ⊤ := by
    simp_rw [SetLike.ext_iff, mem_units_iff, mem_top, and_self, Subgroup.mem_top, implies_true]

@[to_additive]
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := by
    simp_rw [SetLike.ext_iff, mem_units_iff, mem_bot, Units.val_eq_one, inv_eq_one, and_self,
    Subgroup.mem_bot, implies_true]

@[to_additive]
lemma units_inf (S T : Submonoid M): (S ⊓ T).units = S.units ⊓ T.units := by
    ext
    simp_rw [Subgroup.mem_inf, mem_units_iff, mem_inf]
    refine ⟨?_, ?_⟩ <;> exact fun ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ => ⟨⟨h₁, h₃⟩, ⟨h₂, h₄⟩⟩

@[to_additive]
lemma units_mono : Monotone (Submonoid.units (M := M)) := fun _ _ hST x => by
    simp_rw [mem_units_iff]
    exact fun ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive]
lemma units_le (S : Submonoid M) : S.units.toSubmonoid.map (Units.coeHom M) ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    simp_rw [Subgroup.coe_toSubmonoid, SetLike.mem_coe, mem_units_iff] at hy
    exact hy.1

@[to_additive]
lemma le_units_iff (S : Submonoid M) (H : Subgroup Mˣ) :
    H.toSubmonoid.map (Units.coeHom M) ≤ S ↔ H ≤ S.units := by
  refine ⟨fun H => ?_, fun H => le_trans (fun _ => ?_) S.units_le⟩
  · intro x hx
    simp_rw [mem_units_iff]
    refine ⟨H ⟨x, hx, rfl⟩, H ⟨x⁻¹, ?_, rfl⟩⟩
    simp_rw [Subgroup.coe_toSubmonoid, SetLike.mem_coe, inv_mem_iff]
    exact hx
  · simp_rw [mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply,
      forall_exists_index, and_imp]
    rintro y hy rfl
    exact ⟨y, H hy, rfl⟩

/- TODO: It looks like this is a Galois connection. It might be worth defining the
other map which sends H : Subgroup Mˣ to a Submonoid of M,
H.toSubmonoid.map (Units.coeHom M) (effectively a coercion?), proving the GC,
and then most of the above lemmas will follow automatically.
-/

/-- The equivalence between the greatest subgroup of units contained within `S` and the
  type of units within `S`. -/
@[to_additive (attr := simps!) " The equivalence between the greatest additive subgroup of additive
units contained within `S` and the type of additive units within `S`. "]
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun x := ⟨⟨_, S.coe_coe_mem _⟩, ⟨_, S.coe_coe_inv_mem _⟩,
      Subtype.ext (S.coe_coe_mul_coe_inv_coe x),
      Subtype.ext (S.coe_inv_coe_mul_coe_coe x)⟩
  invFun x := ⟨⟨_, _, S.coe_coe_mul_coe_coe_inv x, S.coe_coe_inv_mul_coe_coe x⟩,
      S.mem_units_of_coe_mem_coe_inv_mem (SetLike.coe_mem _) (SetLike.coe_mem _)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

/-
TODO: Remove this comment when other added function is confimed to work.
/-- The equivalence between the greatest subgroup of units of `M` contained within `S` and the
  submonoid of `S` which contains unit elements. -/
@[to_additive (attr := simps!) " The equivalence between the greatest additive subgroup of units
of `M` contained within `S` and the additive submonoid of `S` which contains additive unit
elements. "]
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid
-/

end Units

end Submonoid

namespace Subgroup

@[to_additive]
lemma mem_units_iff_coe_mem (T : Subgroup G) (x : Gˣ): x ∈ T.units ↔ (x : G) ∈ T := by
    simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, Units.val_inv_eq_inv_val, inv_mem_iff,
    and_self]

@[to_additive]
lemma mem_iff_toUnits_mem_units (T : Subgroup G) (x : G) : x ∈ T ↔ toUnits x ∈ T.units := by
    simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, Units.val_inv_eq_inv_val, inv_mem_iff,
    and_self, coe_toUnits]

/-- The equivalence between the greatest subgroup of units contained within `T` and `T` itself. -/
@[to_additive (attr := simps!) " The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself. "]
def unitsEquivSelf (T : Subgroup G) : T.units ≃* T :=
T.unitsEquivUnitsType.trans (toUnits).symm

end Subgroup
