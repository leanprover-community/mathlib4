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

variable {M : Type*}

variable [Monoid M]

--TODO - Find better place for these two things.

@[to_additive]
lemma unitsTypeUnitsTypeEquivUnitsType {M : Type*} [Monoid M] : Mˣˣ ≃* Mˣ := toUnits.symm

/-- The multiplicative equivalence between the type of units of `M` and the submonoid whose elements
  are the units of `M`. -/
@[to_additive (attr := simps!) " The additive equivalence between the type of additive units of `M`
  and the additive submonoid whose elements are the additive units of `M`. "]
noncomputable def unitsTypeEquivIsUnitSubmonoid :
  Mˣ ≃* IsUnit.submonoid M where
  toFun x := ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv x := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

/-- The units of `S`, packaged as a subgroup of `Mˣ`.  -/
@[to_additive " The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. "]
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (Units.coeHom M) ⊓ (S.comap ((Units.coeHom M).comp
    (MulEquiv.inv' Mˣ).symm.toMonoidHom)).unop
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`.  -/
@[to_additive " A additive subgroup of additive units represented as a additive submonoid of `M`. "]
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (Units.coeHom M)

@[to_additive (attr := simp)]
lemma Subgroup.mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := Iff.rfl

@[to_additive (attr := simp)]
lemma Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl

@[to_additive]
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive]
lemma Submonoid.ofunits_units_le (S : Submonoid M) : S.units.ofUnits ≤ S :=
fun  _ ⟨_, hy, hx⟩ => hx ▸ hy.1

@[to_additive]
lemma Submonoid.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive]
lemma Submonoid.ofUnits_units_eq (S : Subgroup Mˣ) : S.ofUnits.units = S := SetLike.ext (fun _ => by
  exact ⟨fun ⟨⟨_, hx, hy⟩, _⟩ => (Units.ext hy) ▸ hx,
  fun hx => ⟨⟨_, hx, rfl⟩, ⟨_, S.inv_mem hx, rfl⟩⟩⟩)

@[to_additive]
def unitsGaloisCoinsertion : GaloisCoinsertion (Subgroup.ofUnits) (Submonoid.units (M := M)) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Submonoid.ofUnits_mono
  Submonoid.ofunits_units_le Submonoid.ofUnits_units_eq

@[to_additive]
lemma unitsGaloisConnection : GaloisConnection (Subgroup.ofUnits) (Submonoid.units (M := M)) :=
unitsGaloisCoinsertion.gc

namespace Submonoid

section Units

@[to_additive]
lemma units_top : (⊤ : Submonoid M).units = ⊤ := unitsGaloisConnection.u_top

@[to_additive]
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := unitsGaloisCoinsertion.u_bot

@[to_additive]
lemma units_inf (S T : Submonoid M): (S ⊓ T).units = S.units ⊓ T.units :=
unitsGaloisConnection.u_inf

@[to_additive]
lemma ge_ofUnits_iff_units_ge (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := unitsGaloisConnection _ _

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
lemma ofUnits_le_iff_le_units (H : Subgroup Mˣ) (S : Submonoid M) :
    H.ofUnits ≤ S ↔ H ≤ S.units := S.ge_ofUnits_iff_units_ge H

variable {G : Type*}  [Group G]

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
