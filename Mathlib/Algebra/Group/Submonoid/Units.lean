/-
Copyright (c) 2023 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Group.Subgroup.Basic

/-!

# Submonoid of units

Given a submonoid `S` of a monoid `M`, we define the subgroup `S.units` as the units of `S` as a
subgroup of `Mˣ`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`, as terms of type `Mˣ`.

We also define, for subgroups `S` of `Mˣ`, `S.ofUnits`, which is `S` considered as a submonoid
of `M`. `Submonoid.units` and `Subgroup.ofUnits` form a Galois coinsertion.

We also make the equivalent additive definitions.

# Implementation details
There are a number of other constructions which are multiplicatively equivalent to `S.units` but
which have a different type.

| Definition           | Type          |
|----------------------|---------------|
| `S.units`            | `Subgroup Mˣ` |
| `Sˣ`                 | `Type u`      |
| `IsUnit.submonoid S` | `Submonoid S` |
| `S.units.ofUnits`    | `Submonoid M` |

All of these are distinct from `S.leftInv`, which is the submonoid of `M` which contains
every member of `M` with a right inverse in `S`.
-/

variable {M : Type*} [Monoid M]

open Units

open Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`.  -/
@[to_additive " The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. "]
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`.  -/
@[to_additive " A additive subgroup of additive units represented as a additive submonoid of `M`. "]
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (coeHom M)

@[to_additive]
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
  fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]
lemma Submonoid.ofUnits_units_le (S : Submonoid M) : S.units.ofUnits ≤ S :=
  fun  _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]
lemma Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
  fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]
lemma Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) : S.ofUnits.units = S :=
  Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

/-- A Galois coinsertion exists between the coercion from a subgroup of units to a submonoid and
the reduction from a submonoid to its unit group. -/
@[to_additive " A Galois coinsertion exists between the coercion from a additive subgroup of
additive units to a additive submonoid and the reduction from a additive submonoid to its unit
group. " ]
def ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[to_additive]
lemma ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
ofUnits_units_gci.gc

@[to_additive]
lemma ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := ofUnits_units_gc _ _

namespace Submonoid

section Units

@[to_additive]
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl

@[to_additive]
lemma mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) ∈ S)
    (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units := ⟨h₁, h₂⟩

@[to_additive]
lemma val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : (x : M) ∈ S := h.1

@[to_additive]
lemma inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := h.2

@[to_additive]
lemma coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.inv_mul

@[to_additive]
lemma coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.mul_inv

@[to_additive]
lemma mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := Subtype.ext x.inv_mul

@[to_additive]
lemma mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext x.mul_inv

@[to_additive]
lemma mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x ∈ S.units) (h₂ : y ∈ S.units):
    x * y ∈ S.units := mul_mem h₁ h₂

@[to_additive]
lemma inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : x⁻¹ ∈ S.units := inv_mem h

@[to_additive]
lemma inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ ∈ S.units ↔ x ∈ S.units := inv_mem_iff

/-- The equivalence between the subgroup of units of `S` and the type of units of `S`. -/
@[to_additive " The equivalence between the additive subgroup of additive units of
`S` and the type of additive units of `S`. "]
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun := fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]
lemma units_top : (⊤ : Submonoid M).units = ⊤ := ofUnits_units_gc.u_top

@[to_additive]
lemma units_inf (S T : Submonoid M): (S ⊓ T).units = S.units ⊓ T.units :=
  ofUnits_units_gc.u_inf

@[to_additive]
lemma units_sInf {s: Set (Submonoid M)} : (sInf s).units = ⨅ S ∈ s, S.units :=
  ofUnits_units_gc.u_sInf

@[to_additive]
lemma units_iInf {ι : Sort*} (f : ι → Submonoid M) : (iInf f).units = ⨅ (i : ι), (f i).units :=
  ofUnits_units_gc.u_iInf

@[to_additive]
lemma units_iInf₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Submonoid M) :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units :=
  ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := ofUnits_units_gci.u_bot

@[to_additive]
lemma units_surjective : Function.Surjective (units (M := M)) :=
  ofUnits_units_gci.u_surjective

@[to_additive]
lemma units_left_inverse :
    Function.LeftInverse (units (M := M)) (Subgroup.ofUnits (M := M)) :=
  ofUnits_units_gci.u_l_leftInverse

/-- The equivalence between the subgroup of units of `S` and the submonoid of unit
elements of `S`. -/
@[to_additive " The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`.  "]
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

end Units

end Submonoid

namespace Subgroup

@[to_additive]
lemma mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := Iff.rfl

@[to_additive]
lemma mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y ∈ S) (h₂ : y = x) : x ∈ S.ofUnits :=
  ⟨_, h₁, h₂⟩

@[to_additive]
lemma exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    ∃ y ∈ S, y = x := h

@[to_additive]
lemma mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S :=
  match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]
lemma isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x ∈ S.ofUnits) : IsUnit x :=
  match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

/-- Given some `x : M` which is a member of the submonoid of unit elements corresponding to a
  subgroup of units, produce a unit of `M` whose coercion is equal to `x`. `-/
@[to_additive " Given some `x : M` which is a member of the additive submonoid of additive unit
elements corresponding to a subgroup of units, produce a unit of `M` whose coercion is equal to
`x`. "]
noncomputable def unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) : Mˣ :=
  (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := Units.ext rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x ∈ S.ofUnits} :
    S.unit_of_mem_ofUnits h ∈ S := S.mem_of_mem_val_ofUnits h

@[to_additive]
lemma unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x ∈ S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext rfl

@[to_additive]
lemma unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S :=
  S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]
lemma mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit ∈ S) : x ∈ S.ofUnits := S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]
lemma mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S :=
  ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

/-- The equivalence between the coercion of a subgroup `S` of `Mˣ` to a submonoid of `M` and
the subgroup itself as a type. -/
@[to_additive " The equivalence between the coercion of an additive subgroup `S` of
`Mˣ` to an additive submonoid of `M` and the additive subgroup itself as a type. "]
noncomputable def ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where
  toFun := fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => Subtype.ext (Units.ext rfl)
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[to_additive (attr := simp)]
lemma ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥ := ofUnits_units_gc.l_bot

@[to_additive]
lemma ofUnits_inf (S T : Subgroup Mˣ): (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits :=
ofUnits_units_gc.l_sup

@[to_additive]
lemma ofUnits_sSup (s: Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S ∈ s, S.ofUnits :=
ofUnits_units_gc.l_sSup

@[to_additive]
lemma ofUnits_iSup {ι : Sort*} {f : ι → Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := ofUnits_units_gc.l_iSup

@[to_additive]
lemma ofUnits_iSup₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Subgroup Mˣ) :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits :=
  ofUnits_units_gc.l_iSup₂

@[to_additive]
lemma ofUnits_injective : Function.Injective (ofUnits (M := M)) :=
  ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]
lemma ofUnits_sup_units (S T : Subgroup Mˣ): (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T :=
  ofUnits_units_gci.u_sup_l _ _

@[to_additive (attr := simp)]
lemma ofUnits_inf_units (S T : Subgroup Mˣ): (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T :=
  ofUnits_units_gci.u_inf_l _ _

@[to_additive]
lemma ofUnits_right_inverse :
    Function.RightInverse (ofUnits (M := M)) (Submonoid.units (M := M)) :=
  ofUnits_units_gci.u_l_leftInverse

@[to_additive]
lemma ofUnits_strictMono : StrictMono (ofUnits (M := M)) := ofUnits_units_gci.strictMono_l

lemma ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits ≤ T.ofUnits ↔ S ≤ T :=
  ofUnits_units_gci.l_le_l_iff

/-- The equivalence between the top subgroup of `Mˣ` coerced to a submonoid `M` and the
units of `M`. -/
@[to_additive " The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`.  "]
noncomputable def ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ :=
  (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

variable {G : Type*}  [Group G]

@[to_additive]
lemma mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ): x ∈ H.units ↔ (x : G) ∈ H := by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

@[to_additive]
lemma mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G): x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by
  simp_rw [mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

@[to_additive (attr := simp)]
lemma mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x ∈ H.units ↔ x ∈ H := by
  simp_rw [mem_units_iff_val_mem, val_toUnits_apply]

@[to_additive (attr := simp)]
lemma val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) ∈ H.ofUnits ↔ x ∈ H := by
  simp_rw [mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

/-- The equivalence between the greatest subgroup of units contained within `T` and `T` itself. -/
@[to_additive " The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself. "]
def unitsEquivSelf (H : Subgroup G) : H.units ≃* H :=
  H.unitsEquivUnitsType.trans toUnits.symm

end Subgroup
