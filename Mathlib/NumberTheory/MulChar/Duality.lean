/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

## Main results

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
  (noncanonically) isomorphic to `Mˣ`.

* `MulChar.mulCharEquiv`: the `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M`
  and `Mˣ` where `R` is a domain with enough roots of unity.

* `MulChar.subgroupOrderIsoSubgroupMulChar`: the order reversing bijection that sends a
  subgroup of `MulChar M R` to its dual subgroup in `MulChar (MulChar M R) R)`.

-/

@[expose] public section

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := .of_equiv _ equivToUnitHom.symm

lemma exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) :
    (∃ χ : MulChar M R, χ a ≠ 1) ↔ ∃ φ : Mˣ →* Rˣ, φ a ≠ 1 := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose! hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose! hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

variable (M R)
variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- If `M` is a finite commutative monoid and `R` is a ring that has enough roots of unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative character `χ : M → R` such that
`χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : a ≠ 1) :
    ∃ χ : MulChar M R, χ a ≠ 1 := by
  by_cases hu : IsUnit a
  · refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose! ha
    rw [← hu.unit_spec, ha, Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

/-- The group of `R`-valued multiplicative characters on a finite commutative monoid `M` is
(noncanonically) isomorphic to its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

/-- The cardinality of the group of `R`-valued multiplicative characters on a finite commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv

noncomputable section IsDomain

variable [IsDomain R]

/--
Let `N` be a submonoid of `M` group and let R` be a domain that has enough roots of unity.
Then any `R`-value multiplicative character of `T` can be extented to a multiplicative
character of `M`.
-/
theorem restrictHom_surjective (N : Submonoid M) :
    Function.Surjective (MulChar.restrictHom N R) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).restrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ?_⟩
  ext
  rw [MonoidHom.restrictHom_apply] at hψ
  rw [restrictHom_apply, restrict_ofUnitHom, hψ]
  simp

/-- The `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M` and `Mˣ` where `R` is a
domain with enough roots of unity.
The image `m` of `η : MulChar (MulChar M R) R` is such that, for all `R`-valued multiplicative
character `χ` of `M`, we have `χ m = η χ`, see `MulChar.apply_mulCharEquiv`.
-/
def mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
  mulEquivToUnitHom.trans <| toUnits.monoidHomCongrLeft.symm.trans <|
    mulEquivToUnitHom.monoidHomCongrLeft.trans <| CommGroup.monoidHomMonoidHomEquiv Mˣ R

variable {M R}

@[simp]
theorem mulCharEquiv_symm_apply_apply (m : Mˣ) (χ : MulChar M R) :
    (mulCharEquiv M R).symm m χ = χ m := by
  classical
  rw [show ((mulCharEquiv M R).symm m) χ =
    if IsUnit χ then ↑(mulEquivToUnitHom χ m) else (0 : R) by rfl, if_pos (Group.isUnit χ),
    mulEquivToUnitHom_apply, coe_equivToUnitHom]

@[simp]
theorem apply_mulCharEquiv (χ : MulChar M R) (η : MulChar (MulChar M R) R) :
    χ (mulCharEquiv M R η) = η χ := by
  rw [← mulCharEquiv_symm_apply_apply (mulCharEquiv M R η) χ, MulEquiv.symm_apply_apply]

variable (M R)

/--
The order reversing bijection that sends a subgroup of the group of `R`-valued multiplicative
characters `MulChar M R` to its dual subgroup in `MulChar (MulChar M R) R)` where
`M` is a finite commutative monoid and `R` is a domain with enough roots of unity.
-/
def subgroupOrderIsoSubgroupMulChar :
    Subgroup (MulChar M R) ≃o (Subgroup (MulChar (MulChar M R) R))ᵒᵈ :=
  haveI : HasEnoughRootsOfUnity R (Monoid.exponent (MulChar M R)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv mulEquivToUnitHom,
      Monoid.exponent_eq_of_mulEquiv
        (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some]
  (CommGroup.subgroupOrderIsoSubgroupMonoidHom (MulChar M R) R).trans <|
   toUnits.monoidHomCongrLeft.mapSubgroup.dual.trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]
theorem mem_subgroupOrderIsoSubgroupMulChar_iff (Y : Subgroup (MulChar M R))
    (η : MulChar (MulChar M R) R) :
    η ∈ (subgroupOrderIsoSubgroupMulChar M R Y).ofDual ↔ ∀ χ ∈ Y, η χ = 1 := by
  simp only [subgroupOrderIsoSubgroupMulChar, OrderIso.trans_apply, OrderIso.dual_apply,
    OrderDual.ofDual_toDual]
  rw [← OrderIso.trans_apply, MulEquiv.mapSubgroup_trans_apply, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv]
  simp [Units.ext_iff]

@[simp]
theorem mem_subgroupOrderIsoSubgroupMulChar_symm_iff (E : Subgroup (MulChar (MulChar M R) R))
    (χ : MulChar M R) :
    χ ∈ (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual E) ↔ ∀ η ∈ E, η χ = 1 := by
  simp only [subgroupOrderIsoSubgroupMulChar, OrderIso.symm_trans_apply, OrderIso.dual_symm_apply,
    MulEquiv.symm_mapSubgroup, MulEquiv.symm_symm, OrderDual.ofDual_toDual,
    MulEquiv.mapSubgroup_apply, MulEquiv.symm_monoidHomCongrLeft,
    CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff, Subgroup.mem_map, MonoidHom.coe_coe,
    mulEquivToUnitHom_apply, MulEquiv.monoidHomCongrLeft_apply, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, MonoidHom.coe_comp, Function.comp_apply]
  -- The two `simps` cannot be merged otherwise it becomes an `∞`-loop
  simp [Units.ext_iff]

end IsDomain

end MulChar
