/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

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
  and `Mˣ`.

* `MulChar.subgroupOrderIsoSubgroupMulChar`: The order reversing bijection that sends a
  subgroup of `Mˣ` to its dual subgroup in `MulChar M R`.

-/

@[expose] public section

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := .of_equiv _ equivToUnitHom.symm

lemma exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) :
    (∃ χ : MulChar M R, χ a ≠ 1) ↔ ∃ φ : Mˣ →* Rˣ, φ a ≠ 1 := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose hφ
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
    contrapose ha
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


/--
Let `N` be a submonoid of `M` group and let `R` be a ring with enough roots of unity.
Then any `R`-value multiplicative character of `N` can be extended to a multiplicative
character of `M`.
-/
theorem restrictHom_surjective (N : Submonoid M) :
    Function.Surjective (MulChar.restrictHom N R) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).restrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ ↦ ?_⟩
  rw [MonoidHom.restrictHom_apply] at hψ
  rw [restrictHom_apply, restrict_ofUnitHom]
  simp [hψ]

/-- The `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M` and `Mˣ`.
The image `m` of `η : MulChar (MulChar M R) R` is such that, for all `R`-valued multiplicative
character `χ` of `M`, we have `χ m = η χ`, see `MulChar.apply_mulCharEquiv`.
-/
noncomputable def mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
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

variable (M R) in
/--
The order reversing bijection that sends a subgroup of `Mˣ` to its dual subgroup in
`MulChar M R` where `M` is a finite commutative monoid and `R` is a ring with enough
roots of unity.
-/
noncomputable def subgroupOrderIsoSubgroupMulChar : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒᵈ :=
  (CommGroup.subgroupOrderIsoSubgroupMonoidHom Mˣ R).trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]
theorem mem_subgroupOrderIsoSubgroupMulChar_iff {H : Subgroup Mˣ} {χ : MulChar M R} :
    χ ∈ (subgroupOrderIsoSubgroupMulChar M R H).ofDual ↔ ∀ m ∈ H, χ m = 1 := by
  rw [subgroupOrderIsoSubgroupMulChar, OrderIso.trans_apply, OrderIso.dual_apply,
    MulEquiv.coe_mapSubgroup, OrderDual.ofDual_toDual, Subgroup.mem_map_equiv]
  simp [← Units.val_eq_one]

@[simp]
theorem mem_subgroupOrderIsoSubgroupMulChar_symm_iff {X : Subgroup (MulChar M R)} {m : Mˣ} :
    m ∈ (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual X) ↔ ∀ χ ∈ X, χ m = 1 := by
  simp [subgroupOrderIsoSubgroupMulChar, ← Units.val_eq_one]

/-- The cardinality of the dual subgroup of `MulChar M R` associated to a subgroup `H` of `Mˣ`
equals the index of `H` in `Mˣ`. -/
theorem card_subgroupOrderIsoSubgroupMulChar {H : Subgroup Mˣ} :
    Nat.card (subgroupOrderIsoSubgroupMulChar M R H).ofDual = Nat.card (Mˣ ⧸ H) := by
  rw [subgroupOrderIsoSubgroupMulChar, OrderIso.trans_apply, OrderIso.dual_apply,
    OrderDual.ofDual_toDual, Subgroup.card_mapSubgroup,
    CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]

end MulChar
