/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
  (noncanonically) isomorphic to `Mˣ`.
-/

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := by
  have : Finite (Mˣ →* Rˣ) := by
    have : Fintype Mˣ := .ofFinite _
    let S := rootsOfUnity (Fintype.card Mˣ) R
    let F := Mˣ →* S
    have fF : Finite F := .of_injective _ DFunLike.coe_injective
    refine .of_surjective (fun f : F ↦ (Subgroup.subtype _).comp f) fun f ↦ ?_
    have H a : f a ∈ S := by simp only [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one, S]
    refine ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ ?_⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      MonoidHom.codRestrict_apply]
  exact .of_equiv _ MulChar.equivToUnitHom.symm

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

end MulChar
