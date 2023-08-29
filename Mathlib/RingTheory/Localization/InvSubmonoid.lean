/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Basic

#align_import ring_theory.localization.inv_submonoid from "leanprover-community/mathlib"@"6e7ca692c98bbf8a64868f61a67fb9c33b10770d"

/-!
# Submonoid of inverses

## Main definitions

 * `IsLocalization.invSubmonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
   each element `x ∈ M`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

open Function

open BigOperators

namespace IsLocalization

section InvSubmonoid

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).leftInv
#align is_localization.inv_submonoid IsLocalization.invSubmonoid

variable [IsLocalization M S]

theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  -- ⊢ ↑(algebraMap R S) a ∈ IsUnit.submonoid S
  exact IsLocalization.map_units S ⟨_, ha⟩
  -- 🎉 no goals
#align is_localization.submonoid_map_le_is_unit IsLocalization.submonoid_map_le_is_unit

/-- There is an equivalence of monoids between the image of `M` and `invSubmonoid`. -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm
#align is_localization.equiv_inv_submonoid IsLocalization.equivInvSubmonoid

/-- There is a canonical map from `M` to `invSubmonoid` sending `x` to `1 / x`. -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)
#align is_localization.to_inv_submonoid IsLocalization.toInvSubmonoid

theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)
#align is_localization.to_inv_submonoid_surjective IsLocalization.toInvSubmonoid_surjective

@[simp]
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _
#align is_localization.to_inv_submonoid_mul IsLocalization.toInvSubmonoid_mul

@[simp]
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩
#align is_localization.mul_to_inv_submonoid IsLocalization.mul_toInvSubmonoid

@[simp]
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert mul_toInvSubmonoid M S m
  -- ⊢ HSMul.hSMul m = HMul.hMul (↑(algebraMap R S) ↑m)
  ext
  -- ⊢ m • x✝ = ↑(algebraMap R S) ↑m * x✝
  rw [← Algebra.smul_def]
  -- ⊢ m • x✝ = ↑m • x✝
  rfl
  -- 🎉 no goals
#align is_localization.smul_to_inv_submonoid IsLocalization.smul_toInvSubmonoid

variable {S}

-- Porting note: `surj'` was taken, so use `surj''` instead
theorem surj'' (z : S) : ∃ (r : R) (m : M), z = r • (toInvSubmonoid M S m : S) := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  -- ⊢ ∃ r m, z = r • ↑(↑(toInvSubmonoid M S) m)
  refine' ⟨r, m, _⟩
  -- ⊢ z = r • ↑(↑(toInvSubmonoid M S) m)
  rw [Algebra.smul_def, ← e, mul_assoc]
  -- ⊢ z = z * (↑(algebraMap R S) ↑(r, m).snd * ↑(↑(toInvSubmonoid M S) m))
  simp
  -- 🎉 no goals
#align is_localization.surj' IsLocalization.surj''

theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  -- ⊢ ↑(↑(toInvSubmonoid M S) x) * ↑(algebraMap R S) ↑x = mk' S 1 x * ↑(algebraMap …
  simp
  -- 🎉 no goals
#align is_localization.to_inv_submonoid_eq_mk' IsLocalization.toInvSubmonoid_eq_mk'

theorem mem_invSubmonoid_iff_exists_mk' (x : S) :
    x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x := by
  simp_rw [← toInvSubmonoid_eq_mk']
  -- ⊢ x ∈ invSubmonoid M S ↔ ∃ m, ↑(↑(toInvSubmonoid M S) m) = x
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩
#align is_localization.mem_inv_submonoid_iff_exists_mk' IsLocalization.mem_invSubmonoid_iff_exists_mk'

variable (S)

theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  -- ⊢ ⊤ ≤ Submodule.span R ↑(invSubmonoid M S)
  rintro x -
  -- ⊢ x ∈ Submodule.span R ↑(invSubmonoid M S)
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  -- ⊢ r • ↑(↑(toInvSubmonoid M S) m) ∈ Submodule.span R ↑(invSubmonoid M S)
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)
  -- 🎉 no goals
#align is_localization.span_inv_submonoid IsLocalization.span_invSubmonoid

theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S := by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  -- ⊢ Algebra.FiniteType R S
  rw [Monoid.fg_iff_submonoid_fg] at this
  -- ⊢ Algebra.FiniteType R S
  rcases this with ⟨s, hs⟩
  -- ⊢ Algebra.FiniteType R S
  refine' ⟨⟨s, _⟩⟩
  -- ⊢ Algebra.adjoin R ↑s = ⊤
  rw [eq_top_iff]
  -- ⊢ ⊤ ≤ Algebra.adjoin R ↑s
  rintro x -
  -- ⊢ x ∈ Algebra.adjoin R ↑s
  change x ∈ (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  -- ⊢ x ∈ ↑(↑Subalgebra.toSubmodule (Algebra.adjoin R ↑s))
  rw [Algebra.adjoin_eq_span, hs, span_invSubmonoid]
  -- ⊢ x ∈ ↑⊤
  trivial
  -- 🎉 no goals
#align is_localization.finite_type_of_monoid_fg IsLocalization.finiteType_of_monoid_fg

end InvSubmonoid

end IsLocalization
