/-
Copyright (c) 2024 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Ring.Pi

/-!
# Localizing a product of commutative rings

## Main Result

 * `injective_of_product_of_localizations` is a theorem stating that the canonical map from a
    localization of a product of rings `R' i `at a monoid `M` to the direct product of
    localizations `R' i` at the projection of `M` onto each corresponding factor is injective.

## Implementation notes

See `Mathlib/RingTheory/Localization/Defs.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, commutative ring, field of fractions
-/

section

open IsLocalization

variable (S : Type*) [CommRing S] {ι : Type*} (R' S' : ι → Type*) [∀ i, CommRing (R' i)]
  [∀ i, CommRing (S' i)] [Algebra (∀ i, R' i) S] [∀ i, Algebra (R' i) (S' i)]
  {M : Submonoid (∀ i, R' i)} [sloc : IsLocalization M S]
  [isloc : ∀ i, IsLocalization (M.map (Pi.evalRingHom R' i)) (S' i)]

/-- Let `M` be a submonoid of a direct product of commutative rings `R' i`, and let `M' i` denote
the projection of `M` onto each corresponding factor. Given a ring homomorphism from the direct
product `∏ R' i` to the product of the localizations of each `R' i` at `M' i`, every `y : M`
maps to a unit under this homomorphism.
-/
lemma isUnit_of_product_of_localizations (y : M) :
    IsUnit ((Pi.ringHom fun i ↦ (algebraMap (R' i) (S' i)).comp (Pi.evalRingHom R' i)) y) := by
  let f' i : (∀i, R' i) →+* S' i := (algebraMap (R' i) (S' i)).comp (Pi.evalRingHom R' i)
  refine isUnit_iff_exists_inv.mpr ?_
  use fun i ↦ Ring.inverse (f' i y)
  rw [mul_comm]
  exact funext fun i ↦ Ring.inverse_mul_cancel (f' i y) ((isloc i).map_units (S' i) ⟨y.1 i,
    Submonoid.mem_map_of_mem (Pi.evalRingHom R' i) y.2⟩)

/-- Let `M` be a submonoid of a direct product of commutative rings `R' i`, and let `M' i` denote
the projection of `M` onto each factor. Then the canonical map from the localization of the direct
product `∏ R' i` at `M` to the direct product of the localizations of each `R' i` at `M' i`
is injective.
-/
theorem injective_of_product_of_localizations [inst : Fintype ι] [DecidableEq ι] :
    Function.Injective (sloc.lift (isUnit_of_product_of_localizations R' S')) := by
  let R := ∀ i, R' i
  let P := ∀ i, S' i
  let f : S →+* P := sloc.lift (isUnit_of_product_of_localizations R' S')
  let f' i : (∀i, R' i) →+* S' i := (algebraMap (R' i) (S' i)).comp (Pi.evalRingHom R' i)
  let f'' : R →+* P := Pi.ringHom f'
  refine (injective_iff_map_eq_zero _ ).mpr ?_
  intro s s₀
  rw [← sloc.mk'_sec S s] at s₀ ⊢
  have h₁ (y : M) (i : ι) : y.1 i ∈ M.map (Pi.evalRingHom R' i) :=
    Submonoid.mem_map_of_mem (Pi.evalRingHom R' i) y.2
  have (x : R × M) : f (mk' S x.1 x.2) = fun i ↦ (isloc i).mk' (S' i) (x.1 i) ⟨x.2.1 i,
    h₁ x.2 i⟩ := by
    refine funext fun i ↦ eq_mk'_iff_mul_eq.mpr ?_
    show _ * f'' _ _ = f'' (x.1) i
    rw [← Pi.mul_apply, ← sloc.lift_eq (isUnit_of_product_of_localizations R' S') ↑x.2,
      ← RingHom.map_mul, mk'_spec, lift_eq (isUnit_of_product_of_localizations R' S') x.1]
  rw [this] at s₀
  apply (sloc.mk'_eq_zero_iff (sec M s).1 (sec M s).2).mpr
  choose m hm using fun i ↦ ((isloc i).mk'_eq_zero_iff ((sec M s).1 i)
    ⟨(sec M s).2.1 i, h₁ (sec M s).2 i⟩).mp (congrFun s₀ i)
  have (i : ι) : ∃ z ∈ M, Pi.evalRingHom R' i z = (m i) := by
    apply (M.mem_map).mp
    exact (m i).2
  choose n hn using this
  use ⟨∏ j : ι, n j, M.prod_mem fun i _ ↦ (hn i).left⟩
  refine funext fun i ↦ ?_
  simp_rw [Pi.mul_apply, Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) n, Pi.mul_apply,
    mul_comm ((n i) i), mul_assoc, ← Pi.evalRingHom_apply R' i (n i), (hn i).right, hm i, mul_zero,
    Pi.zero_apply]

end
