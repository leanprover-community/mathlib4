/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localizations of commutative rings

This file contains various basic results on localizations.

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

 * `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

assert_not_exists Ideal

open Function

namespace Localization

open IsLocalization

variable {ι : Type*} {R : ι → Type*} [∀ i, CommSemiring (R i)]
variable {i : ι} (S : Submonoid (R i))

/-- `IsLocalization.map` applied to a projection homomorphism from a product ring. -/
noncomputable abbrev mapPiEvalRingHom :
    Localization (S.comap <| Pi.evalRingHom R i) →+* Localization S :=
  map (T := S) _ (Pi.evalRingHom R i) le_rfl

open Function in
theorem mapPiEvalRingHom_bijective : Bijective (mapPiEvalRingHom S) := by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := mk'_surjective T x₁
    obtain ⟨r₂, s₂, rfl⟩ := mk'_surjective T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j ↦ ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := mk'_surjective S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

end Localization

section CommSemiring

variable {R : Type*} [CommSemiring R] {M N : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

variable (M S) in
include M in
theorem linearMap_compatibleSMul (N₁ N₂) [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁]
    [Module S N₁] [Module R N₂] [Module S N₂] [IsScalarTower R S N₁] [IsScalarTower R S N₂] :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul f s s' := by
    obtain ⟨r, m, rfl⟩ := mk'_surjective M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

variable (M) in
include M in
-- This is not an instance since the submonoid `M` would become a metavariable in typeclass search.
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps!]
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

end

theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y := by
  simp

theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp

variable (M) in
include M in
protected lemma bijective (f : S →+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q) :
    Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective

end AlgEquiv

section liftAlgHom

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R}
  {S : Type*} [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  {P : Type*} [CommSemiring P] [Algebra A P] [IsLocalization M S]
  {f : R →ₐ[A] P} (hf : ∀ y : M, IsUnit (f y)) (x : S)
include hf

/-- `AlgHom` version of `IsLocalization.lift`. -/
noncomputable def liftAlgHom : S →ₐ[A] P where
  __ := lift hf
  commutes' r := show lift hf (algebraMap A S r) = _ by
    simp [IsScalarTower.algebraMap_apply A R S]

theorem liftAlgHom_toRingHom : (liftAlgHom hf : S →ₐ[A] P).toRingHom = lift hf := rfl

@[simp]
theorem coe_liftAlgHom : ⇑(liftAlgHom hf : S →ₐ[A] P) = lift hf := rfl

theorem liftAlgHom_apply : liftAlgHom hf x = lift hf x := rfl

end liftAlgHom

section AlgEquivOfAlgEquiv

variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R} (S : Type*)
  [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsLocalization M S]
  {P : Type*} [CommSemiring P] [Algebra A P] {T : Submonoid P} (Q : Type*)
  [CommSemiring Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsLocalization T Q]
  (h : R ≃ₐ[A] P) (H : Submonoid.map h M = T)

include H

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M`, `T` respectively,
an isomorphism `h : R ≃ₐ[A] P` such that `h(M) = T` induces an isomorphism of localizations
`S ≃ₐ[A] Q`. -/
@[simps!]
noncomputable def algEquivOfAlgEquiv : S ≃ₐ[A] Q where
  __ := ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]

variable {S Q h}

theorem algEquivOfAlgEquiv_eq_map :
    (algEquivOfAlgEquiv S Q h H : S →+* Q) =
      map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

theorem algEquivOfAlgEquiv_eq (x : R) :
    algEquivOfAlgEquiv S Q h H ((algebraMap R S) x) = algebraMap P Q (h x) := by
  simp

set_option linter.docPrime false in
theorem algEquivOfAlgEquiv_mk' (x : R) (y : M) :
    algEquivOfAlgEquiv S Q h H (mk' S x y) =
      mk' Q (h x) ⟨h y, show h y ∈ T from H ▸ Set.mem_image_of_mem h y.2⟩ := by
  simp [map_mk']

theorem algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv S Q h H).symm =
    algEquivOfAlgEquiv Q S h.symm (show Submonoid.map h.symm T = M by
      rw [← H, ← Submonoid.map_coe_toMulEquiv, AlgEquiv.symm_toMulEquiv,
        ← Submonoid.comap_equiv_eq_map_symm, ← Submonoid.map_coe_toMulEquiv,
        Submonoid.comap_map_eq_of_injective (h : R ≃* P).injective]) := rfl

end AlgEquivOfAlgEquiv

section smul

variable {R : Type*} [CommSemiring R] {S : Submonoid R}
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
variable {M': Type*} [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

/-- If `x` in a `R' = S⁻¹ R`-module `M'`, then for a submodule `N'` of `M'`,
`s • x ∈ N'` if and only if `x ∈ N'` for some `s` in S. -/
lemma smul_mem_iff {N' : Submodule R' M'} {x : M'} {s : S} :
    s • x ∈ N' ↔ x ∈ N' := by
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

end smul

section at_units

variable (R M)

/-- The localization at a module of units is isomorphic to the ring. -/
noncomputable def atUnits (H : M ≤ IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [RingHom.map_mul, ← eq, ← hu, mul_assoc, ← RingHom.map_mul]
    simp

end at_units

end IsLocalization

section

variable (M N)

theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor
  · intro y
    convert (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S → P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    exact id

theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩

theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔
      haveI := (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

variable (S) in
/-- If an algebra is simultaneously localizations for two submonoids, then an arbitrary algebra
is a localization of one submonoid iff it is a localization of the other. -/
theorem isLocalization_iff_of_isLocalization [IsLocalization M S] [IsLocalization N S]
    [Algebra R P] : IsLocalization M P ↔ IsLocalization N P :=
  ⟨fun _ ↦ isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ ↦ isLocalization_of_algEquiv M (algEquiv N S P)⟩

theorem iff_of_le_of_exists_dvd (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) :
    IsLocalization M S ↔ IsLocalization N S :=
  have : IsLocalization N (Localization M) := of_le_of_exists_dvd _ _ h₁ h₂
  isLocalization_iff_of_isLocalization _ _ (Localization M)

end

variable (M)

/-- If `S₁` is the localization of `R` at `M₁` and `S₂` is the localization of
`R` at `M₂`, then every localization `T` of `S₂` at `M₁` is also a localization of
`S₁` at `M₂`, in other words `M₁⁻¹M₂⁻¹R` can be identified with `M₂⁻¹M₁⁻¹R`. -/
lemma commutes (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (M₁ M₂ : Submonoid R)
    [IsLocalization M₁ S₁] [IsLocalization M₂ S₂]
    [IsLocalization (Algebra.algebraMapSubmonoid S₂ M₁) T] :
    IsLocalization (Algebra.algebraMapSubmonoid S₁ M₂) T where
  map_units' := by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units' ⟨a, ha⟩)
  surj' a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units' ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T, ← hz, map_mul, ← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc, hr, mul_assoc, hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul, ← map_mul, mul_assoc, mul_comm _ c, ha, map_mul, map_mul]
    ring

variable (Rₘ Sₙ Rₘ' Sₙ' : Type*) [CommRing Rₘ] [CommRing Sₙ] [CommRing Rₘ'] [CommRing Sₙ']
  [Algebra R Rₘ] [Algebra S Sₙ] [Algebra R Rₘ'] [Algebra S Sₙ'] [Algebra R Sₙ] [Algebra Rₘ Sₙ]
  [Algebra Rₘ' Sₙ'] [Algebra R Sₙ'] (N : Submonoid S) [IsLocalization M Rₘ] [IsLocalization N Sₙ]
  [IsLocalization M Rₘ'] [IsLocalization N Sₙ'] [IsScalarTower R Rₘ Sₙ] [IsScalarTower R S Sₙ]
  [IsScalarTower R Rₘ' Sₙ'] [IsScalarTower R S Sₙ']

theorem algEquiv_comp_algebraMap : (algEquiv N Sₙ Sₙ' : _ →+* Sₙ').comp (algebraMap Rₘ Sₙ) =
      (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') := by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← AlgEquiv.restrictScalars_apply R, AlgEquiv.commutes]

variable {Rₘ} in
theorem algEquiv_comp_algebraMap_apply (x : Rₘ) :
    (algEquiv N Sₙ Sₙ' : _ →+* Sₙ').comp (algebraMap Rₘ Sₙ) x =
    (algebraMap Rₘ' Sₙ').comp (algEquiv M Rₘ Rₘ') x := by
  rw [algEquiv_comp_algebraMap M Rₘ Sₙ Rₘ']


end IsLocalization

namespace Localization

open IsLocalization

theorem mk_natCast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℕ) _

variable [IsLocalization M S]

section

variable (S) (M)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps!]
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

end

nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _

nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _

theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']

theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', algEquiv_symm_mk']

lemma coe_algEquiv :
    (Localization.algEquiv M S : Localization M →+* S) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

lemma coe_algEquiv_symm :
    ((Localization.algEquiv M S).symm : S →+* Localization M) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

end Localization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

theorem mk_intCast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℤ) _

end Localization

open IsLocalization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  letI := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {S} {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
include S
section

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra

noncomputable instance : Algebra (Localization M)
  (Localization (Algebra.algebraMapSubmonoid S M)) := localizationAlgebra M S

instance : IsScalarTower R (Localization M) (Localization (Algebra.algebraMapSubmonoid S M)) :=
  IsScalarTower.of_algebraMap_eq (fun x ↦
    (IsLocalization.map_eq (T := (Algebra.algebraMapSubmonoid S M)) M.le_comap_map x).symm)

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable (S Rₘ Sₘ)

theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

-- can't be simp, as `S` only appears on the RHS
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

variable (M)

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x

theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    IsLocalization.lift (M := M) (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

end

variable (Rₘ Sₘ)

theorem localizationAlgebraMap_def :
    @algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S) =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  rfl

/-- Injectivity of the underlying `algebraMap` descends to the algebra induced by localization. -/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS

end Algebra

end CommRing
