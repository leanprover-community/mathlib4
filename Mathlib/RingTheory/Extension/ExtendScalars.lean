/-
Copyright (c) 2024 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Extension of Scalars for Algebra Extensions

This file provides APIs for extending the base ring of an algebra extension `P : Extension R S`
to its own extension ring `P.Ring`. We introduce canonical maps and isomorphisms between
the cotangent spaces and the first homology of naive cotangent complex associated with
`P.extendScalars` and `P`. We provide commutativity results of these maps and ismorphisms
(See https://github.com/leanprover-community/mathlib4/pull/39520 for an image of the full diagram).
In particular, we show the boundary map of the Jacobi-Zariski sequence of `R → P.Ring → S`
coincides with `P.cotangentComplex` via a canonical isomorphism `P.h1CotangentEquivCotangent`.

## Main definitions and results

- `extendScalars`: Views `P : Extension R S` as `Extension P.Ring S`.
- `toExtendScalars`: The canonical homomorphism from `P` to `P.extendScalars` induced by
  the identity map on the underlying extension rings.
- `cotangentExtendScalarsEquiv` : The linear equivalence between the cotangent spaces of
  `P.extensScalars` and `P` induced by the identity map.
- `h1CotangentExtendScalarsEquiv`: `P.extensScalars` can be used to compute the first homology of
  the naive cotangent complex of `S` over `P.Ring`.
- `h1CotangentEquivOfSurjective`: If `R → P.Ring` is surjective, this is the linear isomorphism
  induced by `P.h1Cotangentι`.
- `h1CotangentEquivCotangent`: This is the linear equivalence between `H1Cotangent P.Ring S` and
  `P.Cotangent` defined by the composition of `h1CotangentExtendScalarsEquiv.symm`,
  `h1CotangentEquivOfSurjective` and `cotangentExtendScalarsEquiv`.
- `cotangentComplex_comp_h1CotangentEquivCotangent`,
  `h1CotangentEquivCotangent_comp_map`: commutativity results.

-/

@[expose] public section

open KaehlerDifferential

namespace Algebra.Extension

universe w v u

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Given an extension `P` of `S` over `R`, `P.extendScalars` is the same extension
but viewed as an extension of `S` over `P.Ring`. -/
@[simps]
def extendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : Extension P.Ring S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homomorphism from `P` to `P.extendScalars` induced by the identity map
on the underlying extension rings. -/
@[simps!]
noncomputable
def toExtendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : P.Hom P.extendScalars :=
  .ofAlgHom (IsScalarTower.toAlgHom R P.Ring P.extendScalars.Ring)
    (by dsimp; ext; simp)

/-- `Extension.extendScalars` does not change the cotangent space of an extension. -/
noncomputable
def cotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.Cotangent ≃ₗ[S] P.Cotangent :=
  LinearEquiv.refl _ _

@[simp]
lemma cotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
    P.cotangentExtendScalarsEquiv.symm.toLinearMap = Cotangent.map P.toExtendScalars := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem H1Cotangent.map_toExtendScalars_injective (P : Extension.{w} R S) :
    Function.Injective (H1Cotangent.map P.toExtendScalars) := by
  rw [← LinearMap.ker_eq_bot, H1Cotangent.map, LinearMap.ker_restrict,
    ← cotangentExtendScalarsEquiv_symm_toLinearMap, LinearEquiv.ker,
    Submodule.comap_bot, Submodule.ker_subtype]

/-- The first homology of the naive cotangent complex of `P.extendScalars` is
linearly equivalent to that of `S` over `P.Ring`. -/
@[simps! toLinearMap]
noncomputable
def h1CotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.H1Cotangent ≃ₗ[S] H1Cotangent P.Ring S :=
  Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

@[simp]
lemma h1CotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
  P.h1CotangentExtendScalarsEquiv.symm = H1Cotangent.map P.extendScalars.defaultHom := rfl

/-- Given an extension `P` of `S` over `R` such that `algebraMap R P.Ring` is surjective,
this is the equivalence induced by `P.h1Cotangentι`. -/
@[simps! toLinearMap]
noncomputable
def h1CotangentEquivOfSurjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) (h : Function.Surjective (algebraMap R P.Ring)) :
    P.H1Cotangent ≃ₗ[S] P.Cotangent where
  __ := P.h1Cotangentι
  invFun x := ⟨x, by
    have : Subsingleton Ω[P.Ring⁄R] := subsingleton_of_surjective R P.Ring h
    exact Subsingleton.elim _ _⟩

/-- Given an extension `P : Extension R S`, this is the linear equivalence between
the first homology of the naive cotangent complex of `S` over `P.Ring` and
the cotangent space of `P`. -/
noncomputable
def h1CotangentEquivCotangent {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    H1Cotangent P.Ring S ≃ₗ[S] P.Cotangent :=
  P.h1CotangentExtendScalarsEquiv.symm ≪≫ₗ
    P.extendScalars.h1CotangentEquivOfSurjective Function.surjective_id ≪≫ₗ
    P.cotangentExtendScalarsEquiv

theorem cotangentComplex_comp_h1CotangentEquivCotangent (P : Extension.{w} R S) :
    P.cotangentComplex.comp P.h1CotangentEquivCotangent.toLinearMap =
      H1Cotangent.δ R P.Ring S := by
  rw [h1CotangentEquivCotangent, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    h1CotangentEquivOfSurjective_toLinearMap, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    LinearEquiv.comp_toLinearMap_symm_eq, LinearMap.comp_assoc,
    h1CotangentExtendScalarsEquiv_toLinearMap]
  ext ⟨x, _⟩
  obtain ⟨⟨x : P.Ring, x_in : x ∈ P.ker⟩, rfl⟩ := Cotangent.mk_surjective x
  trans 1 ⊗ₜ[P.Ring] D R P.Ring x; · exact cotangentComplex_mk P ⟨x, x_in⟩
  let u : (Generators.self P.Ring S).toExtension.ker :=
    ⟨algebraMap P.Ring (Generators.self P.Ring S).toExtension.Ring x, by
      rwa [← Ideal.mem_comap, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]⟩
  rw [← Generators.H1Cotangent.δ_C _ _ u.prop]
  congr

theorem h1CotangentEquivCotangent_comp_map (P : Extension.{w} R S) :
    P.h1CotangentEquivCotangent.toLinearMap.comp (Algebra.H1Cotangent.map R P.Ring S S) =
      h1Cotangentι.comp (H1Cotangent.map P.defaultHom) := by
  rw [h1CotangentEquivCotangent, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    h1CotangentExtendScalarsEquiv_symm_toLinearMap, h1CotangentEquivOfSurjective_toLinearMap,
    LinearMap.comp_assoc, LinearMap.comp_assoc, Algebra.H1Cotangent.map,
    ← (H1Cotangent.map P.extendScalars.defaultHom).restrictScalars_self, ← H1Cotangent.map_comp,
    eq_comm, ← LinearEquiv.toLinearMap_symm_comp_eq, cotangentExtendScalarsEquiv_symm_toLinearMap,
    ← LinearMap.comp_assoc, Cotangent.map_comp_h1Cotangentι, LinearMap.restrictScalars_self,
    LinearMap.comp_assoc, ← (H1Cotangent.map P.toExtendScalars).restrictScalars_self,
    ← H1Cotangent.map_comp, H1Cotangent.map_eq]

theorem H1Cotangent.map_defaultHom_surjective (P : Extension.{w} R S) :
    Function.Surjective (H1Cotangent.map P.defaultHom) := by
  rw [← LinearMap.range_eq_top,
    ← (Submodule.map_injective_of_injective h1Cotangentι_injective).eq_iff,
    ← LinearMap.range_comp, ← P.h1CotangentEquivCotangent_comp_map, LinearMap.range_comp,
    ← (Algebra.H1Cotangent.exact_map_δ R P.Ring S).linearMap_ker_eq, Submodule.map_top,
    ← exact_hCotangentι_cotangentComplex.linearMap_ker_eq, Submodule.map_equiv_eq_comap_symm,
    LinearMap.ker, LinearMap.ker, ← Submodule.comap_comp]
  congr
  rw [LinearEquiv.comp_toLinearMap_symm_eq, P.cotangentComplex_comp_h1CotangentEquivCotangent]

end Algebra.Extension
