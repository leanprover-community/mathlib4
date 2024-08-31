/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of root pairings
This file defines the category of root pairings, following the definition of category of root data
given in SGA III Exp. 21 Section 6.
## Main definitions:
 * `RootPairingCat`: Objects are root pairings.
 * `Hom`: A morphism of root data is a linear map of weight spaces, its transverse on coweight
   spaces, and a bijection on the set that indexes roots and coroots.
 * `Hom.id`: The identity morphism.
 * `Hom.comp`: The composite of two morphisms.

## TODO

 * Special types of morphisms: Isogenies, weight/coweight space embeddings
 * Radicals
 * Products and irreducibility
 * Weyl group reimplementation?

## Implementation details

This is mostly copied from `ModuleCat`.

-/

open Set Function CategoryTheory

noncomputable section

universe v u

variable {R : Type u} [CommRing R]

/-- The category of root pairings. -/
structure RootPairingCat (R : Type u) [CommRing R] where
  /-- The weight space of a root pairing. -/
  weight : Type v
  [weightIsAddCommGroup : AddCommGroup weight]
  [weightIsModule : Module R weight]
  /-- The coweight space of a root pairing. -/
  coweight : Type v
  [coweightIsAddCommGroup : AddCommGroup coweight]
  [coweightIsModule : Module R coweight]
  /-- The set that indexes roots and coroots. -/
  index : Type v
  /-- The root pairing structure. -/
  pairing : RootPairing index R weight coweight

attribute [instance] RootPairingCat.weightIsAddCommGroup RootPairingCat.weightIsModule
attribute [instance] RootPairingCat.coweightIsAddCommGroup RootPairingCat.coweightIsModule

namespace RootPairingCat

/-- A morphism of root pairings is a pair of mutually transposed maps of weight and coweight spaces
that preserves roots and coroots.  We make the map of indexing sets explicit. -/
@[ext]
structure Hom (P Q : RootPairingCat R) where
  /-- A linear map on weight space. -/
  weight_map : P.weight →ₗ[R] Q.weight
  /-- A contravariant linear map on coweight space. -/
  coweight_map : Q.coweight →ₗ[R] P.coweight
  /-- A bijection on index sets. -/
  index_map : P.index ≃ Q.index
  weight_coweight_transpose :
    LinearMap.dualMap weight_map =
      P.pairing.toDualRight ∘ₗ coweight_map ∘ₗ Q.pairing.toDualRight.symm
  root_weight_map : weight_map ∘ P.pairing.root = Q.pairing.root ∘ index_map
  coroot_coweight_map : coweight_map ∘ Q.pairing.coroot = P.pairing.coroot ∘ index_map.symm

/-- The identity morphism of a root pairing. -/
@[simps!]
def Hom.id (P : RootPairingCat R) : Hom P P where
  weight_map := LinearMap.id
  coweight_map := LinearMap.id
  index_map := Equiv.refl P.index
  weight_coweight_transpose := by simp
  root_weight_map := by simp
  coroot_coweight_map := by simp

/-- Composition of morphisms -/
@[simps!]
def Hom.comp {P P₁ P₂ : RootPairingCat R} (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where
  weight_map := g.weight_map ∘ₗ f.weight_map
  coweight_map := f.coweight_map ∘ₗ g.coweight_map
  index_map := f.index_map.trans g.index_map
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap, f.weight_coweight_transpose, g.weight_coweight_transpose,
      ← LinearMap.comp_assoc _ f.coweight_map, ← LinearMap.comp_assoc]
    nth_rw 2 [LinearMap.comp_assoc]
    simp
  root_weight_map := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.coe_trans]
    rw [comp.assoc, f.root_weight_map, ← comp.assoc, g.root_weight_map, comp.assoc]
  coroot_coweight_map := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.symm_trans_apply]
    rw [comp.assoc, g.coroot_coweight_map, ← comp.assoc, f.coroot_coweight_map, comp.assoc]
    simp

@[simp]
lemma Hom.id_comp {P P₁ : RootPairingCat R} (f : Hom P P₁) :
    Hom.comp f (Hom.id P) = f := by
  ext x <;> simp

@[simp]
lemma Hom.comp_id {P P₁ : RootPairingCat R} (f : Hom P P₁) :
    Hom.comp (Hom.id P₁) f = f := by
  ext x <;> simp

@[simp]
lemma Hom.comp_assoc {P P₁ P₂ P₃ : RootPairingCat R} (f : Hom P P₁) (g : Hom P₁ P₂)
    (h : Hom P₂ P₃) : Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  ext <;> simp

instance category : Category.{v, max (v+1) u} (RootPairingCat.{v} R) where
  Hom P Q := Hom P Q
  id P := Hom.id P
  comp f g := Hom.comp g f

/-- The endomorphism of a root pairing given by a reflection. -/
@[simps!]
def reflection_hom {P : RootPairingCat R} (i : P.index) : Hom P P where
  weight_map := P.pairing.reflection i
  coweight_map := P.pairing.coreflection i
  index_map := P.pairing.reflection_perm i
  weight_coweight_transpose := by
    ext f x
    simp only [LinearMap.dualMap_apply, LinearEquiv.coe_coe, LinearEquiv.comp_coe,
      LinearEquiv.trans_apply]
    rw [RootPairing.reflection_apply, RootPairing.coreflection_apply]
    simp [PerfectPairing.toLin_apply, mul_comm]
  root_weight_map := by ext; simp
  coroot_coweight_map := by ext; simp

end RootPairingCat
