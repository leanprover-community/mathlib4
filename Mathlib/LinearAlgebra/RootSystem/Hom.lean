/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Morphisms of root pairings
This file defines morphisms of root pairings, following the definition of morphisms of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
 * `Hom`: A morphism of root data is a linear map of weight spaces, its transverse on coweight
   spaces, and a bijection on the set that indexes roots and coroots.
 * `Hom.id`: The identity morphism.
 * `Hom.comp`: The composite of two morphisms.

## TODO

 * Special types of morphisms: Isogenies, weight/coweight space embeddings
 * Weyl group reimplementation?

-/

open Set Function

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A morphism of root pairings is a pair of mutually transposed maps of weight and coweight spaces
that preserves roots and coroots.  We make the map of indexing sets explicit. -/
@[ext]
structure Hom {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) where
  /-- A linear map on weight space. -/
  weightMap : M →ₗ[R] M₂
  /-- A contravariant linear map on coweight space. -/
  coweightMap : N₂ →ₗ[R] N
  /-- A bijection on index sets. -/
  indexEquiv : ι ≃ ι₂
  weight_coweight_transpose : weightMap.dualMap ∘ₗ Q.toDualRight = P.toDualRight ∘ₗ coweightMap
  root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
  coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm

/-- The identity morphism of a root pairing. -/
@[simps!]
def Hom.id (P : RootPairing ι R M N) : Hom P P where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp

/-- Composition of morphisms -/
@[simps!]
def Hom.comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap, ← LinearMap.comp_assoc _ f.coweightMap,
      ← f.weight_coweight_transpose, LinearMap.comp_assoc g.coweightMap,
      ← g.weight_coweight_transpose, ← LinearMap.comp_assoc]
  root_weightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.coe_trans]
    rw [comp_assoc, f.root_weightMap, ← comp_assoc, g.root_weightMap, comp_assoc]
  coroot_coweightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.symm_trans_apply]
    rw [comp_assoc, g.coroot_coweightMap, ← comp_assoc, f.coroot_coweightMap, comp_assoc]
    simp

@[simp]
lemma Hom.id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    Hom.comp f (Hom.id P) = f := by
  ext x <;> simp

@[simp]
lemma Hom.comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    Hom.comp (Hom.id Q) f = f := by
  ext x <;> simp

@[simp]
lemma Hom.comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : Hom P₂ P₃) (g : Hom P₁ P₂) (f : Hom P P₁) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  ext <;> simp

/-- The endomorphism of a root pairing given by a reflection. -/
def Hom.reflection (P : RootPairing ι R M N) (i : ι) : Hom P P where
  weightMap := P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflection_perm i
  weight_coweight_transpose := by
    ext f x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      PerfectPairing.toDualRight_apply, LinearMap.dualMap_apply, PerfectPairing.flip_apply_apply,
      LinearEquiv.comp_coe, LinearEquiv.trans_apply]
    rw [RootPairing.reflection_apply, RootPairing.coreflection_apply]
    simp only [← PerfectPairing.toLin_apply, map_sub, map_smul, LinearMap.sub_apply,
      toLin_toPerfectPairing, LinearMap.smul_apply, smul_eq_mul, sub_right_inj]
    simp only [PerfectPairing.toLin_apply, PerfectPairing.flip_apply_apply, mul_comm]
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp

@[simp]
lemma Hom.reflection_weightMap (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).weightMap = (P.reflection i) := rfl

@[simp]
lemma Hom.reflection_coweightMap (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).coweightMap = (P.coreflection i) := rfl

@[simp]
lemma Hom.reflection_indexEquiv (P : RootPairing ι R M N) (i : ι) :
    (RootPairing.Hom.reflection P i).indexEquiv = P.reflection_perm i := rfl

/-- The endomorphism monoid of a root pairing. -/
instance (P : RootPairing ι R M N) : Monoid (Hom P P) where
  mul := Hom.comp
  mul_assoc := Hom.comp_assoc
  one := Hom.id P
  one_mul := Hom.id_comp P P
  mul_one := Hom.comp_id P P

@[simp]
lemma weightMap_one (P : RootPairing ι R M N) :
    Hom.weightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl

@[simp]
lemma coweightMap_one (P : RootPairing ι R M N) :
    Hom.coweightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl

@[simp]
lemma indexEquiv_one (P : RootPairing ι R M N) :
    Hom.indexEquiv (P := P) (Q := P) 1 = Equiv.refl ι :=
  rfl

@[simp]
lemma weightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    Hom.weightMap (x * y) = Hom.weightMap x ∘ₗ Hom.weightMap y :=
  rfl

@[simp]
lemma coweightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    Hom.coweightMap (x * y) = Hom.coweightMap y ∘ₗ Hom.coweightMap x :=
  rfl

@[simp]
lemma indexEquiv_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    Hom.indexEquiv (x * y) = Hom.indexEquiv x ∘ Hom.indexEquiv y :=
  rfl

/-- The endomorphism monoid of a root pairing. -/
abbrev End (P : RootPairing ι R M N) := Hom P P

/-- The automorphism group of a root pairing. -/
abbrev Aut (P : RootPairing ι R M N) := (End P)ˣ

instance (P : RootPairing ι R M N) : Group (Aut P) := inferInstance

/-- The automorphism of a root pairing given by reflection. -/
def Hom.reflectionEquiv (P : RootPairing ι R M N) (i : ι) : Aut P where
  val := Hom.reflection P i
  inv := Hom.reflection P i
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- The subgroup of automorphisms generated by reflections. -/
def WeylGroup (P : RootPairing ι R M N) : Subgroup (Aut P) :=
    Subgroup.closure (range fun i => Hom.reflectionEquiv P i)

/-!
/-- The weight space representation of a Weyl group. -/
def weylGroupToWeightMap (P : RootPairing ι R M N) : P.WeylGroup →* (M ≃ₗ[R] M) where
  toFun f := {
    toFun := fun x => Hom.weightMap f.1.1 x
    map_add' := fun x y => by simp
    map_smul' := fun r x => by simp
    invFun := fun x => Hom.weightMap f.1.2 x
    left_inv := by
      intro x
      simp only [Units.inv_eq_val_inv]
      rw [← @Hom.comp_weightMap_apply]
      rw [← @Units.inv_eq_val_inv]
      rw?
  }

/-- The permutation representation of a Weyl group on its indexing set. -/
def weylGroupToPerm : P.WeylGroup →* Equiv.Perm ι where
-/
end RootPairing
