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

lemma weight_coweight_transpose_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (x : N₂) (f : Hom P Q) :
    f.weightMap.dualMap (Q.toDualRight x) = P.toDualRight (f.coweightMap x) :=
  Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x

lemma root_weightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι) (f : Hom P Q) :
    f.weightMap (P.root i) = Q.root (f.indexEquiv i) :=
  Eq.mp (propext funext_iff) f.root_weightMap i

lemma coroot_coweightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι₂) (f : Hom P Q) :
    f.coweightMap (Q.coroot i) = P.coroot (f.indexEquiv.symm i) :=
  Eq.mp (propext funext_iff) f.coroot_coweightMap i

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

/-- The weight space representation of endomorphisms -/
def weightEndHom (P : RootPairing ι R M N) : End P →* (M →ₗ[R] M) where
  toFun g := Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp

lemma weightEndHom_injective (P : RootPairing ι R M N) : Injective P.weightEndHom := by
  intro f g hfg
  ext x
  · exact congrFun (congrArg DFunLike.coe hfg) x
  · refine (LinearEquiv.injective P.toDualRight) ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.toDualRight x)
  · refine (Embedding.injective P.root) ?_
    simp_rw [← root_weightMap_apply]
    exact congrFun (congrArg DFunLike.coe hfg) (P.root x)

/-- The weight space representation of automorphisms -/
def weightHom (P : RootPairing ι R M N) : Aut P →* (M ≃ₗ[R] M) :=
  MonoidHom.comp (Module.endUnitsToModuleAutEquiv R M) (Units.map (weightEndHom P))

lemma weightHom_injective (P : RootPairing ι R M N) : Injective P.weightHom :=
  (EquivLike.comp_injective (Units.map P.weightEndHom)
    (Module.endUnitsToModuleAutEquiv R M)).mpr <| Units.map_injective P.weightEndHom_injective

/-- The coweight space representation of endomorphisms -/
def coweightEndHom (P : RootPairing ι R M N) : End P →* (N →ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, LinearMap.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, LinearMap.one_eq_id]

lemma coweightEndHom_injective (P : RootPairing ι R M N) : Injective P.coweightEndHom := by
  intro f g hfg
  ext x
  · dsimp [coweightEndHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M)
        (σ₂₃ := RingHom.id R) (P.toDualRight)) hfg
    rw [← f.weight_coweight_transpose, ← g.weight_coweight_transpose] at h
    have : f.weightMap = g.weightMap := by
      haveI refl : Module.IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
      exact (Module.dualMap_dualMap_eq_iff R M (Bijective.injective
        (Module.bijective_dual_eval R M))).mp (congrArg LinearMap.dualMap
        ((LinearEquiv.eq_comp_toLinearMap_iff f.weightMap.dualMap g.weightMap.dualMap).mp h))
    exact congrFun (congrArg DFunLike.coe this) x
  · dsimp [coweightEndHom] at hfg
    simp_all only [MulOpposite.op_inj]
  · dsimp [coweightEndHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    set y := f.indexEquiv x with hy
    have : f.coweightMap (P.coroot y) = g.coweightMap (P.coroot y) := by
      exact congrFun (congrArg DFunLike.coe hfg) (P.coroot y)
    rw [coroot_coweightMap_apply, coroot_coweightMap_apply, Embedding.apply_eq_iff_eq, hy] at this
    rw [Equiv.symm_apply_apply] at this
    rw [this, Equiv.apply_symm_apply]

/-- The coweight space representation of automorphisms -/
def coweightHom (P : RootPairing ι R M N) : Aut P →* (N ≃ₗ[R] N)ᵐᵒᵖ :=
  MonoidHom.comp (N := (N →ₗ[R] N)ˣᵐᵒᵖ) (MulEquiv.op (Module.endUnitsToModuleAutEquiv R N))
    (MonoidHom.comp (Units.opEquiv (M := (N →ₗ[R] N))) (Units.map (coweightEndHom P)))

lemma coweightHom_injective (P : RootPairing ι R M N) : Injective P.coweightHom :=
  (EquivLike.comp_injective (⇑Units.opEquiv ∘ ⇑(Units.map P.coweightEndHom))
          (MulEquiv.op (Module.endUnitsToModuleAutEquiv R N))).mpr <|
    (EquivLike.comp_injective (⇑(Units.map P.coweightEndHom)) Units.opEquiv).mpr <|
      Units.map_injective P.coweightEndHom_injective

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

/-- The automorphism of a root pairing given by reflection. -/
def Hom.reflectionEquiv (P : RootPairing ι R M N) (i : ι) : Aut P where
  val := Hom.reflection P i
  inv := Hom.reflection P i
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

-- TODO: redefine Weyl group

end RootPairing
