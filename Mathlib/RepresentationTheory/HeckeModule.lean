/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Induction

This files defines Hecke algebras and Hecke modules.

-/

@[expose] public section

namespace Representation

section

variable {G H : Type*} [Group G] [Group H]
variable {k : Type*} [CommRing k]
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
variable {W : Type*} [AddCommGroup W] [Module k W] {σ : Representation k H W}

noncomputable def IntertwiningMap.resToInd (φ : H →* G) (f : IntertwiningMap σ (ρ.comp φ)) :
    IntertwiningMap (ind φ σ) ρ :=
  ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => ρ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun h ↦ by
      ext g x
      have : f ((σ h x)) = ρ (φ h) (f x) := by
        exact congrArg (fun f ↦ f x) (f.2 h)
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, this], fun g ↦ by ext; simp [ind_apply]⟩

/-- `IndV.mk` is an `abbrev` so we do not put `@[simp]` here. -/
lemma IntertwiningMap.resToInd_apply_IndVMk_trivial_eq (φ : H →* G) (g : G) (w : W)
    (f : IntertwiningMap σ (ρ.comp φ)) :
    IntertwiningMap.resToInd φ f (IndV.mk φ σ g w) = ρ g⁻¹ (f w) := by
  simp [resToInd]

variable (k)

noncomputable def cosetVector (H : Subgroup G) (g : G) :
    IndV H.subtype (trivial k H k) := IndV.mk H.subtype (trivial k H k) g 1

@[simp]
lemma ind_apply_cosetVector (H : Subgroup G) (g₁ g₂ : G) :
    ind H.subtype (trivial k H k) g₁ (cosetVector k H g₂) = cosetVector k H (g₂ * g₁⁻¹) := by
  exact ind_mk _ _ g₁ g₂ 1

@[simp]
lemma ind_apply_subgroup_cosetVector_one {H : Subgroup G} (h : H) :
    ind H.subtype (trivial k H k) h (cosetVector k H 1) = cosetVector k H 1 := by
  rw [ind_apply_cosetVector, one_mul, cosetVector, cosetVector]
  convert IndV.mk_map_inv_mul H.subtype (trivial k H k) h 1 1
  · simp
  · simp

lemma IntertwiningMap.surjective_cosetVector_one {H : Subgroup G}
    (f : IntertwiningMap ρ (ind H.subtype (trivial k H k))) {v : V} (h : f v = cosetVector k H 1) :
    Function.Surjective f := by
  intro x
  refine IndV.induction_on x ?_ ?_
  · intro g r
    use r • (ρ g⁻¹ v)
    rw [map_smul, IntertwiningMap.isIntertwining, h, ind_apply_cosetVector, cosetVector, ← map_smul,
      smul_eq_mul, mul_one, one_mul, inv_inv]
  · intro _ _ ⟨v, hv⟩ ⟨w, hw⟩
    use v + w
    rw [map_add, hv, hw]

@[simp]
lemma IntertwiningMap.resToInd_apply_cosetVector_eq (H : Subgroup G) (g : G)
    (f : IntertwiningMap (trivial k H k) (ρ.comp H.subtype)) :
    IntertwiningMap.resToInd H.subtype f (cosetVector k H g) = ρ g⁻¹ (f 1) := by
  exact IntertwiningMap.resToInd_apply_IndVMk_trivial_eq H.subtype g 1 f

noncomputable def bimoduleHecke₁.canonicalIntertwiningMap {H1 H2 : Subgroup G} (h : H1 ≤ H2) :
    IntertwiningMap (ind H1.subtype (trivial k H1 k)) (ind H2.subtype (trivial k H2 k)) :=
  IntertwiningMap.resToInd H1.subtype
    ⟨LinearMap.toSpanSingleton k _ (cosetVector k H2 1), fun g ↦ by
      ext
      rw [isTrivial_def, LinearMap.comp_id, LinearMap.toSpanSingleton_apply, one_smul,
        LinearMap.coe_comp ((MonoidHom.comp (ind H2.subtype (trivial k (↥H2) k)) H1.subtype) g),
        Function.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, MonoidHom.comp_apply,
        cosetVector, ind_mk, one_mul, ← mul_one (H1.subtype g)⁻¹]
      exact (IndV.mk_map_inv_mul H2.subtype _ ⟨g, h g.2⟩ 1 1).symm⟩

lemma bimoduleHecke₁.canonicalIntertwiningMap_apply_cosetVector_one_eq {H1 H2 : Subgroup G}
    (h : H1 ≤ H2) :
    bimoduleHecke₁.canonicalIntertwiningMap k h (cosetVector k H1 1) = cosetVector k H2 1 := by
  unfold bimoduleHecke₁.canonicalIntertwiningMap
  rw [IntertwiningMap.resToInd_apply_cosetVector_eq, IntertwiningMap.coe_mk,
    LinearMap.toSpanSingleton_apply, one_smul, ind_apply_cosetVector, one_mul, inv_one, inv_one]

@[simp]
lemma bimoduleHecke₁.canonicalIntertwiningMap_apply_cosetVector_eq {H1 H2 : Subgroup G}
    (h : H1 ≤ H2) (g : G) :
    bimoduleHecke₁.canonicalIntertwiningMap k h (cosetVector k H1 g) = cosetVector k H2 g := by
  rw [← inv_inv g, ← one_mul g⁻¹⁻¹, ← ind_apply_cosetVector, ← ind_apply_cosetVector,
    ← bimoduleHecke₁.canonicalIntertwiningMap_apply_cosetVector_one_eq k h,
    IntertwiningMap.isIntertwining]

end

universe u v
variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]
variable {W : Type u} [AddCommGroup W] [Module k W]
variable (H : Subgroup G) (σ : Representation k H V) (ρ : Representation k G W)

noncomputable section

/-- The twisted Hecke algebra with respect to a representation of a subgroup `H`. -/
abbrev algebraHecke : Type u := (ind H.subtype σ).IntertwiningMap (ind H.subtype σ)

/-- The opposite algebra of the twisted Hecke algebra. -/
abbrev algebraHeckeOp := (MulOpposite (algebraHecke H σ))

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev moduleHecke : Type u := (ind H.subtype σ).IntertwiningMap ρ

variable (k)

/-- The standard Hecke algebra of subgroup `H`. -/
abbrev algebraHecke₁ := algebraHecke H (trivial k H k)

/-- The opposite algebra of the standard Hecke algebra. -/
abbrev algebraHecke₁Op := MulOpposite (algebraHecke₁ k H)

variable {k}

/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev moduleHecke₁ := (ind H.subtype (trivial k H k)).IntertwiningMap ρ

/-- The standard Hecke bimodule. -/
abbrev bimoduleHecke₁ (H1 H2 : Subgroup G) : Type u :=
  moduleHecke₁ H1 (ind H2.subtype (trivial k H2 k))

namespace Rep

open CategoryTheory

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev toHeckeModule (A : Rep k G) : ModuleCat (algebraHeckeOp H σ) :=
  ModuleCat.of (algebraHeckeOp H σ) (moduleHecke H σ A.ρ)

/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev toHecke₁Module (A : Rep k G) : ModuleCat (algebraHecke₁Op k H) :=
  ModuleCat.of (algebraHecke₁Op k H) (moduleHecke₁ H A.ρ)

/-- The induced map between Hecke modules from a morphism between represeentations. -/
abbrev toHeckeModuleMap {A B : Rep k G} (f : A ⟶ B) : toHeckeModule H σ A ⟶ toHeckeModule H σ B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

/-- The induced map between Hecke modules over the opposite standard Hecke algebra from a morphism
between representations. -/
abbrev toHecke₁ModuleMap {A B : Rep k G} (f : A ⟶ B) : toHecke₁Module H A ⟶ toHecke₁Module H B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

/-- The functor sending represenations to Hecke modules over the opposite twisted Hecke algbera. -/
abbrev toHeckeModuleFunctor : Rep k G ⥤ ModuleCat (algebraHeckeOp H σ) where
  obj := toHeckeModule H σ
  map := toHeckeModuleMap H σ

/-- The functor sending represenations to Hecke modules over the opposite standard Hecke algbera. -/
abbrev toHecke₁ModuleFunctor : Rep k G ⥤ ModuleCat (algebraHecke₁Op k H) where
  obj := toHecke₁Module H
  map := toHecke₁ModuleMap H

end Rep

end

end Representation
