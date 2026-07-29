/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Induction

This files defines Hecke algebras and Hecke modules.

-/

@[expose] public section

namespace Representation

variable {G : Type*} [Group G]
variable {k : Type*} [CommRing k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {W : Type*} [AddCommGroup W] [Module k W]

noncomputable section hecke

variable (H : Subgroup G) (σ : Representation k H W) (ρ : Representation k G V)

/-- The twisted Hecke algebra with respect to a representation of a subgroup `H`. -/
abbrev algebraHecke := (ind H.subtype σ).IntertwiningMap (ind H.subtype σ)

/-- The opposite algebra of the twisted Hecke algebra. -/
abbrev algebraHeckeOp := (MulOpposite (algebraHecke H σ))

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev moduleHecke := (ind H.subtype σ).IntertwiningMap ρ

variable (k)

/-- The standard Hecke algebra of subgroup `H`. -/
abbrev algebraHecke₁ := algebraHecke H (trivial k H k)

/-- The opposite algebra of the standard Hecke algebra. -/
abbrev algebraHecke₁Op := MulOpposite (algebraHecke₁ k H)

variable {k}

/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev moduleHecke₁ := (ind H.subtype (trivial k H k)).IntertwiningMap ρ

variable (k) in
/-- The standard Hecke bimodule. -/
abbrev bimoduleHecke₁ (H1 H2 : Subgroup G) := moduleHecke₁ H1 (ind H2.subtype (trivial k H2 k))

variable {H : Type*} [Group H] {σ : Representation k H W} {ρ : Representation k G V}

/-- One direction of `resIndEquiv` which we use to construct IntertwiningMaps staring from `ind`. -/
noncomputable def IntertwiningMap.indTo (φ : H →* G) (f : IntertwiningMap σ (ρ.comp φ)) :
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

-- `IndV.mk` is an `abbrev` so no `@[simp]` here.
lemma IntertwiningMap.indTo_apply_IndVMk_trivial_eq (φ : H →* G) (g : G) (w : W)
    (f : IntertwiningMap σ (ρ.comp φ)) :
    IntertwiningMap.indTo φ f (IndV.mk φ σ g w) = ρ g⁻¹ (f w) := by
  simp [indTo]

variable (k)

/-- The characteristic function on the coset `Hg`. -/
noncomputable def cosetVector₁ (H : Subgroup G) (g : G) :
    IndV H.subtype (trivial k H k) := IndV.mk H.subtype (trivial k H k) g 1

@[simp]
lemma ind_apply_cosetVector₁ (H : Subgroup G) (g₁ g₂ : G) :
    ind H.subtype (trivial k H k) g₁ (cosetVector₁ k H g₂) = cosetVector₁ k H (g₂ * g₁⁻¹) := by
  exact ind_mk _ _ g₁ g₂ 1

@[simp]
lemma ind_apply_mul_subgroup_cosetVector₁ {H : Subgroup G} (h : H) (g : G) :
    cosetVector₁ k H (h * g) = cosetVector₁ k H g := by
  unfold cosetVector₁
  convert IndV.mk_map_inv_mul H.subtype (trivial k H k) h⁻¹ g 1
  · simp
  · simp

lemma IntertwiningMap.surjective_cosetVector₁_one {H : Subgroup G}
    (f : IntertwiningMap ρ (ind H.subtype (trivial k H k))) (h : ∃ v, f v = cosetVector₁ k H 1) :
    Function.Surjective f := by
  intro x
  refine IndV.induction_on x ?_ ?_
  · intro g r
    obtain ⟨v, hv⟩ := h
    use r • (ρ g⁻¹ v)
    rw [map_smul, IntertwiningMap.isIntertwining, hv, ind_apply_cosetVector₁, cosetVector₁,
      ← map_smul, smul_eq_mul, mul_one, one_mul, inv_inv]
  · intro _ _ ⟨v, hv⟩ ⟨w, hw⟩
    use v + w
    rw [map_add, hv, hw]

@[simp]
lemma IntertwiningMap.indTo_apply_cosetVector₁_eq (H : Subgroup G) (g : G)
    (f : IntertwiningMap (trivial k H k) (ρ.comp H.subtype)) :
    IntertwiningMap.indTo H.subtype f (cosetVector₁ k H g) = ρ g⁻¹ (f 1) := by
  exact IntertwiningMap.indTo_apply_IndVMk_trivial_eq H.subtype g 1 f

namespace bimoduleHecke₁

/-- The IntertwiningMap sending the neutral cosetVector₁ to the neutral cosetVector₁. -/
noncomputable def canonicalIntertwiningMap {H1 H2 : Subgroup G} (h : H1 ≤ H2) :
    bimoduleHecke₁ k H1 H2 :=
  IntertwiningMap.indTo H1.subtype
    ⟨LinearMap.toSpanSingleton k _ (cosetVector₁ k H2 1), fun g ↦ by
      ext
      rw [isTrivial_def, LinearMap.comp_id, LinearMap.toSpanSingleton_apply, one_smul,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply, one_smul,
        MonoidHom.comp_apply, cosetVector₁, ind_mk, one_mul, ← mul_one (H1.subtype g)⁻¹]
      exact (IndV.mk_map_inv_mul H2.subtype _ ⟨g, h g.2⟩ 1 1).symm⟩

lemma canonicalIntertwiningMap_apply_cosetVector₁_one_eq {H1 H2 : Subgroup G}
    (h : H1 ≤ H2) :
    bimoduleHecke₁.canonicalIntertwiningMap k h (cosetVector₁ k H1 1) = cosetVector₁ k H2 1 := by
  unfold canonicalIntertwiningMap
  rw [IntertwiningMap.indTo_apply_cosetVector₁_eq, IntertwiningMap.coe_mk,
    LinearMap.toSpanSingleton_apply, one_smul, ind_apply_cosetVector₁, one_mul, inv_inv]

@[simp]
lemma canonicalIntertwiningMap_apply_cosetVector₁_eq {H1 H2 : Subgroup G}
    (h : H1 ≤ H2) (g : G) :
    bimoduleHecke₁.canonicalIntertwiningMap k h (cosetVector₁ k H1 g) = cosetVector₁ k H2 g := by
  rw [← inv_inv g, ← one_mul g⁻¹⁻¹, ← ind_apply_cosetVector₁, ← ind_apply_cosetVector₁,
    ← canonicalIntertwiningMap_apply_cosetVector₁_one_eq k h, IntertwiningMap.isIntertwining]

noncomputable def coCanonicalIntertwiningMap {H1 H2 : Subgroup G} [H1.IsFiniteRelIndex H2] :
    bimoduleHecke₁ k H2 H1 :=
  IntertwiningMap.indTo H2.subtype sorry
    --⟨LinearMap.toSpanSingleton k _ (∑ i, cosetVector₁ k H1 (h i)), sorry⟩


end bimoduleHecke₁

end hecke

noncomputable section

namespace Rep

universe u
variable {G : Type u} [Group G]
variable {k : Type u} [CommRing k]
variable (H : Subgroup G)
variable {W : Type u} [AddCommGroup W] [Module k W] (σ : Representation k H W)

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
