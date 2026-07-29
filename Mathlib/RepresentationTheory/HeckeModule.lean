/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.Index
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
abbrev bimoduleHecke₁ (H₁ H₂ : Subgroup G) := moduleHecke₁ H₁ (ind H₂.subtype (trivial k H₂ k))

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

/-- The vector of characteristic function on the right coset `Hg`. -/
noncomputable def cosetVector₁ (H : Subgroup G) (g : G) :
    IndV H.subtype (trivial k H k) := IndV.mk H.subtype (trivial k H k) g 1

@[simp]
lemma ind_apply_cosetVector₁ (H : Subgroup G) (g₁ g₂ : G) :
    ind H.subtype (trivial k H k) g₁ (cosetVector₁ k H g₂) = cosetVector₁ k H (g₂ * g₁⁻¹) := by
  exact ind_mk _ _ g₁ g₂ 1

/-- A rewrite lemma. -/
lemma cosetVector₁_eq_ind_apply (H : Subgroup G) (g : G) :
    cosetVector₁ k H g = ind H.subtype (trivial k H k) g⁻¹ (cosetVector₁ k H 1) := by
  simp

@[simp]
lemma cosetVector₁_subgroup_mul_eq {H : Subgroup G} (h : H) (g : G) :
    cosetVector₁ k H (h * g) = cosetVector₁ k H g := by
  unfold cosetVector₁
  convert IndV.mk_map_inv_mul H.subtype (trivial k H k) h⁻¹ g 1
  · simp
  · simp

@[simp]
lemma cosetVector₁_subgroup_eq {H : Subgroup G} (h : H) :
    cosetVector₁ k H h = cosetVector₁ k H 1 := by
  rw [← mul_one h]
  exact cosetVector₁_subgroup_mul_eq k h 1

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

variable {k}

@[simp]
lemma IntertwiningMap.indTo_apply_cosetVector₁_eq (H : Subgroup G) (g : G)
    (f : IntertwiningMap (trivial k H k) (ρ.comp H.subtype)) :
    IntertwiningMap.indTo H.subtype f (cosetVector₁ k H g) = ρ g⁻¹ (f 1) := by
  exact IntertwiningMap.indTo_apply_IndVMk_trivial_eq H.subtype g 1 f

noncomputable def moduleHecke₁.invariantMk (H : Subgroup G) (v : V) (h : ∀ (g : H), ρ g v = v) :
    moduleHecke₁ H ρ :=
  IntertwiningMap.indTo H.subtype ⟨LinearMap.toSpanSingleton k _ v, fun g => by ext; simp [h g]⟩

@[simp]
lemma moduleHecke₁.invariantMk_apply_cosetVector₁ (H : Subgroup G) (v : V) (g : G)
    (h : ∀ (g : H), ρ g v = v) :
    moduleHecke₁.invariantMk H v h (cosetVector₁ k H g) = ρ g⁻¹ v := by
  simp [invariantMk]

@[ext]
lemma moduleHecke₁.ext {H : Subgroup G} (f g : moduleHecke₁ H ρ)
    (h : f (cosetVector₁ k H 1) = g (cosetVector₁ k H 1)) : f = g := by
  ext x
  have hx : f (cosetVector₁ k H x) = g (cosetVector₁ k H x) := by
    rw [cosetVector₁_eq_ind_apply, IntertwiningMap.isIntertwining, h,
      IntertwiningMap.isIntertwining]
  exact hx

namespace bimoduleHecke₁

variable (k)

/-- The `IntertwiningMap` sending the neutral `cosetVector₁` to the neutral `cosetVector₁`. -/
noncomputable def canonicalIntertwiningMap (H₁ H₂ : Subgroup G) (h : H₁ ≤ H₂) :
    bimoduleHecke₁ k H₁ H₂ :=
  moduleHecke₁.invariantMk H₁ (cosetVector₁ k H₂ 1) (fun g ↦ by
      simpa [comm] using cosetVector₁_subgroup_eq k (H := H₂) ⟨g.val, h g.prop⟩⁻¹)

@[simp]
lemma canonicalIntertwiningMap_apply_cosetVector₁_eq {H₁ H₂ : Subgroup G}
    (h : H₁ ≤ H₂) (g : G) :
    canonicalIntertwiningMap k H₁ H₂ h (cosetVector₁ k H₁ g) = cosetVector₁ k H₂ g := by
  have h_one : canonicalIntertwiningMap k H₁ H₂ h (cosetVector₁ k H₁ 1) = cosetVector₁ k H₂ 1 := by
    simp [canonicalIntertwiningMap]
  rw [cosetVector₁_eq_ind_apply, cosetVector₁_eq_ind_apply _ H₂, ← h_one,
    IntertwiningMap.isIntertwining]

variable (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The `IntertwiningMap` sending the neutral `cosetVector₁ k H₂ 1` to the sum of
`cosetVector₁ k H₁ gᵢ` where `gᵢ` runs through representatives of `⟦H₁∩H₂\H₂⟧`. -/
noncomputable def coCanonicalIntertwiningMap (H₂ H₁ : Subgroup G) [H₁.IsFiniteRelIndex H₂] :
    bimoduleHecke₁ k H₂ H₁ :=
  moduleHecke₁.invariantMk H₂
    (∑ g : Quotient (QuotientGroup.rightRel (H₁.subgroupOf H₂)),
        Quotient.liftOn g (fun x => (cosetVector₁ k H₁ x)) fun _ y ⟨h, heq⟩ => by
          rw [← heq]
          exact cosetVector₁_subgroup_mul_eq k (⟨h.val, h.prop⟩ : H₁) y)
    (fun h => by
      rw [map_sum]
      exact Fintype.sum_equiv
        (Quotient.congr (Equiv.mulRight h⁻¹) (fun _ _ => by simp [QuotientGroup.rightRel_apply])) _
        _ (fun g => Quotient.inductionOn g (fun a => by simp)))

lemma coCanonicalIntertwiningMap_apply_cosetVector₁_eq (H₁ H₂ : Subgroup G) (g : G)
    [H₁.IsFiniteRelIndex H₂] :
    coCanonicalIntertwiningMap k H₂ H₁ (cosetVector₁ k H₂ g) =
    (∑ g' : Quotient (QuotientGroup.rightRel (H₁.subgroupOf H₂)),
      Quotient.liftOn g' (fun x => (cosetVector₁ k H₁ (x * g))) fun _ y ⟨h, heq⟩ => by
        rw [← heq]
        change cosetVector₁ k H₁ ((h * y) * g) = cosetVector₁ k H₁ (y * g)
        rw [mul_assoc]
        exact cosetVector₁_subgroup_mul_eq k (⟨h.val, h.prop⟩ : H₁) (y * g)) := by
  rw [cosetVector₁_eq_ind_apply, IntertwiningMap.isIntertwining, coCanonicalIntertwiningMap,
    moduleHecke₁.invariantMk_apply_cosetVector₁, map_sum, map_sum]
  exact Fintype.sum_congr _ _ (fun x => Quotient.inductionOn x (by simp))

@[simp]
lemma coCanonicalIntertwiningMap_comp_canonicalIntertwiningMap (H₁ H₂ : Subgroup G) (h : H₁ ≤ H₂)
    [H₁.IsFiniteRelIndex H₂] :
    (canonicalIntertwiningMap k H₁ H₂ h).comp (coCanonicalIntertwiningMap k H₂ H₁) =
    H₁.relIndex H₂ := by
  ext
  have heq : (H₁.relIndex H₂ : algebraHecke₁ k H₂) (cosetVector₁ k H₂ 1) =
      ∑ (x : Quotient (QuotientGroup.rightRel (H₁.subgroupOf H₂))), (cosetVector₁ k H₂ 1) := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card,
      ← QuotientGroup.card_quotient_rightRel]
    simp; rfl
  simp only [heq, IntertwiningMap.comp_apply, coCanonicalIntertwiningMap_apply_cosetVector₁_eq,
    mul_one, map_sum]
  exact Fintype.sum_congr _ _ (fun z => Quotient.inductionOn z (by simp))

lemma canonicalIntertwiningMap_comp_coCanonicalIntertwiningMap (H₁ H₂ : Subgroup G) (h : H₁ ≤ H₂)
    [H₁.IsFiniteRelIndex H₂] :
    (coCanonicalIntertwiningMap k H₂ H₁).comp (canonicalIntertwiningMap k H₁ H₂ h)
    (cosetVector₁ k H₁ 1) =
    ∑ (x : Quotient (QuotientGroup.rightRel (H₁.subgroupOf H₂))), x.liftOn
      (fun g => (cosetVector₁ k H₁ g)) (fun x y ⟨h, hxy⟩ => by
        rw [← hxy]
        exact cosetVector₁_subgroup_mul_eq k (⟨h.val, h.prop⟩ : H₁) y) := by
  simp [coCanonicalIntertwiningMap_apply_cosetVector₁_eq]

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
