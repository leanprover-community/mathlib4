/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Intertwining maps

This file gives defines intertwining maps of representations.

-/

@[expose] public section

open Pointwise
open scoped MonoidAlgebra

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module A V] [Module A W] (ρ : Representation A G V) (σ : Representation A G W)
  (f : V →ₗ[A] W)
/-- An unbundled version of `IntertwiningMap`. -/
@[mk_iff] structure IsIntertwiningMap where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/-- An intertwining map between two representations `ρ` and `σ` of the same monoid `G` is a map
  between underlying modules which commutes with the `G`-actions. -/
@[ext] structure IntertwiningMap where
  /-- An underlying `A`-linear map of the underlying `A`-modules. -/
  toLinearMap : V →ₗ[A] W
  isIntertwining (g : G) (v : V) : toLinearMap (ρ g v) = σ g (toLinearMap v)

lemma to_linear_map_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap :=
    by
  intro f g h
  ext x
  exact congrFun (congrArg DFunLike.coe h) x

lemma to_fun_injective : Function.Injective fun f :
    IntertwiningMap ρ σ ↦ f.toLinearMap.toFun := by
  intro f g h
  ext x
  exact congrFun h x

instance : FunLike (IntertwiningMap ρ σ) V W where
  coe f := f.toLinearMap
  coe_injective' := to_fun_injective ρ σ

theorem intertwiningMap_toLinearMap (f : IntertwiningMap ρ σ) (v : V) : f v = f.toLinearMap v := rfl

instance : Zero (IntertwiningMap ρ σ) :=
  ⟨{ toLinearMap := 0
     isIntertwining := by intro g v; simp }⟩

@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V → W) = 0 := rfl

instance : Add (IntertwiningMap ρ σ) :=
  ⟨fun f g =>
    { toLinearMap := f.toLinearMap + g.toLinearMap
      isIntertwining := by intro γ v; simp [f.isIntertwining, g.isIntertwining] }⟩

@[simp] lemma coe_add (f g : IntertwiningMap ρ σ) :
    ((f + g : IntertwiningMap ρ σ) : V → W) = f + g := rfl

instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f =>
    { toLinearMap := a • f.toLinearMap
      isIntertwining := by
        intro g v
        calc
          (a • f.toLinearMap) (ρ g v) = a • f.toLinearMap (ρ g v) := by
            simp [LinearMap.smul_apply]
          _ = a • σ g (f.toLinearMap v) := by
            simp [f.isIntertwining]
          _ = σ g (a • f.toLinearMap v) := by
            symm
            simp}⟩

@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V → W) = a • f := rfl

instance : SMul ℕ (IntertwiningMap ρ σ) :=
  ⟨fun n f =>
    { toLinearMap := n • f.toLinearMap
      isIntertwining := by
        intro g v
        simp [LinearMap.smul_apply, f.isIntertwining]}⟩

@[simp] lemma coe_nsmul (n : ℕ) (f : IntertwiningMap ρ σ) :
    ((n • f : IntertwiningMap ρ σ) : V → W) = n • f := rfl

instance instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ) :=
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

/-- A coercion from intertwining maps to additive monoid homomorphisms. -/
def coeFnAddMonoidHom : IntertwiningMap ρ σ →+ V → W where
  toFun := (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

instance : Module A (IntertwiningMap ρ σ) :=
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

variable {ρ σ} in
/-- An intertwining map considered an a linear map of corresponding modules over the group
  algebra. -/
def asLinearMap (f : IntertwiningMap ρ σ) : ρ.asModule →ₗ[A[G]] σ.asModule where
  toFun := f.toLinearMap
  map_add' := f.toLinearMap.map_add'
  map_smul' m v := by
    induction m using MonoidAlgebra.induction_linear with
      | zero => simp [f.toLinearMap.map_zero]
      | add x y hx hy => simp [add_smul, hx, hy]
      | single g a => simp [f.isIntertwining]; rfl

variable {ρ σ} in
/-- A linear map between two modules over a group algebra considered as an intertwining map
  between th corresponding representations. -/
def ofLinearMap (f : ρ.asModule →ₗ[A[G]] σ.asModule) : IntertwiningMap ρ σ where
  toLinearMap := { f with
    map_smul' a v := by simp
  }
  isIntertwining g v := by
    simp only [LinearMap.coe_mk]
    have h := f.map_smul' (MonoidAlgebra.single g 1) v
    simp only [Representation.single_smul, one_smul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      RingHom.id_apply] at h
    exact h

/-- The identity map, considered as an intertwining map from a representation to itself. -/
noncomputable def IntertwiningMap.id : IntertwiningMap ρ ρ := ofLinearMap LinearMap.id

@[simp] lemma IntertwiningMap.id_apply (v : V) : IntertwiningMap.id ρ v = v := rfl

theorem as_linear_map_to_linear_map (f : IntertwiningMap ρ σ) : ofLinearMap (asLinearMap f) = f :=
    by ext x; rfl

theorem to_linear_map_as_linear_map (f : ρ.asModule →ₗ[A[G]] σ.asModule) :
  asLinearMap (ofLinearMap f) = f := by ext x; rfl

theorem isIntertwiningMap_of_central (g : G) (hg : g ∈ Submonoid.center G) :
    IsIntertwiningMap ρ ρ (ρ g) := by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  change ((ρ g) * (ρ g')) v = ((ρ g') * (ρ g)) v
  rw [← ρ.map_mul, ← hg g', ρ.map_mul]

/-- If `g` is a central element of a monoid `G`, then this is the action of `g`, considered as an
  intertwining map from any representation of `G` to itself. -/
def IntertwiningMap.CentralMul (g : G) (hg : g ∈ Submonoid.center G) : (IntertwiningMap ρ ρ) where
  toLinearMap := ρ g
  isIntertwining := (isIntertwiningMap_of_central ρ g hg).isIntertwining
