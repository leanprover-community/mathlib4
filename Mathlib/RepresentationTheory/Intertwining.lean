/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Intertwining maps

This file gives defines intertwining maps of representations (aka equivariant linear maps).

-/

@[expose] public section

open scoped MonoidAlgebra

namespace Representation

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module A V] [Module A W] (ρ : Representation A G V) (σ : Representation A G W)
  (f : V →ₗ[A] W)

/-- An unbundled version of `IntertwiningMap`. -/
@[mk_iff] structure IsIntertwiningMap : Prop where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/-- An intertwining map between two representations `ρ` and `σ` of the same monoid `G` is a map
  between underlying modules which commutes with the `G`-actions. -/
@[ext] structure IntertwiningMap extends V →ₗ[A] W where
  /-- An underlying `A`-linear map of the underlying `A`-modules. -/
  isIntertwining' (g : G) (v : V) : toFun (ρ g v) = σ g (toFun v)

namespace IntertwiningMap

lemma toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap := by
  intro f g h
  ext x
  exact congrFun (congrArg DFunLike.coe h) x

lemma toFun_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap.toFun := by
  intro f g h
  ext x
  exact congrFun h x

instance : FunLike (IntertwiningMap ρ σ) V W where
  coe f := f.toFun
  coe_injective' := toFun_injective ρ σ

lemma isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) := f.isIntertwining' g v

@[simp] theorem toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v  = f v := rfl

instance : Zero (IntertwiningMap ρ σ) := ⟨⟨0, by simp⟩⟩

@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V → W) = 0 := rfl

instance : Add (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ ⟨f.toLinearMap + g.toLinearMap, by simp [f.isIntertwining, g.isIntertwining]⟩⟩

@[simp] lemma coe_add (f g : IntertwiningMap ρ σ) :
    ((f + g : IntertwiningMap ρ σ) : V → W) = f + g := rfl

instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f ↦ ⟨a • f.toLinearMap, by simp [f.isIntertwining]⟩⟩

@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V → W) = a • f := rfl

instance : SMul ℕ (IntertwiningMap ρ σ) :=
  ⟨fun n f ↦ ⟨n • f.toLinearMap, by simp [f.isIntertwining]⟩⟩

@[simp] lemma coe_nsmul (n : ℕ) (f : IntertwiningMap ρ σ) :
    ((n • f : IntertwiningMap ρ σ) : V → W) = n • f := rfl

instance instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

/-- A coercion from intertwining maps to additive monoid homomorphisms. -/
def coeFnAddMonoidHom : IntertwiningMap ρ σ →+ V → W where
  toFun := (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

instance : Module A (IntertwiningMap ρ σ) :=
  fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

/-- An intertwining map is the same thing as a linear map over the group ring. -/
def equivLinearMapAsModule :
    IntertwiningMap ρ σ ≃ₗ[A] ρ.asModule →ₗ[A[G]] σ.asModule where
  toFun f :=
    { toFun := f.toLinearMap
      map_add' := f.toLinearMap.map_add'
      map_smul' m v := by
        induction m using MonoidAlgebra.induction_linear with
          | zero => simp [f.toLinearMap.map_zero]
          | add x y hx hy => simp [add_smul, map_add, hx, hy]
          | single g a => simp [f.isIntertwining]; rfl}
  invFun f :=
    { toLinearMap := { f with
        map_smul' a v := by simp }
      isIntertwining' g v := by simpa using f.map_smul' (MonoidAlgebra.single g 1) v }
  map_add' g₁ g₂ := by ext; simp
  map_smul' t g := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

/-- The identity map, considered as an intertwining map from a representation to itself. -/
noncomputable def id : IntertwiningMap ρ ρ where
  toLinearMap := LinearMap.id
  isIntertwining' := by simp

@[simp] lemma id_apply (v : V) : IntertwiningMap.id ρ v = v := rfl

theorem isIntertwiningMap_of_mem_center (g : G) (hg : g ∈ Submonoid.center G) :
    IsIntertwiningMap ρ ρ (ρ g) := by
  rw [isIntertwiningMap_iff]
  intro g' v
  rw [Submonoid.mem_center_iff] at hg
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← ρ.map_mul, ← hg g', ρ.map_mul]

/-- If `g` is a central element of a monoid `G`, then this is the action of `g`, considered as an
  intertwining map from any representation of `G` to itself. -/
def centralMul (g : G) (hg : g ∈ Submonoid.center G) : IntertwiningMap ρ ρ where
  toLinearMap := ρ g
  isIntertwining' := (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining

end IntertwiningMap

end Representation
