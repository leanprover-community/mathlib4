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

variable {A G V W U : Type*} [CommRing A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U]
  (ρ : Representation A G V) (σ : Representation A G W) (τ : Representation A G U)
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

@[simp]
theorem intertwiningMap_toLinearMap (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v := rfl

instance : Zero (IntertwiningMap ρ σ) :=
  ⟨{ toLinearMap := 0
     isIntertwining := by intro g v; simp }⟩

@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V → W) = 0 := rfl

@[simp]
lemma toLinearMap_zero_eq_zero : (IntertwiningMap.toLinearMap (0 : IntertwiningMap ρ σ)) = 0 := rfl

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

variable {ρ σ τ} in
/-- Composition of intertwining maps. -/
def IntertwiningMap.comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    IntertwiningMap ρ τ where
  toLinearMap := LinearMap.comp f.toLinearMap g.toLinearMap
  isIntertwining γ v := by simp [g.isIntertwining, f.isIntertwining]

@[simp]
lemma toLinearMap_comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
  (IntertwiningMap.comp f g).toLinearMap =  LinearMap.comp f.toLinearMap g.toLinearMap := rfl

instance : Mul (IntertwiningMap ρ ρ) where
  mul := IntertwiningMap.comp

/-- The identity map, considered as an intertwining map from a representation to itself. -/
def IntertwiningMap.id : IntertwiningMap ρ ρ :=
  { toLinearMap := LinearMap.id
    isIntertwining := by intro g v; rfl }

@[simp] lemma IntertwiningMap.id_apply (v : V) : IntertwiningMap.id ρ v = v := by rfl

instance : One (IntertwiningMap ρ ρ) where
  one := IntertwiningMap.id ρ

@[simp] lemma coe_one : ((1 : IntertwiningMap ρ ρ) : V → V) = id := rfl

@[simp] lemma toLinearMap_one : (IntertwiningMap.toLinearMap (1 : IntertwiningMap ρ ρ)) = 1 := rfl

@[simp] lemma toLinearMap_mul (f g : IntertwiningMap ρ ρ) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl

instance (priority := 1) instPow : Pow (IntertwiningMap ρ ρ) ℕ where
  pow f n := npowRec n f

instance instNatCast : NatCast (IntertwiningMap ρ ρ) :=
  ⟨fun n => n • (1 : IntertwiningMap ρ ρ)⟩

@[simp] lemma toLinearMap_pow (f : IntertwiningMap ρ ρ) (n : ℕ) :
    (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  change _ = npowRec n _
  induction n with
  | zero => rfl
  | succ n ih =>
    change (npowRec (n + 1) f).toLinearMap = npowRec (n + 1) f.toLinearMap
    change (npowRec n f).toLinearMap = npowRec n f.toLinearMap at ih
    rw [npowRec, npowRec, toLinearMap_mul, ih]

@[simp] lemma toLinearMap_natCast (n : ℕ) :
    (IntertwiningMap.toLinearMap (n : IntertwiningMap ρ ρ)) = (n : V →ₗ[A] V) := rfl

instance : Semiring (IntertwiningMap ρ ρ) :=
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (to_linear_map_injective ρ ρ) (toLinearMap_zero_eq_zero ρ ρ) (toLinearMap_one (ρ := ρ))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun f n => toLinearMap_pow (ρ := ρ) f n)
    (fun n => toLinearMap_natCast (ρ := ρ) n)

instance : Algebra A (IntertwiningMap ρ ρ) :=
  Algebra.ofModule
    (h₁ := by
      intro a f g
      ext v
      rfl)
    (h₂ := by
      intro a f g
      ext v
      change f.toLinearMap (a • g.toLinearMap v) = a • f.toLinearMap (g.toLinearMap v)
      simp only [intertwiningMap_toLinearMap, map_smul])

@[simp] lemma toLinearMap_algebraMap (a : A) :
    IntertwiningMap.toLinearMap (algebraMap A (IntertwiningMap ρ ρ) a) =
      algebraMap A (Module.End A V) a := by
  ext v
  rfl

variable {ρ σ} in
/-- An intertwining map considered an a linear map of corresponding modules over the group
  algebra. -/
def asLinearMap (f : IntertwiningMap ρ σ) : ρ.asModule →ₗ[A[G]] σ.asModule where
  toFun := f.toLinearMap
  map_add' := f.toLinearMap.map_add'
  map_smul' m v := by
    induction m using MonoidAlgebra.induction_linear with
      | zero => simp [f.toLinearMap.map_zero]
      | add x y hx hy => simp only [add_smul, map_add, hx, hy, RingHom.id_apply]
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

theorem as_linear_map_to_linear_map (f : IntertwiningMap ρ σ) : ofLinearMap (asLinearMap f) = f :=
    by ext x; rfl

theorem to_linear_map_as_linear_map (f : ρ.asModule →ₗ[A[G]] σ.asModule) :
  asLinearMap (ofLinearMap f) = f := by ext x; rfl

variable {ρ σ} in
theorem asLinearMap_bijective : Function.Bijective (asLinearMap (ρ := ρ) (σ := σ)) := by
  have h_left :
      Function.LeftInverse (ofLinearMap (ρ := ρ) (σ := σ))
        (asLinearMap (ρ := ρ) (σ := σ)) := by
    intro f
    exact as_linear_map_to_linear_map (ρ := ρ) (σ := σ) f
  have h_right :
      Function.RightInverse (ofLinearMap (ρ := ρ) (σ := σ))
        (asLinearMap (ρ := ρ) (σ := σ)) := by
    intro f
    exact to_linear_map_as_linear_map (ρ := ρ) (σ := σ) f
  exact ⟨h_left.injective, h_right.surjective⟩

variable {ρ σ} in
theorem ofLinearMap_bijective : Function.Bijective (ofLinearMap (ρ := ρ) (σ := σ)) := by
  have h_left :
      Function.LeftInverse (asLinearMap (ρ := ρ) (σ := σ))
        (ofLinearMap (ρ := ρ) (σ := σ)) := by
    intro f
    exact to_linear_map_as_linear_map (ρ := ρ) (σ := σ) f
  have h_right :
      Function.RightInverse (asLinearMap (ρ := ρ) (σ := σ))
        (ofLinearMap (ρ := ρ) (σ := σ)) := by
    intro f
    exact as_linear_map_to_linear_map (ρ := ρ) (σ := σ) f
  exact ⟨h_left.injective, h_right.surjective⟩

variable {ρ σ} in
@[simp]
theorem asLinearMap_zero_iff (f : IntertwiningMap ρ σ) : asLinearMap f = 0 ↔ f = 0 := by
  constructor <;> intro hf <;> ext v <;> simp only [intertwiningMap_toLinearMap,
    toLinearMap_zero_eq_zero, LinearMap.zero_apply]
  · change (asLinearMap f) v = 0
    rw [hf]
    rfl
  · rw [hf]
    rfl

variable {ρ σ} in
@[simp]
theorem ofLinearMap_zero_iff (f : ρ.asModule →ₗ[A[G]] σ.asModule) : ofLinearMap f = 0 ↔ f = 0 := by
  constructor <;> intro hf <;> ext v <;> simp only [intertwiningMap_toLinearMap,
    toLinearMap_zero_eq_zero, LinearMap.zero_apply]
  · change (ofLinearMap f) v = 0
    rw [hf]
    rfl
  · rw [hf]
    rfl

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
