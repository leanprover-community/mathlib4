/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov, Edison Xie
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

section non_comm
section Monoid

variable {A G V W U : Type*} [Semiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

/-- An unbundled version of `IntertwiningMap`. -/
@[mk_iff] structure IsIntertwiningMap : Prop where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/-- An intertwining map between two representations `ρ` and `σ` of the same monoid `G` is a map
  between underlying modules which commutes with the `G`-actions. -/
structure IntertwiningMap extends V →ₗ[A] W where
  /-- An underlying `A`-linear map of the underlying `A`-modules. -/
  isIntertwining' (g : G) : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap

lemma IntertwiningMap.isIntertwining_assoc {f : IntertwiningMap ρ σ} (g : G) (l : U →ₗ[A] V) :
    f.toLinearMap ∘ₗ ρ g ∘ₗ l = σ g ∘ₗ f.toLinearMap ∘ₗ l := by
  rw [← LinearMap.comp_assoc, f.2, LinearMap.comp_assoc]

namespace IntertwiningMap

@[ext]
lemma ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g
  simpa using h

lemma toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap :=
  fun {_ _} ↦ ext _ _

lemma toFun_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap.toFun := by
  intro f g h
  ext x
  exact congrFun h x

instance : FunLike (IntertwiningMap ρ σ) V W where
  coe f := f.toFun
  coe_injective' := toFun_injective ρ σ

instance : LinearMapClass (IntertwiningMap ρ σ) A V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

@[simp] theorem coe_mk (f : V →ₗ[A] W) (h) : ⇑(⟨f, h⟩ : IntertwiningMap ρ σ) = f := rfl

lemma isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) := congr($(f.isIntertwining' g) v)

@[simp] theorem toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v := rfl

instance : Zero (IntertwiningMap ρ σ) := ⟨⟨0, by simp⟩⟩

@[simp] lemma coe_zero : ((0 : IntertwiningMap ρ σ) : V → W) = 0 := rfl

@[simp] lemma zero_toLinearMap : (0 : IntertwiningMap ρ σ).toLinearMap = 0 := rfl

instance : Add (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ ⟨f.toLinearMap + g.toLinearMap, by
    simp [LinearMap.add_comp, LinearMap.comp_add, f.2, g.2,]⟩⟩

@[simp] lemma coe_add (f g : IntertwiningMap ρ σ) :
    ((f + g : IntertwiningMap ρ σ) : V → W) = f + g := rfl

@[simp]
lemma add_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

instance : SMul ℕ (IntertwiningMap ρ σ) :=
  ⟨fun n f ↦ ⟨n • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

@[simp] lemma coe_nsmul (f : IntertwiningMap ρ σ) (n : ℕ) :
    ((n • f : IntertwiningMap ρ σ) : V → W) = n • f := rfl

instance instAddCommMonoid : AddCommMonoid (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommMonoid _ (coe_zero ρ σ) (coe_add ρ σ) (by intro f n; rw [coe_nsmul])

section group

variable {V W P : Type*} [AddCommMonoid V] [AddCommGroup W]
  [AddCommGroup P] [Module A V] [Module A W] [Module A P] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G P) (f : V →ₗ[A] W)

instance : Neg (IntertwiningMap ρ σ) :=
  ⟨fun f ↦ ⟨-f.toLinearMap, by simp [LinearMap.neg_comp, f.2]⟩⟩

@[simp]
lemma coe_neg (f : IntertwiningMap ρ σ) : ((-f : IntertwiningMap ρ σ) : V → W) = -f := rfl

instance : Sub (IntertwiningMap ρ σ) :=
  ⟨fun f g ↦ ⟨f.toLinearMap - g.toLinearMap, by
    simp [LinearMap.sub_comp, LinearMap.comp_sub, f.2, g.2]⟩⟩

@[simp] lemma coe_sub (f g : IntertwiningMap ρ σ) :
    ((f - g : IntertwiningMap ρ σ) : V → W) = f - g := rfl

@[simp]
lemma sub_toLinearMap (f g : IntertwiningMap ρ σ) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl

instance : SMul ℤ (IntertwiningMap ρ σ) :=
  ⟨fun z f ↦ ⟨z • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

@[simp] lemma coe_zsmul (f : IntertwiningMap ρ σ) (z : ℤ) :
    ((z • f : IntertwiningMap ρ σ) : V → W) = z • f := rfl

instance : AddCommGroup (IntertwiningMap ρ σ) :=
  fast_instance%
  DFunLike.coe_injective.addCommGroup _ (coe_zero ρ σ) (coe_add ρ σ) (coe_neg ρ σ) (coe_sub ρ σ)
    (coe_nsmul ρ σ) (coe_zsmul ρ σ)

end group

/-- A coercion from intertwining maps to additive monoid homomorphisms. -/
def coeFnAddMonoidHom : IntertwiningMap ρ σ →+ V → W where
  toFun := (⇑)
  map_zero' := coe_zero ρ σ
  map_add' := coe_add ρ σ

/-- The identity map, considered as an intertwining map from a representation to itself. -/
def id : IntertwiningMap ρ ρ where
  toLinearMap := LinearMap.id
  isIntertwining' := by simp

variable {ρ σ τ} in
/-- Composition of intertwining maps.

A convenience variant of `IntertwiningMap.llcomp` for use in dot notation. -/
def comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap ρ τ where
  __ := f.toLinearMap ∘ₗ g.toLinearMap
  isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]

@[simp]
lemma comp_toLinearMap (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (comp f g).toLinearMap = f.toLinearMap.comp g.toLinearMap := rfl

@[simp]
lemma comp_apply (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V) :
    comp f g v = f (g v) := rfl

lemma comp_add (f₁ f₂ : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f₁ + f₂).comp g = comp f₁ g + comp f₂ g := by ext1; simp [LinearMap.add_comp]

lemma add_comp (f : IntertwiningMap σ τ) (g₁ g₂ : IntertwiningMap ρ σ) :
    comp f (g₁ + g₂) = comp f g₁ + comp f g₂ := by ext1; simp [LinearMap.comp_add]

end IntertwiningMap

end Monoid

end non_comm

variable {A G V W U : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

section Monoid

namespace IntertwiningMap

instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f ↦ ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V → W) = a • f := rfl

lemma smul_toLinearMap (a : A) (f : IntertwiningMap ρ σ) :
    (a • f).toLinearMap = a • f.toLinearMap := rfl

instance : Module A (IntertwiningMap ρ σ) :=
  fast_instance%
  Function.Injective.module A (coeFnAddMonoidHom ρ σ) DFunLike.coe_injective (coe_smul ρ σ)

set_option backward.isDefEq.respectTransparency false in
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
          | single g a => simp [f.isIntertwining]; rfl }
  invFun f :=
    { toLinearMap := { f with
        map_smul' a v := by simp }
      isIntertwining' g := by ext v; simpa using f.map_smul' (MonoidAlgebra.single g 1) v }
  map_add' g₁ g₂ := by ext; simp
  map_smul' t g := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

/-- Composition of intertwining maps. -/
def llcomp : IntertwiningMap σ τ →ₗ[A] IntertwiningMap ρ σ →ₗ[A] IntertwiningMap ρ τ where
  toFun f :=
    { toFun g :=
      { toLinearMap := f.toLinearMap.comp g.toLinearMap
        isIntertwining' := by simp [LinearMap.comp_assoc, g.2, f.isIntertwining_assoc]}
      map_add' _ _ := by ext; simp [map_add]
      map_smul' _ _ := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

lemma comp_def (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f g = llcomp _ _ _ f g := rfl

lemma smul_comp (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (a • f).comp g = a • comp f g := by simp [comp_def]

lemma comp_smul (a : A) (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    comp f (a • g) = a • comp f g := by simp [comp_def]

instance : Mul (IntertwiningMap ρ ρ) where
  mul := comp

@[simp] lemma coe_mul (f g : IntertwiningMap ρ ρ) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl

@[simp] lemma mul_apply (f g : IntertwiningMap ρ ρ) (v : V) : (f * g) v = f (g v) := rfl

instance : One (IntertwiningMap ρ ρ) := ⟨id ρ⟩

@[simp] lemma coe_one : ((1 : IntertwiningMap ρ ρ) : V → V) = (_root_.id : V → V) := rfl

instance : Semigroup (IntertwiningMap ρ ρ) :=
  Function.Injective.semigroup (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) (coe_mul ρ)

instance : Pow (IntertwiningMap ρ ρ) ℕ := ⟨fun f n => npowRecAuto n f⟩

instance : Monoid (IntertwiningMap ρ ρ) :=
  Function.Injective.monoid (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl (fun _ _ => rfl)
    (fun f n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ, coe_mul, show f ^ (n + 1) = f ^ n * f from rfl, ih])

instance : NatCast (IntertwiningMap ρ ρ) where
  natCast n := n • (1 : IntertwiningMap ρ ρ)

instance instSemiring : Semiring (IntertwiningMap ρ ρ) :=
  fast_instance%
  Function.Injective.semiring (fun f : IntertwiningMap ρ ρ => f.toLinearMap)
    (toLinearMap_injective ρ ρ) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih => simp [ih, pow_succ])
    (fun _ => rfl)

instance : Algebra A (IntertwiningMap ρ ρ) :=
  Algebra.ofModule (fun a f g => rfl) (fun a f g => by ext; simp)

@[simp] lemma algebraMap_apply (a : A) : algebraMap A (IntertwiningMap ρ ρ) a = a • 1 := rfl

/-- Intertwining maps from `ρ` to itself are the same as `A[G]`-linear endomorphisms. -/
noncomputable def equivAlgEnd :
    IntertwiningMap ρ ρ ≃ₐ[A] Module.End A[G] ρ.asModule :=
  AlgEquiv.ofLinearEquiv
    (equivLinearMapAsModule ρ ρ)
    (by rfl)
    (by intro f g; rfl)

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
  isIntertwining' x := LinearMap.ext <| (isIntertwiningMap_of_mem_center ρ g hg).isIntertwining x

end IntertwiningMap


/-- Equivalence between representations is a bijective intertwining map. -/
@[ext]
structure Equiv extends IntertwiningMap ρ σ, V ≃ₗ[A] W

/-- Underlying linear isomorphism of an equivalence of representations. -/
add_decl_doc Equiv.toLinearEquiv

/-- The intertwining map underlying an equivalence of representations. -/
add_decl_doc Equiv.toIntertwiningMap

namespace Equiv

variable {ρ σ} (φ : Equiv ρ σ)

instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toFun
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ := Equiv.ext

@[simp] lemma coe_toIntertwiningMap : ⇑φ.toIntertwiningMap = ⇑φ := rfl

@[simp] lemma coe_toLinearMap : ⇑φ.toLinearMap = ⇑φ := rfl

@[simp] lemma coe_invFun : φ.invFun = EquivLike.inv φ := rfl

@[simp]
theorem toLinearEquiv_toLinearMap :
  LinearEquiv.toLinearMap φ.toLinearEquiv = φ.toIntertwiningMap.toLinearMap := rfl

@[simp]
theorem toLinearEquiv_apply (v : V) :
  φ.toLinearEquiv v = φ.toIntertwiningMap v := rfl

theorem conj_apply_self (g : G) : φ.conj (ρ g) = σ g := by ext; simp [φ.isIntertwining]

end Equiv

end Monoid

namespace Equiv

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)

/-- dualTensorHom as an equivalence of representations. -/
@[simps!] noncomputable def dualTensorHom : Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  toLinearEquiv := dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

end Group

end Equiv

end Representation
