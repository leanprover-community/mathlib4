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

/-- An intertwining map constructed form the linear map and the fact that it is intertwining. -/
def _root_.LinearMap.intertwiningMap_of_isIntertwiningMap
    (hf : ∀ (g : G), ∀ (v : V), f (ρ g v) = σ g (f v)) : IntertwiningMap ρ σ :=
  { f with isIntertwining' g := by ext v; exact hf g v}

lemma IntertwiningMap.isIntertwining_assoc {f : IntertwiningMap ρ σ} (g : G) (l : U →ₗ[A] V) :
    f.toLinearMap ∘ₗ ρ g ∘ₗ l = σ g ∘ₗ f.toLinearMap ∘ₗ l := by
  rw [← LinearMap.comp_assoc, f.2, LinearMap.comp_assoc]

namespace IntertwiningMap

variable {ρ σ} in
@[ext]
lemma ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g
  simpa using h

lemma toLinearMap_injective : Function.Injective fun f : IntertwiningMap ρ σ ↦ f.toLinearMap :=
  fun _ _ ↦ ext

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

lemma toLinearMap_mk (f : V →ₗ[A] W) (h) :
  (⟨f, h⟩ : IntertwiningMap ρ σ).toLinearMap = f := rfl

lemma isIntertwining (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) := congr($(f.isIntertwining' g) v)

lemma toLinearMap_apply (f : IntertwiningMap ρ σ) (v : V) : f.toLinearMap v = f v := rfl

@[simp] lemma coe_toLinearMap (f : IntertwiningMap ρ σ) : (f.toLinearMap : _ → _) = f := rfl

@[simp] lemma _root_.LinearMap.toIntertwiningMap
  (hf : ∀ (g : G), ∀ (v : V), f (ρ g v) = σ g (f v)) (v : V) :
  f.intertwiningMap_of_isIntertwiningMap ρ σ hf v = f v := rfl

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

lemma toLinearMap_sum {ι : Type*} (s : Finset ι) (f : ι → IntertwiningMap ρ σ) :
    (∑ i ∈ s, f i : IntertwiningMap ρ σ).toLinearMap = ∑ i ∈ s, (f i).toLinearMap := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

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

@[simp]
lemma toLinearMap_id : (id ρ).toLinearMap = LinearMap.id := rfl

@[simp]
lemma id_apply (v : V) : id ρ v = v := rfl

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

/-- Equivalence between representations is a bijective intertwining map. -/
structure Equiv extends IntertwiningMap ρ σ, V ≃ₗ[A] W where
  mk' ::

attribute [coe] Equiv.toIntertwiningMap

/-- Underlying linear isomorphism of an equivalence of representations. -/
add_decl_doc Equiv.toLinearEquiv

/-- The intertwining map underlying an equivalence of representations. -/
add_decl_doc Equiv.toIntertwiningMap

namespace Equiv

variable {ρ σ} (φ : Equiv ρ σ)

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
def mk (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) : ρ.Equiv σ where
  __ := e
  isIntertwining' := he

lemma toLinearEquiv_mk' {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearEquiv = e := rfl

lemma toIntertwiningMap_mk' (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toIntertwiningMap = ⟨e.toLinearMap, he⟩ := rfl

@[simp]
lemma toLinearMap_mk' (e : V ≃ₗ[A] W) (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).toLinearMap = e.toLinearMap := rfl

lemma toLinearEquiv_injective : Function.Injective (toLinearEquiv : (σ.Equiv ρ) → _) :=
  fun φ ψ h ↦ by cases φ; cases ψ; simpa [IntertwiningMap.ext_iff] using h

lemma toLinearEquiv_inj (φ ψ : σ.Equiv ρ) : φ.toLinearEquiv = ψ.toLinearEquiv ↔ φ = ψ :=
  toLinearEquiv_injective.eq_iff

instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by
    cases φ; cases ψ
    simp_all [IntertwiningMap.ext_iff]

instance : LinearEquivClass (σ.Equiv ρ) A W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]
lemma mk_apply {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/-- Any representation is equivalent to itself. -/
def refl : Equiv ρ ρ where
  __ := LinearEquiv.refl _ _
  isIntertwining' g := by simp

@[simp] lemma toIntertwiningMap_refl : (refl ρ).toIntertwiningMap = .id ρ := rfl

@[simp] lemma toLinearMap_refl : (refl ρ).toLinearMap = LinearMap.id := rfl

@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

@[simp] lemma coe_toIntertwiningMap : ⇑φ.toIntertwiningMap = φ := rfl

@[simp] lemma coe_toLinearMap : ⇑φ.toLinearMap = φ := rfl

lemma coe_invFun : φ.invFun = φ.symm := rfl

theorem toLinearEquiv_toLinearMap :
  φ.toLinearEquiv.toLinearMap  = φ.toIntertwiningMap.toLinearMap := rfl

theorem toLinearEquiv_apply (v : V) : φ.toLinearEquiv v = φ.toIntertwiningMap v := rfl

open LinearMap in
/-- The equiv between representations are symmetric. -/
@[symm]
def symm (φ : Equiv ρ σ) : Equiv σ ρ where
  __ := φ.toLinearEquiv.symm
  isIntertwining' g := by
    rw [← cancel_left φ.toLinearEquiv.injective, ← comp_assoc, ← comp_assoc, φ.1.2 g, φ.comp_symm,
      comp_assoc, φ.comp_symm, id_comp, comp_id]

open LinearMap in
lemma _root_.LinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃ₗ[A] W}
    (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (g : G) :
    e.symm ∘ₗ (σ g) = (ρ g) ∘ₗ e.symm := by
  apply e.comp_toLinearMap_eq_iff _ _|>.1
  rw [← comp_assoc, ← comp_assoc, he g, e.comp_symm, id_comp, comp_assoc, e.comp_symm, comp_id]

@[simp]
lemma mk_symm {e : V ≃ₗ[A] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl

lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl

lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

variable {τ}

open LinearMap in
/-- Composition of two `Equiv`. -/
@[trans]
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ where
  __ := φ.toLinearEquiv.trans ψ.toLinearEquiv
  isIntertwining' g := by
    rw [LinearEquiv.coe_trans, comp_assoc, φ.1.2, ← comp_assoc, ψ.1.2, comp_assoc]

@[simp]
lemma toIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toIntertwiningMap = ψ.toIntertwiningMap.comp φ.toIntertwiningMap := rfl

@[simp]
lemma toLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toLinearMap = ψ.toLinearMap ∘ₗ φ.toLinearMap := rfl

@[simp]
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

end Monoid

end non_comm

variable {A G V W U : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid U] [Module A V] [Module A W] [Module A U] (ρ : Representation A G V)
  (σ : Representation A G W) (τ : Representation A G U) (f : V →ₗ[A] W)

variable {ρ σ} in
theorem Equiv.conj_apply_self (g : G) (φ : Equiv ρ σ) : φ.conj (ρ g) = σ g := by
  ext w
  have := (congr($(φ.symm.toIntertwiningMap.2 g) w)).symm
  simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply, LinearEquiv.conj_apply_apply,
    coe_symm, toLinearEquiv_apply, coe_toIntertwiningMap] at this ⊢
  simp [this]

section Monoid

namespace IntertwiningMap

instance : SMul A (IntertwiningMap ρ σ) :=
  ⟨fun a f ↦ ⟨a • f.toLinearMap, by simp [LinearMap.smul_comp, LinearMap.comp_smul, f.2]⟩⟩

@[simp] lemma coe_smul (a : A) (f : IntertwiningMap ρ σ) :
    ((a • f : IntertwiningMap ρ σ) : V → W) = a • f := rfl

@[simp]
lemma toLinearMap_smul (a : A) (f : IntertwiningMap ρ σ) :
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
    { toFun g := ((f.toLinearMap.comp g.toLinearMap).intertwiningMap_of_isIntertwiningMap ρ τ
      (by intro γ v; simp [f.isIntertwining, g.isIntertwining]))
      map_add' _ _ := by ext; simp [map_add, toLinearMap_apply]
      map_smul' _ _ := by ext; simp [toLinearMap_apply] }
  map_add' _ _ := by ext; simp [toLinearMap_apply]
  map_smul' _ _ := by ext; simp [toLinearMap_apply]

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

/-- `IntertwiningMap.toLinearMap` as a linear map. -/
@[simps] def toLinearMapl : IntertwiningMap ρ σ →ₗ[A] V →ₗ[A] W where
  toFun := toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module A V] [Module A W] (ρ : Representation A G V) (σ : Representation A G W) in
instance [Module.Finite A V] [IsNoetherian A W] :
    Module.Finite A (IntertwiningMap ρ σ) :=
  .of_injective (toLinearMapl (ρ := ρ) (σ := σ)) (toLinearMap_injective ρ σ)

variable {ρ σ} in
/-- A bijective intertwining map is an equivalence of representations. -/
noncomputable
def ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    Equiv ρ σ where
  isIntertwining' := f.isIntertwining'
  toLinearEquiv :=  LinearEquiv.ofBijective f.toLinearMap hf

@[simp]
theorem coe_ofBijective (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) :
    ⇑(f.ofBijective hf) = ⇑f := rfl

variable {P : Type*} [AddCommMonoid P] [Module A P] {π : Representation A G P}

variable {ρ σ τ}

/-- The tensor product of intertwining maps induced from tensor product of linear maps. -/
def tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (tprod ρ τ).IntertwiningMap (tprod σ π) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    rw [tprod_apply, ← TensorProduct.map_comp, f.2, g.2, TensorProduct.map_comp, tprod_apply]

@[simp]
lemma toLinearMap_tensor (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f.tensor g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

@[simp]
lemma tensor_add_left (f₁ f₂ : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (f₁ + f₂).tensor g = f₁.tensor g + f₂.tensor g := by ext; simp [TensorProduct.add_tmul]

@[simp]
lemma tensor_add_right (f : IntertwiningMap ρ σ) (g₁ g₂ : IntertwiningMap τ π) :
    f.tensor (g₁ + g₂) = f.tensor g₁ + f.tensor g₂ := by ext; simp [TensorProduct.tmul_add]

@[simp]
lemma tensor_smul_left (a : A) (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) :
    (a • f).tensor g = a • (f.tensor g) := by ext; simp [TensorProduct.smul_tmul]

@[simp]
lemma tensor_smul_right (f : IntertwiningMap ρ σ) (a : A) (g : IntertwiningMap τ π) :
    f.tensor (a • g) = a • (f.tensor g) := by ext; simp [TensorProduct.tmul_smul]

@[simp]
lemma tensor_apply (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ π) (v : V) (w : U) :
    f.tensor g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

variable (ρ) in
/-- The intertwining map induced from `f : σ → τ` to `ρ.tprod σ → ρ.tprod τ`. -/
def lTensor (f : IntertwiningMap σ τ) :
    (tprod ρ σ).IntertwiningMap (tprod ρ τ) := tensor (id ρ) f

@[simp]
lemma toLinearMap_lTensor (f : IntertwiningMap ρ σ) :
    (f.lTensor τ).toLinearMap = f.toLinearMap.lTensor U := rfl

@[simp]
lemma lTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.lTensor ρ (v ⊗ₜ w) = v ⊗ₜ f w := rfl

@[simp]
lemma lTensor_id : lTensor ρ (id σ) = id (tprod ρ σ) := by ext; simp

@[simp]
lemma lTensor_zero : lTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
lemma lTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    lTensor ρ (f₁ + f₂) = lTensor ρ f₁ + lTensor ρ f₂ := tensor_add_right _ _ _

@[simp]
lemma lTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    lTensor ρ (a • f) = a • lTensor ρ f := tensor_smul_right _ _ _

variable (ρ) in
/-- The natural intertwining map `σ.tprod ρ → τ.tprod ρ` induced by `f : σ → τ`. -/
def rTensor (f : IntertwiningMap σ τ) :
    (tprod σ ρ).IntertwiningMap (tprod τ ρ) := tensor f (id ρ)

@[simp]
lemma toLinearMap_rTensor (f : IntertwiningMap σ τ) :
    (f.rTensor ρ).toLinearMap = f.toLinearMap.rTensor V := rfl

@[simp]
lemma rTensor_apply (f : IntertwiningMap σ τ) (v : V) (w : W) :
    f.rTensor ρ (w ⊗ₜ v) = f w ⊗ₜ v := rfl

@[simp]
lemma rTensor_id : rTensor ρ (id σ) = id (tprod σ ρ) := by ext; simp

@[simp]
lemma rTensor_zero : rTensor ρ (0 : IntertwiningMap σ τ) = 0 := by ext; simp

@[simp]
lemma rTensor_add (f₁ f₂ : IntertwiningMap σ τ) :
    rTensor ρ (f₁ + f₂) = rTensor ρ f₁ + rTensor ρ f₂ := tensor_add_left _ _ _

@[simp]
lemma rTensor_smul (a : A) (f : IntertwiningMap σ τ) :
    rTensor ρ (a • f) = a • rTensor ρ f := tensor_smul_left _ _ _

lemma rTensor_comp_lTensor (f : IntertwiningMap σ ρ) (g : IntertwiningMap ρ τ) :
    (f.rTensor τ).comp (g.lTensor σ) = f.tensor g := by ext; simp

lemma lTensor_comp_rTensor (f : IntertwiningMap σ ρ) (g : IntertwiningMap ρ τ) :
    (f.lTensor τ).comp (g.rTensor σ) = g.tensor f := by ext; simp

end IntertwiningMap

namespace TensorProduct

noncomputable section

/-- Equivalence between representations induced from `TensorProduct.comm`. -/
def comm : (tprod ρ σ).Equiv (tprod σ ρ) :=
  .mk (_root_.TensorProduct.comm A V W) <| fun g ↦ by ext; simp

@[simp]
lemma toLinearMap_comm : (comm ρ σ).toLinearMap = _root_.TensorProduct.comm A V W := rfl

@[simp]
lemma comm_apply (v : V) (w : W) : comm ρ σ (v ⊗ₜ w) = w ⊗ₜ v := rfl

lemma comm_comp_lTensor (f : IntertwiningMap σ τ) :
    (comm ρ τ).comp (f.lTensor ρ) = (f.rTensor ρ).comp (comm ρ σ).toIntertwiningMap := by ext; simp

lemma comm_comp_rTensor (f : IntertwiningMap σ τ) :
    (comm τ ρ).comp (f.rTensor ρ) = (f.lTensor ρ).comp (comm σ ρ).toIntertwiningMap := by ext; simp

lemma comm_symm : (comm σ ρ).symm = comm ρ σ := by rfl

/-- The `Equiv` between representations induced from `TensorProduct.assoc`. -/
def assoc : (tprod (tprod ρ σ) τ).Equiv (tprod ρ (tprod σ τ)) :=
  .mk (_root_.TensorProduct.assoc A V W U) <| fun g ↦ by ext; simp

@[simp]
lemma toLinearMap_assoc : (assoc ρ σ τ).toLinearMap = _root_.TensorProduct.assoc A V W U := rfl

@[simp]
lemma assoc_symm_toLinearMap : (assoc ρ σ τ).symm.toLinearMap =
  (_root_.TensorProduct.assoc A V W U).symm := rfl

@[simp]
lemma assoc_apply (v : V) (w : W) (u : U) : assoc ρ σ τ ((v ⊗ₜ w) ⊗ₜ u) = v ⊗ₜ (w ⊗ₜ u) := rfl

variable (A) in
/-- The `Equiv` between representations induced from `TensorProduct.rid`. -/
def rid : (σ.tprod (trivial A G A)).Equiv σ :=
  .mk (_root_.TensorProduct.rid A W) <| fun g ↦ by ext; simp

@[simp]
lemma toLinearMap_rid : (rid A σ).toLinearMap = _root_.TensorProduct.rid A W := rfl

@[simp]
lemma rid_apply (w : W) (a : A) : rid A σ (w ⊗ₜ a) = a • w := rfl

@[simp]
lemma rid_symm_apply (w : W) : (rid A σ).symm w = w ⊗ₜ 1 := rfl

variable (A) in
/-- The `Equiv` between representations induced from `TensorProduct.lid`. -/
def lid : ((trivial A G A).tprod σ).Equiv σ :=
  .mk (_root_.TensorProduct.lid A W) <| fun g ↦ by ext; simp

@[simp]
lemma toLinearMap_lid : (lid A σ).toLinearMap = _root_.TensorProduct.lid A W := rfl

@[simp]
lemma lid_apply (a : A) (w : W) : lid A σ (a ⊗ₜ w) = a • w := rfl

@[simp]
lemma lid_symm_apply (w : W) : (lid A σ).symm w = 1 ⊗ₜ w := rfl

end

end TensorProduct

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
