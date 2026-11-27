/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Topology.ContinuousMap.Algebra

import Mathlib.CategoryTheory.Category.Init

/-!
# Continuous representations

This file defines continuous representations of a monoid `G` on a `R`-module `V` and
related basic results.

## Main Results

* `ContRepresentation R G V` is the type of continuous representations of a monoid `G` on a
  `R`-module `V` which is a topological additive group. The monoid `G` is not assumed to have a
  topology, but for each element of `G`, the action on `V` is a continuous linear map.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind φ π`. If `H` is a topological group, `G` is a group with a topology,
  `φ : G →ₜ* H` is a continuous homomorphism and `π` is a continuous representation of `G` on
  `V`, then `π.coind φ` is the coinduced continuous representation of `H` on the submodule of
  `C(H, V)` of functions `f` satisfying `f (φ g * h) = π g (f h)` for all `g : G` and `h : H`.

* `ContRepresentation.coind₁ π`. If `π` is a continuous representation of a topological group `G` on
  `V` then `π.coind₁` is the continuous representation of `G` on `C(G, V)` in which `g : G` acts by
  `f ↦ (x ↦ π g (f (g⁻¹ * x)))`. The functor `coind₁` is used to construct a resolution of `π` of
  the form `0 → π → π.coind₁ → π.coind₁.coind₁ → π.coind₁.coind₁.coind₁ → ...`, which is used in
  the definition of `continuousCohomology`.

* `ContRepresentation.coindEquivCoind₁`. In the case that the action `G × V → V` is continuous,
  `π.coind₁` is isomorphic to the coinduction along `1 : Unit →ₜ* G` of the trivial representation
  of the trivial group on `V`.

* `ContIntertwiningMap.mapInvariantsOfRes φ f` is the continuous linear map
  `π.invariants →L[R] π'.invariants` induced by a monoid homomorphism `φ : H →* G` and a
  continuous intertwining map `f : π.restrict φ →ⁱL π'`.

* `ContRepresentation.coind₁ResMap φ f` is the continuous intertwining map
  `π.coind₁.restrict φ →ⁱL π'.coind₁` induced by a continuous group homomorphism `φ : H →ₜ* G`
  and a continuous intertwining map `f : π.restrict φ →ⁱL π'`, given by `F ↦ f ∘ F ∘ φ`.

## Tags

continuous representation, algebra
-/

@[expose] public section

variable (R G V W U : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U]

/-- A continuous representation of a group `G` on a `R`-module `V` which is a topological addgroup
  is a homomorphism `G →* V →L[R] V`. -/
structure ContRepresentation where
  ofMonoidHom ::
  /-- The underlying monoid homomorphism of a continuous representation. -/
  toMonoidHom : G →* V →L[R] V

@[macro_inline]
instance : FunLike (ContRepresentation R G V) G (V →L[R] V) where
  coe π := π.toMonoidHom
  coe_injective π₁ π₂ _ := by cases π₁; cases π₂; simp_all

instance : MonoidHomClass (ContRepresentation R G V) G (V →L[R] V) where
  map_one π := π.toMonoidHom.map_one
  map_mul π := π.toMonoidHom.map_mul

lemma ContRepresentation.toMonoidHom_apply (π : ContRepresentation R G V) (g : G) :
    π.toMonoidHom g = π g := rfl

@[simp]
lemma ContRepresentation.apply_inv_apply {G : Type*} [Group G] (π : ContRepresentation R G V)
    (g : G) (v : V) : π g (π g⁻¹ v) = v := by
  rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

@[simp]
lemma ContRepresentation.inv_apply_apply {G : Type*} [Group G] (π : ContRepresentation R G V)
    (g : G) (v : V) : π g⁻¹ (π g v) = v := by
  rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

/-- Every continuous representation "is" a representation. -/
abbrev ContRepresentation.toRepresentation (π : ContRepresentation R G V) :
    Representation R G V :=
  .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π.toMonoidHom

variable {R G V W U}

/-- A continuous intertwining map between two continuous representations is an intertwining map
  which is also continuous. -/
structure ContIntertwiningMap (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
    extends V →L[R] W where
  isIntertwining' (g : G) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap

/-- notation for continuous intertwining maps -/
scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContIntertwiningMap

open ContRepresentation

variable {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  {π₃ : ContRepresentation R G U}

/-- Any continuous intertwining map is an intertwining map. -/
abbrev toIntertwiningMap (f : π₁ →ⁱL π₂) :
    Representation.IntertwiningMap π₁.toRepresentation π₂.toRepresentation where
  __ := f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.isIntertwining' g))

/-- The identity continuous intertwining map. -/
def id : π₁ →ⁱL π₁ where
  __ := ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[simp]
lemma toContinuousLinearMap_id :
    (id : π₁ →ⁱL π₁).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[ext]
lemma ext {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {f g : π₁ →ⁱL π₂} (h : f.toContinuousLinearMap = g.toContinuousLinearMap) : f = g := by
  cases f; cases g; congr

lemma toContinuousLinearMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toContinuousLinearMap :=
  fun _ _ ↦ ext

lemma toIntertwiningMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toIntertwiningMap :=
  fun _ _ _ ↦ by ext; simp_all

lemma toFun_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toFun := fun f g h ↦ by
  ext x; congrm $h x

@[macro_inline]
instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    FunLike (π₁ →ⁱL π₂) V W where
  coe f := f.toFun
  coe_injective := toFun_injective

lemma id_apply (v : V) : (.id : π₁ →ⁱL π₁) v = v := rfl

lemma toContinuousLinearMap_apply (f : π₁ →ⁱL π₂) (v : V) :
  f.toContinuousLinearMap v = f v := rfl

lemma isIntertwining {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v) :=
  f.toIntertwiningMap.isIntertwining _ _ g v

instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    ContinuousLinearMapClass (π₁ →ⁱL π₂) R V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont

open ContinuousLinearMap in
/-- The composition of two continuous intertwining maps is a continuous intertwining map. -/
def comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : π₁ →ⁱL π₃ where
  __ := f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by
    rw [comp_assoc, g.isIntertwining', ← comp_assoc, f.isIntertwining', comp_assoc]

@[simp]
lemma toContinuousLinearMap_comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) :
    (f.comp g).toContinuousLinearMap = f.toContinuousLinearMap.comp g.toContinuousLinearMap := rfl

@[simp]
lemma comp_id (f : π₁ →ⁱL π₂) : f.comp .id = f := rfl

@[simp]
lemma id_comp (f : π₁ →ⁱL π₂) : ContIntertwiningMap.id.comp f = f := rfl

instance : Add (π₁ →ⁱL π₂) where
  add f g := ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, by
    simp [g.isIntertwining', f.isIntertwining']⟩

@[simp]
lemma toContinuousLinearMap_add (f g : π₁ →ⁱL π₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := rfl

lemma add_apply (f g : π₁ →ⁱL π₂) (v : V) : (f + g) v = f v + g v := rfl

lemma comp_add (f : π₂ →ⁱL π₃) (g h : π₁ →ⁱL π₂) :
    f.comp (g + h) = f.comp g + f.comp h := by ext; simp

lemma add_comp (f g : π₂ →ⁱL π₃) (h : π₁ →ⁱL π₂) :
    (f + g).comp h = f.comp h + g.comp h := by ext; simp

instance : One (π₁ →ⁱL π₁) where one := .id

lemma one_def : (1 : π₁ →ⁱL π₁) = .id := rfl

@[simp]
lemma toContinuousLinearMap_one : (1 : π₁ →ⁱL π₁).toContinuousLinearMap = 1 := rfl

lemma one_apply (v : V) : (1 : π₁ →ⁱL π₁) v = v := rfl

instance : Zero (π₁ →ⁱL π₂) where zero := ⟨0, by simp⟩

@[simp]
lemma toContinuousLinearMap_zero : (0 : π₁ →ⁱL π₂).toContinuousLinearMap = 0 := rfl

lemma zero_apply (v : V) : (0 : π₁ →ⁱL π₂) v = 0 := rfl

instance : AddZeroClass (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addZeroClass _
    toContinuousLinearMap_zero toContinuousLinearMap_add

section SMul

variable {S : Type*} [DistribSMul S W] [SMulCommClass R S W]
  [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R]

instance instSMul :
    SMul S (π₁ →ⁱL π₂) where
  smul s f := ⟨s • f.toContinuousLinearMap, fun g ↦ by
    rw [ContinuousLinearMap.smul_comp, f.isIntertwining', ContinuousLinearMap.comp_smul]⟩

@[simp]
lemma toContinuousLinearMap_smul (s : S) (f : π₁ →ⁱL π₂) :
    (s • f).toContinuousLinearMap = s • f.toContinuousLinearMap := rfl

lemma smul_apply (s : S) (f : π₁ →ⁱL π₂) (v : V) : (s • f) v = s • f v := rfl

end SMul

instance : AddCommSemigroup (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommSemigroup _
    toContinuousLinearMap_add

instance : Neg (π₁ →ⁱL π₂) where
  neg f := ⟨-f.toContinuousLinearMap, by simp [f.isIntertwining']⟩

@[simp]
lemma toContinuousLinearMap_neg (f : π₁ →ⁱL π₂) :
    (-f).toContinuousLinearMap = -f.toContinuousLinearMap := rfl

lemma neg_apply (f : π₁ →ⁱL π₂) (v : V) : (-f) v = -f v := rfl

instance : Sub (π₁ →ⁱL π₂) where
  sub f g := ⟨f.toContinuousLinearMap - g.toContinuousLinearMap, by
    simp [g.isIntertwining', f.isIntertwining']⟩

@[simp]
lemma toContinuousLinearMap_sub (f g : π₁ →ⁱL π₂) :
    (f - g).toContinuousLinearMap = f.toContinuousLinearMap - g.toContinuousLinearMap := rfl

lemma sub_apply (f g : π₁ →ⁱL π₂) (v : V) : (f - g) v = f v - g v := rfl

lemma sub_comp (f g : π₂ →ⁱL π₃) (h : π₁ →ⁱL π₂) :
    (f - g).comp h = f.comp h - g.comp h := by
  ext; simp

lemma comp_sub (f : π₂ →ⁱL π₃) (g h : π₁ →ⁱL π₂) :
    f.comp (g - h) = f.comp g - f.comp h := by
  ext; simp


section addcommgroup

variable {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
  [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R]

lemma smul_comp {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    (s : S) (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : (s • f).comp g = s • (f.comp g) := by
  ext; simp

lemma comp_smul {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W]
    [LinearMap.CompatibleSMul W W S R] [LinearMap.CompatibleSMul W U S R]
    (s : S) (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : f.comp (s • g) = s • (f.comp g) := by
  ext; simp

instance : AddCommGroup (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ ↦ toContinuousLinearMap_smul _ _) (fun _ _ ↦ toContinuousLinearMap_smul _ _)

instance : DistribMulAction S (π₁ →ⁱL π₂) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [smul_add]

instance instModule {S : Type*} [Ring S] [Module S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] :
    Module S (π₁ →ⁱL π₂) where
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

end addcommgroup

end ContIntertwiningMap

namespace ContRepresentation

/-- The equivalence between continuous representations. -/
structure Equiv (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) extends
    V ≃L[R] W, ContIntertwiningMap π₁ π₂  where mk'' ::

attribute [coe] Equiv.toContIntertwiningMap

/-- Underlying continuous linear isomorphism of an equivalence of continuous representations. -/
add_decl_doc Equiv.toContinuousLinearEquiv

/-- The continuous intertwining map underlying an equivalence of continuous representations. -/
add_decl_doc Equiv.toContIntertwiningMap

namespace Equiv

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W}
  {τ : ContRepresentation R G U} (φ : Equiv ρ σ)

lemma isIntertwining (g : G) :
    φ.toContinuousLinearEquiv.toContinuousLinearMap ∘L (ρ g) =
      (σ g) ∘L φ.toContinuousLinearEquiv.toContinuousLinearMap :=
  φ.isIntertwining' g

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
def mk (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ where
  __ := e
  cont := e.continuous
  isIntertwining' := he

lemma toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearEquiv = e := rfl

lemma toContIntertwiningMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContIntertwiningMap = ⟨e.toContinuousLinearMap, he⟩ := rfl

@[simp]
lemma toContinuousLinearMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearMap = e.toContinuousLinearMap := rfl

lemma toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : (σ.Equiv ρ) → _) :=
  fun φ ψ h ↦ by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h

lemma toContinuousLinearEquiv_inj (φ ψ : σ.Equiv ρ) :
    φ.toContinuousLinearEquiv = ψ.toContinuousLinearEquiv ↔ φ = ψ :=
  toContinuousLinearEquiv_injective.eq_iff

@[macro_inline]
instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all

instance : ContinuousLinearEquivClass (σ.Equiv ρ) R W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]
lemma mk_apply {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/-- Any continuous representation is equivalent to itself. -/
def refl : Equiv ρ ρ := mk (ContinuousLinearEquiv.refl R V) (by simp)

@[simp] lemma toContIntertwiningMap_refl : (refl ρ).toContIntertwiningMap = .id := rfl

@[simp] lemma toContinuousLinearMap_refl :
    (refl ρ).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

@[simp] lemma coe_toContIntertwiningMap : ⇑φ.toContIntertwiningMap = φ := rfl

lemma coe_toContinuousLinearMap : ⇑φ.toContinuousLinearMap = φ := rfl

lemma coe_invFun : φ.invFun = φ.symm := rfl

theorem toContinuousLinearEquiv_toContinuousLinearMap :
    φ.toContinuousLinearEquiv.toContinuousLinearMap =
      φ.toContIntertwiningMap.toContinuousLinearMap := rfl

theorem toContinuousLinearEquiv_apply (v : V) :
    φ.toContinuousLinearEquiv v = φ.toContIntertwiningMap v := rfl

open ContinuousLinearMap in
/-- The equiv between continuous representations are symmetric. -/
@[symm]
def symm : Equiv σ ρ := mk φ.toContinuousLinearEquiv.symm <| fun g ↦ by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective, ← comp_assoc, ← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

open ContinuousLinearMap

lemma _root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃L[R] W}
    (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (g : G) :
    e.symm ∘L (σ g) = (ρ g) ∘L e.symm :=
  (mk e he).symm.isIntertwining g

@[simp]
lemma mk_symm {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl

lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl

lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

/-- Composition of two `Equiv`s. -/
@[trans]
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ := mk
  (φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) <| fun g ↦ by
  rw [← ContinuousLinearEquiv.comp_coe, comp_assoc,
    φ.isIntertwining, ← comp_assoc, ψ.isIntertwining, comp_assoc]

@[simp]
lemma toContIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toContIntertwiningMap = ψ.toContIntertwiningMap.comp φ.toContIntertwiningMap := rfl

@[simp]
lemma toContinuousLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := rfl

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

variable (R G V) in
/-- The trivial continuous representation of a group `G` on a `R`-module `V`. -/
def trivial : ContRepresentation R G V := ofMonoidHom 1

@[simp]
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl

lemma apply_apply (π : ContRepresentation R G V) (g h : G) (v : V) :
    π g (π h v) = π (g * h) v := by simp

/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[implicit_reducible]
def restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G) :
    ContRepresentation R H V := ofMonoidHom (π.toMonoidHom.comp φ)

lemma restrict_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G)
    (h : H) : π.restrict φ h = π (φ h) := rfl

@[simp]
lemma restrict_apply_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G)
    (h : H) (v : V) : π.restrict φ h v = π (φ h) v := rfl

/-- The restriction of a continuous intertwining map along a monoid homomorphism. -/
def _root_.ContIntertwiningMap.restrict {H : Type*} [Monoid H] {π : ContRepresentation R G V}
    {π' : ContRepresentation R G W} (φ : H →* G) (f : π →ⁱL π') :
    π.restrict φ →ⁱL π'.restrict φ where
  __ := f.toContinuousLinearMap
  isIntertwining' h := by
    ext; simp [f.toContinuousLinearMap_apply, f.isIntertwining]

lemma _root_.ContIntertwiningMap.restrict_toContinuousLinearMap {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G) (f : π →ⁱL π') :
    (f.restrict φ).toContinuousLinearMap = f.toContinuousLinearMap := rfl

@[simp] lemma _root_.ContIntertwiningMap.restrict_apply {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G)
    (f : π →ⁱL π') (v : V) : f.restrict φ v = f v := rfl

lemma _root_.ContIntertwiningMap.restrict_sub {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G)
    (f g : π →ⁱL π') : (f - g).restrict φ = f.restrict φ - g.restrict φ := rfl

/--
For `ρ : ContRepresentation R G V` and a subgroup `N` of `G`,
`ρ.relInvariants N` is the `R`-submodule of `V` consisting of the `N`-invariant elements.
-/
def relInvariants (π : ContRepresentation R G V) (N : Submonoid G) : Submodule R V where
  carrier   := {v : V | ∀ n ∈ N, π n v = v}
  add_mem'  := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp] lemma mem_relInvariants {π : ContRepresentation R G V} {N : Submonoid G} (v : V) :
    v ∈ π.relInvariants N ↔ ∀ n ∈ N, π n v = v := Iff.rfl

/-- The submodule of `G`-invariant elements of a continuous representation. -/
def invariants (π : ContRepresentation R G V) : Submodule R V := π.relInvariants ⊤

@[simp]
lemma mem_invariants {π : ContRepresentation R G V} (v : V) :
    v ∈ π.invariants ↔ ∀ g, π g v = v := by simp [invariants]

/-- The map induced on `G`-invariant elements by a continuous intertwining map. -/
def _root_.ContIntertwiningMap.mapInvariants
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') : π.invariants →L[R] π'.invariants :=
  f.toContinuousLinearMap.restrict <| by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewrite, this lemma should be used when `mapInvariants` is
-- applied to `(homogeneousCochains X).X 0`
lemma _root_.ContIntertwiningMap.mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') (v : π.invariants) :
    f.mapInvariants v = f v := rfl

@[simp]
lemma _root_.ContIntertwiningMap.mk_mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') (v : V) (hv : v ∈ π.invariants) :
    f.mapInvariants ⟨v, hv⟩ = f v := rfl

variable {H : Type*} [Monoid H]

lemma invariants_le_invariants_restrict (π : ContRepresentation R G V) (φ : H →* G) :
    π.invariants ≤ (π.restrict φ).invariants :=
  fun _ hv h ↦ hv (φ h)

variable {π : ContRepresentation R G V} {π' : ContRepresentation R H W}

/-- Given a monoid homomorphism `φ : H →* G`, a `G`-representation `π` and an
`H`-representation `π'`, a continuous intertwining map `f : π.restrict φ →ⁱL π'` induces a
continuous linear map `π.invariants →L[R] π'.invariants` between the invariant submodules. -/
def _root_.ContIntertwiningMap.mapInvariantsOfRes (φ : H →* G)
    (f : π.restrict φ →ⁱL π') : π.invariants →L[R] π'.invariants :=
  f.toContinuousLinearMap.restrict <| by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewriting
lemma _root_.ContIntertwiningMap.mapInvariantsOfRes_apply (φ : H →* G)
    (f : π.restrict φ →ⁱL π') (v : π.invariants) :
    f.mapInvariantsOfRes φ v = f v := rfl

@[simp]
lemma _root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply (φ : H →* G)
    (f : π.restrict φ →ⁱL π') (v : V) (hv : v ∈ π.invariants) :
    f.mapInvariantsOfRes φ ⟨v, hv⟩ = f v := rfl

open scoped Pointwise in
class _root_.Submonoid.Normal (N : Submonoid G) : Prop where
  isNormal (g : G) : g • (N : Set G) = MulOpposite.op g • N

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
-- variable {G H : Type*} [Group G] [Group H] (N : Subgroup G) [hN : N.Normal]
--   (π : ContRepresentation R G V)
  -- [TopologicalSpace G] [TopologicalSpace R]
  -- [ContinuousSMul R V] [ContinuousSMul R W] [TopologicalSpace H]
  -- (φ : G →ₜ* H)

variable (N : Submonoid G) [N.Normal]

instance {G : Type*} [Group G] (N : Subgroup G) [N.Normal] : N.toSubmonoid.Normal where
  isNormal := (normal_iff_eq_cosets N).mp ‹_›

/-- The smallest congruence relation on `G` identifying every element of `N` with `1`. -/
def _root_.Submonoid.quotientCon (N : Submonoid G) : Con G := conGen fun x y ↦ x ∈ N ∧ y = 1

instance : HasQuotient G (Submonoid G) where
  Quotient N := N.quotientCon.Quotient

instance (N : Submonoid G) : Monoid (G ⧸ N) := inferInstanceAs (Monoid N.quotientCon.Quotient)

instance [TopologicalSpace G] (N : Submonoid G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuot

/-- Translations on `G ⧸ N` are continuous: a map out of `G ⧸ N` is continuous iff its composite
with the quotient map is. Joint continuity of multiplication would need the product of two quotient
maps to be a quotient map, which can fail when the quotient map is not open. -/
instance [TopologicalSpace G] [SeparatelyContinuousMul G] (N : Submonoid G) :
    SeparatelyContinuousMul (G ⧸ N) where
  continuous_const_mul {a} := by
    induction a using Con.induction_on with
    | H x => exact isQuotientMap_quot_mk.continuous_iff.2 <|
        continuous_quot_mk.comp (continuous_const_mul x)
  continuous_mul_const {a} := by
    induction a using Con.induction_on with
    | H x => exact isQuotientMap_quot_mk.continuous_iff.2 <|
        continuous_quot_mk.comp (continuous_mul_const x)

/-- The quotient map `G →* G ⧸ N`. -/
def _root_.Submonoid.mkQ (N : Submonoid G) : G →* G ⧸ N := N.quotientCon.mk'

/-- The quotient map `G →ₜ* G ⧸ N` as a continuous monoid homomorphism. -/
def _root_.QuotientTopMonoid.mk [TopologicalSpace G] (N : Submonoid G) : G →ₜ* G ⧸ N where
  toMonoidHom := N.mkQ
  continuous_toFun := continuous_quot_mk

@[simp]
lemma _root_.QuotientTopMonoid.coe_mk [TopologicalSpace G] (N : Submonoid G) :
    ↑(QuotientTopMonoid.mk N) = N.mkQ := rfl

/-- A monoid homomorphism that kills `N` factors through `G ⧸ N`. -/
def _root_.Submonoid.liftQ (N : Submonoid G) {M : Type*} [Monoid M] (f : G →* M)
    (hf : N ≤ MonoidHom.mker f) : G ⧸ N →* M :=
  N.quotientCon.lift f <| Con.conGen_le.2 fun x y ⟨hx, hy⟩ ↦ by
    simpa [Con.ker_rel, hy] using hf hx

open scoped Pointwise in
lemma _root_.Submonoid.Normal.exists_mul_eq_mul {n : G} (hn : n ∈ N) (g : G) :
    ∃ n' ∈ N, n * g = g * n' := by
  obtain ⟨n', hn', h : g * n' = n * g⟩ : n * g ∈ g • (N : Set G) := by
    rw [Submonoid.Normal.isNormal]
    exact ⟨n, hn, rfl⟩
  exact ⟨n', hn', h.symm⟩

/-- For a normal submonoid `N` of `G`, the equivalence relation on `G` given by `x ~ y` iff
`x * n₁ = y * n₂` for some `n₁ n₂ ∈ N`. It underlies the congruence `Submonoid.Normal.con N`. -/
def _root_.Submonoid.Normal.setoid : Setoid G where
  r x y := ∃ n₁ ∈ N, ∃ n₂ ∈ N, x * n₁ = y * n₂
  iseqv := {
    refl _ := ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨n₁, h₁, n₂, h₂, h⟩ ↦ ⟨n₂, h₂, n₁, h₁, h.symm⟩
    trans := fun ⟨n₁, h₁, n₂, h₂, h⟩ ⟨m₁, k₁, m₂, k₂, h'⟩ ↦ by
      obtain ⟨n₃, h₃, e⟩ := Submonoid.Normal.exists_mul_eq_mul N h₂ m₁
      exact ⟨n₁ * m₁, N.mul_mem h₁ k₁, m₂ * n₃, N.mul_mem k₂ h₃, by
        rw [← mul_assoc, h, mul_assoc, e, ← mul_assoc, h', mul_assoc]⟩ }

/-- The congruence relation of a normal submonoid `N` of `G`: `x ~ y` iff `x * n₁ = y * n₂` for
some `n₁ n₂ ∈ N`. It is the smallest congruence relation identifying every element of `N` with `1`
(`Submonoid.Normal.con_eq_conGen`), so its quotient is the quotient monoid of `G` by `N`. For a
normal subgroup it is `QuotientGroup.con` (`Submonoid.Normal.con_toSubmonoid`). -/
def _root_.Submonoid.Normal.con : Con G where
  toSetoid := Submonoid.Normal.setoid N
  mul' {_ y z _} := fun ⟨n₁, h₁, n₂, h₂, h⟩ ⟨m₁, k₁, m₂, k₂, h'⟩ ↦ by
    obtain ⟨n₁', h₁', e₁⟩ := Submonoid.Normal.exists_mul_eq_mul N h₁ z
    obtain ⟨n₂', h₂', e₂⟩ := Submonoid.Normal.exists_mul_eq_mul N h₂ z
    -- multiply the first relation on the right by `z`, the second on the left by `y`
    exact (Submonoid.Normal.setoid N).iseqv.trans (y := y * z)
      ⟨n₁', h₁', n₂', h₂', by rw [mul_assoc, ← e₁, ← mul_assoc, h, mul_assoc, e₂, mul_assoc]⟩
      ⟨m₁, k₁, m₂, k₂, by rw [mul_assoc, h', mul_assoc]⟩

lemma _root_.Submonoid.Normal.con_eq_conGen :
    Submonoid.Normal.con N = conGen fun x y ↦ x ∈ N ∧ y = 1 := by
  apply le_antisymm
  · rintro x y ⟨n₁, h₁, n₂, h₂, h⟩
    set c := conGen fun x y : G ↦ x ∈ N ∧ y = 1
    have hn (n : G) (hn : n ∈ N) : c n 1 := ConGen.Rel.of n 1 ⟨hn, rfl⟩
    have e₁ : c (x * n₁) x := by simpa using c.mul (c.refl x) (hn n₁ h₁)
    have e₂ : c (y * n₂) y := by simpa using c.mul (c.refl y) (hn n₂ h₂)
    exact c.trans (c.symm e₁) (h ▸ e₂)
  · exact Con.conGen_le.2 fun x y ⟨hx, hy⟩ ↦
      hy ▸ (⟨1, N.one_mem, x, hx, by simp⟩ : Submonoid.Normal.con N x 1)

lemma _root_.Submonoid.Normal.con_le_ker {M : Type*} [Monoid M] (f : G →* M)
    (hf : N ≤ MonoidHom.mker f) : Submonoid.Normal.con N ≤ Con.ker f := by
  rintro x y ⟨n₁, h₁, n₂, h₂, h⟩
  have e₁ : f n₁ = 1 := hf h₁
  have e₂ : f n₂ = 1 := hf h₂
  rw [Con.ker_rel]
  simpa [e₁, e₂] using congrArg f h

lemma _root_.Submonoid.Normal.con_toSubmonoid {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] : Submonoid.Normal.con N.toSubmonoid = QuotientGroup.con N := by
  refine Con.ext fun x y ↦ ?_
  change _ ↔ QuotientGroup.leftRel N x y
  rw [QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨n₁, h₁, n₂, h₂, h⟩
    have : x⁻¹ * y = n₁ * n₂⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
    exact this ▸ N.mul_mem h₁ (N.inv_mem h₂)
  · intro h
    exact ⟨x⁻¹ * y, h, 1, N.one_mem, by simp⟩

open scoped Pointwise in
lemma rho_mem_relInvariants' {v : V} (hv : v ∈ π.relInvariants N) (g : G) :
    π g v ∈ π.relInvariants N := by
  intro n hn
  obtain ⟨n', hn', h : g * n' = n * g⟩ : n * g ∈ g • (N : Set G) := by
    rw [Submonoid.Normal.isNormal]
    exact ⟨n, hn, rfl⟩
  rw [← mul_apply_eq_comp, ← map_mul, ← h, map_mul, mul_apply_eq_comp, hv n' hn']

/-- For a normal subgroup `N` of `G`, `ρ.relInvariantsRho N` is the representation of `G` on
the `N`-invariants `ρ.relInvariants N` induced by `ρ`. -/
@[simps] def relInvariantsRho : ContRepresentation R G (π.relInvariants N) := ⟨{
  toFun g       := (π g).restrict (fun _ hv ↦ π.rho_mem_relInvariants' N hv g)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp
}⟩

/-- A continuous intertwining map `f : ρ →ⁱL ρ'` restricts to a continuous intertwining map
`ρ.relInvariantsRho N →ⁱL ρ'.relInvariantsRho N` on `N`-invariants. -/
def relInvariantsIntertwining {π'' : ContRepresentation R G W} (f : π →ⁱL π'') :
    π.relInvariantsRho N →ⁱL π''.relInvariantsRho N where
  toContinuousLinearMap := f.toContinuousLinearMap.restrict (by
    intro v hv n hn
    have := (f.isIntertwining n v).symm
    rwa [hv n hn] at this)
  isIntertwining' g := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrict_apply]
    exact f.isIntertwining g v

lemma le_relInvariantsRho_ker : N ≤ MonoidHom.mker (π.relInvariantsRho N).toMonoidHom := by
  intro n hn
  rw [MonoidHom.mem_mker]
  ext ⟨_,hv⟩
  apply hv _ hn

/-- The representation of the quotient monoid `G ⧸ N` on the `N`-invariants `π.relInvariants N`,
obtained by factoring `π.relInvariantsRho N` through the quotient map `N.mkQ : G →* G ⧸ N`. -/
def relInvariantsInfl :
    ContRepresentation R (G ⧸ N) (π.relInvariants N) :=
  ⟨N.liftQ (π.relInvariantsRho N).toMonoidHom (π.le_relInvariantsRho_ker N)⟩

/-- The continuous intertwining map `π.relInvariantsInfl N →ⁱL π''.relInvariantsInfl N` of
representations of the quotient monoid, induced by a continuous intertwining map
`f : π →ⁱL π''`. -/
def relInvariantsIntertwining' {π'' : ContRepresentation R G W} (f : π →ⁱL π'') :
    π.relInvariantsInfl N →ⁱL π''.relInvariantsInfl N where
  toContinuousLinearMap := (relInvariantsIntertwining N f).toContinuousLinearMap
  isIntertwining' g := by
    induction g using Con.induction_on with
    | H g => exact (relInvariantsIntertwining N f).isIntertwining' g

variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W]
  (φ : G →ₜ* H) (π)

/-- The underlying module of the coinduced continuous representation. -/
@[simps]
def coindV : Submodule R C(H, V) where
  carrier   := {f | ∀ g h, f (φ g * h) = π g (f h)}
  add_mem'  := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
lemma mem_coindV (f : C(H, V)) : f ∈ π.coindV φ ↔ ∀ g h, f (φ g * h) = π g (f h) := Iff.rfl

instance : ContinuousSMul R (π.coindV φ) where
  continuous_smul := by continuity

variable [SeparatelyContinuousMul H]
--variable [IsTopologicalGroup H]

/-- The coinduced continuous representation where the action of `H` is defined by
  `h ↦ f ↦ f ∘ (· * h)`. -/
def coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ) where
  toMonoidHom.toFun h := {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
    cont := continuous_induced_rng.2 <| by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtypeVal}
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

@[simp] lemma coind_apply_coe_apply (h : H) (f : π.coindV φ) (x : H) :
    (coind φ π h f).val x = f.val (x * h) := rfl

lemma coind_apply_coe (h : H) (f : π.coindV φ) :
    ↑(coind φ π h f) = f.val.comp (ContinuousMap.mulRight h) := by ext; dsimp

open ContinuousMap
variable [SeparatelyContinuousMul G]

/-- Given a continuous representation `π` of `G` on `V`,
this defines a continuous representation `π.coind₁` of `G` on the function space `C(G, V)`.
The action of an element `g : G` is defined by `f ↦ (x ↦ π g (f (g⁻¹ * x)))`.
This new representation of `G` is isomorphic (assuming that the map `G × V → V` is continuous,
see `coindEquivCoind₁`) to the coinduction along `1 : Unit →ₜ* G` of the trivial representation
of the trivial group on `V`, but the action has been twisted so that the map `const : V → C(G, V)`
is an intertwining map. -/
def coind₁ (π : ContRepresentation R G V) :
    ContRepresentation R G C(G, V) where
  toMonoidHom.toFun g := {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulRight g))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
lemma coind₁_apply_apply (π : ContRepresentation R G V) (g : G) (f : C(G, V)) (x : G) :
    π.coind₁ g f x = π g (f (x * g)) := rfl

/-- The functoriality of `coind₁`. -/
@[simps]
def coind₁Map {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} (f : π₁ →ⁱL π₂) :
    coind₁ π₁ →ⁱL coind₁ π₂ where
  toFun := (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

/-- The component at `π` of the natural transformation `𝟭 ⟶ coind₁`, sending `v` to the constant
function with value `v`. -/
@[simps]
def coind₁ι (π : ContRepresentation R G V) : π →ⁱL coind₁ π where
  toFun := ContinuousMap.const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : ContRepresentation R G V)

omit [TopologicalSpace R] in
/-- Continuity of the twist `F ↦ fun x ↦ π (a x) (F x)` of `C(G, V)`, for `a : C(G, G)`. It
underlies `coindLEquivCoind₁`. -/
private lemma continuous_coindEquivCoind₁_aux (hπ : Continuous fun gv : G × V ↦ π gv.1 gv.2)
    (a : C(G, G)) :
    Continuous fun F : C(G, V) ↦
      (⟨fun x ↦ π (a x) (F x), hπ.comp <| a.continuous.prodMk F.continuous⟩ : C(G, V)) :=
  (continuous_postcomp ⟨_, hπ⟩).comp <| ContinuousMap.continuous_prodMk.comp <|
    (continuous_const (y := a)).prodMk continuous_id

/-- If `G` is a topological group and the action map `(g, v) ↦ π g v` is jointly continuous, then
the underlying module of the coinduction along `1 : Unit →ₜ* G` of the trivial representation of
`Unit` on `V` is continuously linearly equivalent to `C(G, V)`, via the twist
`f ↦ fun x ↦ π x⁻¹ (f x)`, whose inverse is `f ↦ fun x ↦ π x (f x)`. -/
@[simps]
def coindLEquivCoind₁ (hπ : Continuous fun gv : G × V ↦ π gv.1 gv.2) :
    (trivial R Unit V).coindV (1 : Unit →ₜ* G) ≃L[R] C(G, V) where
  toFun f := ⟨fun x ↦ π x⁻¹ (f.val x), hπ.comp <| continuous_inv.prodMk f.val.continuous⟩
  invFun f := ⟨⟨fun x ↦ π x (f x), hπ.comp <| continuous_id.prodMk f.continuous⟩, by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  continuous_toFun := by
    exact (continuous_coindEquivCoind₁_aux π hπ ⟨Inv.inv, continuous_inv⟩).comp
      continuous_subtypeVal
  continuous_invFun := by
    exact continuous_induced_rng.2 (continuous_coindEquivCoind₁_aux π hπ (.id G))

/-- If `G` is a topological group and the action map `G × V → V`, `(g, v) ↦ π g v` is (jointly)
continuous, then the coinduction along `1 : Unit →ₜ* G` of the trivial representation of the
trivial group on `V` is equivalent to `π.coind₁`. The underlying equivalence of `C(G, V)` is the
twist `f ↦ fun x ↦ π x⁻¹ (f x)` (see `coindLEquivCoind₁`). -/
def coindEquivCoind₁ (hπ : Continuous fun gv : G × V ↦ π gv.1 gv.2) :
    ((trivial R Unit V).coind (1 : PUnit →ₜ* G)).Equiv π.coind₁ :=
  .mk (coindLEquivCoind₁ π hπ) fun g ↦ by ext; simp

/-- The equivalence between `coind₁` and `coind` of the trivial representation of trivial
  subgroup of `G`. -/
@[deprecated coindEquivCoind₁ +typeChanged (since := "2026-11-16")]
def coind₁Equivcoind : (coind₁ (.trivial R (⊥ : Subgroup G) V)).Equiv
    (coind 1 (.trivial R G V)) :=
  (coindEquivCoind₁ _ (by simpa using continuous_snd)).symm.trans <|
    .mk (ContinuousLinearEquiv.ofEq _ _ (by ext; simp)) fun _ ↦ rfl

end Group

section coind₁ResMap

variable [ContinuousSMul R U] {π' : ContRepresentation R H W} {π}

/-- Given a continuous group homomorphism `φ : H →ₜ* G`, precomposition with `φ` defines a
continuous intertwining map `π.coind₁.restrict φ →ⁱL (π.restrict φ).coind₁`. -/
def coind₁Res (φ : H →ₜ* G) (π : ContRepresentation R G V) :
    π.coind₁.restrict (φ : H →* G) →ⁱL (π.restrict (φ : H →* G)).coind₁ where
  __ := ContinuousMap.compCLM R V φ.toContinuousMap
  isIntertwining' _ := by ext; simp

@[simp]
lemma coind₁Res_apply (φ : H →ₜ* G) (π : ContRepresentation R G V) (F : C(G, V)) (x : H) :
    coind₁Res φ π F x = F (φ x) := rfl

@[simp]
lemma coind₁Res_id (π : ContRepresentation R G V) :
    coind₁Res (ContinuousMonoidHom.id G) π = .id := rfl

/-- Given a continuous group homomorphism `φ : H →ₜ* G`, a continuous intertwining map
`f : π.restrict φ →ⁱL π'` induces a continuous intertwining map
`π.coind₁.restrict φ →ⁱL π'.coind₁`, sending `F : C(G, V)` to `f ∘ F ∘ φ : C(H, W)`. -/
def coind₁ResMap (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') :
    π.coind₁.restrict (φ : H →* G) →ⁱL π'.coind₁ :=
  (coind₁Map f).comp (coind₁Res φ π)

@[simp]
lemma coind₁ResMap_apply (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') (F : C(G, V))
    (x : H) : coind₁ResMap φ f F x = f (F (φ x)) := rfl

lemma coind₁ResMap_id {π' : ContRepresentation R G W} (f : π →ⁱL π') :
    coind₁ResMap (ContinuousMonoidHom.id G) f = coind₁Map f := rfl

/-- The naturality of `coind₁ι` with respect to `coind₁ResMap`. -/
lemma coind₁ResMap_comp_coind₁ι_restrict (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') :
    (coind₁ResMap φ f).comp (π.coind₁ι.restrict (φ : H →* G)) = π'.coind₁ι.comp f := rfl

lemma coind₁Map_comp_coind₁ResMap (φ : H →ₜ* G) {σ : ContRepresentation R H U}
    (f : π.restrict φ →ⁱL π') (g : π' →ⁱL σ) :
    (coind₁Map g).comp (coind₁ResMap φ f) = coind₁ResMap φ (g.comp f) := rfl

lemma coind₁ResMap_comp_coind₁Map_restrict (φ : H →ₜ* G) {ρ : ContRepresentation R G U}
    (g : ρ →ⁱL π) (f : π.restrict (φ : H →* G) →ⁱL π') :
    (coind₁ResMap φ f).comp ((coind₁Map g).restrict (φ : H →* G)) =
      coind₁ResMap φ (f.comp (g.restrict (φ : H →* G))) := rfl

end coind₁ResMap

end ContRepresentation
