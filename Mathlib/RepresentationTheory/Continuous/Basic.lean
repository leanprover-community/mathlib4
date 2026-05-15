/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
## Continuous representations

This file defines continuous representations of a monoid `G` on a `R`-module `V` and
related basic results.

## Main Results

* `ContRepresentation R G V` is the type of continuous representations of a monoid `G` on a
  `R`-module `V` which is a topological addgroup (where the action of `G` on `V` is
  *not* assumed to be continuous). The reason for this more general definition is that it allows us
  to define the coinduced representation of a continuous representation as also a continuous
  representation without any restriction on the topology on `G`.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind₁ π` is the coinduced continuous representation on the space of
  continuous functions from `G` to `V` for a continuous representation `π`.

## Tags
continuous representation, algebra
-/

@[expose] public section

variable (R G V W : Type*) [Monoid G]
  [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W]

/-- A continuous representation of a group `G` on a `R`-module `V` which is a topological addgroup
  is a homomorphism `G →* V →L[R] V`. -/
abbrev ContRepresentation := G →* V →L[R] V

/-- Every continuous representation "is" a representation. -/
abbrev ContRepresentation.toRepresentation (π : ContRepresentation R G V) :
    Representation R G V :=
  .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π

variable {R G V W}
#exit
/-- A continuous intertwining map between two continuous representations is an intertwining map
  which is also continuous. -/
structure ContIntertwiningMap (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
    extends Representation.IntertwiningMap π₁.toRepresentation π₂.toRepresentation where
  cont : Continuous toFun

/-- notation for continuous intertwining maps -/
scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContIntertwiningMap

open ContRepresentation

@[ext]
lemma ext {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {f g : π₁ →ⁱL π₂} (h : f.toIntertwiningMap = g.toIntertwiningMap) : f = g := by
  cases f; cases g; congr

lemma toIntertwiningMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toIntertwiningMap :=
  fun _ _ ↦ ext

lemma toFun_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toFun := fun f g h ↦ by
  ext x; exact congr_fun h x

instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    FunLike (π₁ →ⁱL π₂) V W where
  coe f := f.toFun
  coe_injective' := toFun_injective

lemma isIntertwining {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v) :=
  f.toIntertwiningMap.isIntertwining _ _ g v

instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    ContinuousLinearMapClass (π₁ →ⁱL π₂) R V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous := cont

/-- Coerce a continuous intertwining map to a continuous map. -/
abbrev toContinuousMap {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) : C(V, W) := f

end ContIntertwiningMap

namespace ContRepresentation


structure Equiv (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) extends
    ContIntertwiningMap π₁ π₂, V ≃L[R] W where mk'' ::

attribute [coe] Equiv.toContIntertwiningMap

/-- Underlying continuous linear isomorphism of an equivalence of continuous representations. -/
add_decl_doc Equiv.toContinuousLinearEquiv

/-- The continuous intertwining map underlying an equivalence of continuous representations. -/
add_decl_doc Equiv.toContIntertwiningMap

namespace Equiv

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W} (φ : Equiv ρ σ)

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
def mk (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ where
  __ := e
  cont := e.continuous
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(he g))

lemma toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toLinearEquiv = e := rfl

lemma toIntertwiningMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContIntertwiningMap = ⟨⟨e.toContinuousLinearMap, he⟩, _⟩ := rfl

@[simp]
lemma toLinearMap_mk' (e : V ≃ₗ[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
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

instance : LinearEquivClass (σ.Equiv ρ) R W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

@[simp]
lemma mk_apply {e : V ≃ₗ[R] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (v : V) :
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
  φ.toLinearEquiv.toLinearMap = φ.toIntertwiningMap.toLinearMap := rfl

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
lemma _root_.LinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃ₗ[R] W}
    (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) (g : G) :
    e.symm ∘ₗ (σ g) = (ρ g) ∘ₗ e.symm := by
  apply e.comp_toLinearMap_eq_iff _ _ |>.1
  rw [← comp_assoc, ← comp_assoc, he g, e.comp_symm, id_comp, comp_assoc, e.comp_symm, comp_id]

@[simp]
lemma mk_symm {e : V ≃ₗ[R] W} (he : ∀ g, e ∘ₗ (ρ g) = (σ g) ∘ₗ e) :
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

variable (R G V) in
/-- The trivial continuous representation of a group `G` on a `R`-module `V`. -/
def trivial : ContRepresentation R G V := 1

@[simp]
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl

/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[simps!]
def restrict {H : Typenst_11 : IsTopologicalGroup H]
        (π : ContRepresentation R G V) (h : H) (x : ↥(coindV φ π)),
        *} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G) :
    ContRepresentation R H V := .comp π φ

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W]

variable {H : Type*} [Group H] [TopologicalSpace H]
variable (φ : G →ₜ* H) (π : ContRepresentation R G V)

@[simps]
def coindV : Submodule R C(H,V) where
  carrier   := {f | ∀ g h, f (φ g * h) = π g (f h)}
  add_mem'  := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
lemma mem_coindV (f : C(H, V)) : f ∈ π.coindV φ ↔ ∀ g h, f (φ g * h) = π g (f h) := Iff.rfl

instance : ContinuousSMul R (π.coindV φ) where
  continuous_smul := by continuity

variable [IsTopologicalRing R] [IsTopologicalGroup G] [IsTopologicalGroup H]

@[simps]
def coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ) where
  toFun h := {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
    cont := continuous_induced_rng.2 <| by
      simpa using (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  map_one' := by ext; simp
  map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

open ContinuousMap

/-- Given a continuous representation `π` of `G` on `V`,
this defines a Continuous representation `π.coind₁` of `G` on the function space `C(G,V)`.
The action of an element `g : G` is defined by `f ↦ (x ↦ π g (f (g⁻¹ * x)))`.
This new representation of `G` is isomorphic to the continuous coinduction
of the trivial representation of the trivial subgroup of `G`, but the action has been
twisted so that the map `const : V → C(G,V)` is an intertwining map. -/
@[simps]
def coind₁ (π : ContRepresentation R G V) :
    ContRepresentation R G C(G, V) where
  toFun g := {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

/-- The functoriality of `coind₁`. -/
@[simps]
def coind₁_map (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) (f : π₁ →ⁱL π₂) :
    coind₁ π₁ →ⁱL coind₁ π₂ where
  toFun := .comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp f.toContinuousMap

/-- The naturality of the transformation from `𝟭 ⟶ coind₁`. -/
@[simps]
def coind₁_ι (π : ContRepresentation R G V) : π →ⁱL coind₁ π where
  toFun := .const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

-- abbrev coind₁Equivcoind

end ContRepresentation
