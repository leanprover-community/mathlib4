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
  *Not* assumed to be continuous so that `coind₁`). The reason for this more general
  definition is that it allows us to define the coinduced representation of a continuous
  representation. The coinduced representation is then also a continuous representation without any
  restriction on the topology on `G`.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind₁ π` is the coinduced continuous representation on the space of
  continuous functions from `G` to `V` for a continuous representation `π`.

## Tags
continuous representation, algebra
-/

-- This file needs to import `Mathlib.Algebra.Category.ModuleCat.Topology.Basic` for the definitions
set_option linter.directoryDependency false

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

variable (R G V) in
/-- The trivial continuous representation of a group `G` on a `R`-module `V`. -/
def trivial : ContRepresentation R G V := 1

@[simp]
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl

/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[simps!]
def restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G) :
    ContRepresentation R H V := .comp π φ

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R]
  [IsTopologicalRing R] [ContinuousSMul R V] [ContinuousSMul R W]

open ContinuousMap

/-- Continuous representation (co)induced on the space of continuous functions from `G` to `V`. -/
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

end ContRepresentation
