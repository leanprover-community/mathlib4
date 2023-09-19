/-
Copyright (c) 2023 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that as a set a pointed cone is convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

## TODO

- Rewrite proper cones using pointed cones.
- Construct products and/or direct sums of pointed cones.

-/

variable {𝕜 E F G : Type*}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone (𝕜 : Type*) (E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  Submodule { c : 𝕜 // 0 ≤ c } E

namespace PointedCone

section Definitions

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) where
  coe := fun S => {
    carrier := S
    smul_mem' := fun c hc _ hx => S.smul_mem ⟨c, le_of_lt hc⟩ hx
    add_mem' := fun _ hx _ hy => S.add_mem hx hy }

theorem coe_injective : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) :=
  fun _ _ => by simp

@[simp]
theorem coe_pointed (S : PointedCone 𝕜 E) : (S : ConvexCone 𝕜 E).Pointed := by
  simp [ConvexCone.Pointed]

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

instance instZero (S : PointedCone 𝕜 E) : Zero S :=
  ⟨0, S.zero_mem⟩

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def _root_.ConvexCone.toSubmodule {S : ConvexCone 𝕜 E} (hS : S.Pointed) :
    Submodule { c : 𝕜 // 0 ≤ c } E where
  carrier := S
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := hS
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    cases' eq_or_lt_of_le hc with hzero hpos
    · unfold ConvexCone.Pointed at hS
      convert hS
      simp [← hzero]
    · apply ConvexCone.smul_mem
      convert hpos
      exact hx

@[simp]
lemma _root_.ConvexCone.mem_toSubmodule {S : ConvexCone 𝕜 E} (hS : S.Pointed) (x : E) :
    x ∈ S.toSubmodule hS ↔ x ∈ S :=
  Iff.rfl

@[simp]
lemma _root_.ConvexCone.coe_toSubmodule {S : ConvexCone 𝕜 E} (hS : S.Pointed) :
    (S.toSubmodule hS : Set E) = S :=
  rfl

end Definitions

section Maps

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable [AddCommMonoid G] [Module 𝕜 G]

/-!

## Maps between pointed cones

There is already a definition of maps between submodules, `Submodule.map`. In our case, these maps
are induced from linear maps between the ambient modules that are linear over nonnegative scalars.
Such maps are unlikely to be of any use in practice. So, we construct some API to define maps
between pointed cones induced from linear maps between the ambient modules that are linear over
*all* scalars.

-/

/-- The image of a pointed cone under a `𝕜`-linear map is a pointed cone. -/
def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F :=
  let f' := LinearMap.restrictScalars { c : 𝕜 // 0 ≤ c } f
  Submodule.map f' S

@[simp, norm_cast]
theorem coe_map (S : PointedCone 𝕜 E) (f : E →ₗ[𝕜] F) : (S.map f : Set F) = f '' S :=
  rfl

@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl

theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f S

@[simp]
theorem map_id (S : PointedCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| Set.image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : PointedCone 𝕜 E :=
  let f' := LinearMap.restrictScalars { c : 𝕜 // 0 ≤ c } f
  Submodule.comap f' S

@[simp, norm_cast]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : PointedCone 𝕜 E) : S.comap LinearMap.id = S :=
  rfl

theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Maps

section PositiveCone

variable (𝕜 E)
variable [OrderedSemiring 𝕜]
variable [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone 𝕜 E :=
  (ConvexCone.positive 𝕜 E).toSubmodule <| ConvexCone.pointed_positive 𝕜 E

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone
section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner dual cone of a pointed cone is a pointed cone. -/
def dual (S : PointedCone ℝ E) : PointedCone ℝ E :=
  ((S : Set E).innerDualCone).toSubmodule <| pointed_innerDualCone (S : Set E)

@[simp, norm_cast]
theorem coe_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl

@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop

end Dual

end PointedCone
