/-
Copyright (c) 2023 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that as a set a pointed cone is convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

variable {𝕜 E F G : Type*}

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone (𝕜 E) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  Submodule {c : 𝕜 // 0 ≤ c} E

/-- Give a set `s` in `E`, `toPointedCone 𝕜 s` is the cone consisting of linear combinations of
elements in `s` with non-negative coefficients. -/
abbrev Set.toPointedCone (𝕜) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (s : Set E) :=
  Submodule.span {c : 𝕜 // 0 ≤ c} s

-- TODO: add more API for `Set.toPointedCone`

namespace PointedCone

open Function

section Definitions

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Every pointed cone is a convex cone. -/
@[coe]
def toConvexCone (S : PointedCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := S
  smul_mem' c hc _ hx := S.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := S.add_mem hx hy

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) where
  coe := toConvexCone

theorem toConvexCone_injective : Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) :=
  fun _ _ => by simp [toConvexCone]

@[simp]
theorem toConvexCone_pointed (S : PointedCone 𝕜 E) : (S : ConvexCone 𝕜 E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

instance instZero (S : PointedCone 𝕜 E) : Zero S :=
  ⟨0, S.zero_mem⟩

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def _root_.ConvexCone.toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) : PointedCone 𝕜 E where
  carrier := S
  add_mem' hx hy := S.add_mem hx hy
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
lemma _root_.ConvexCone.mem_toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) (x : E) :
    x ∈ S.toPointedCone hS ↔ x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
lemma _root_.ConvexCone.coe_toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) :
    S.toPointedCone hS = S :=
  rfl

instance canLift : CanLift (ConvexCone 𝕜 E) (PointedCone 𝕜 E) (↑) ConvexCone.Pointed where
  prf S hS := ⟨S.toPointedCone hS, rfl⟩

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
  Submodule.map (f : E →ₗ[𝕜≥0] F) S

@[simp, norm_cast]
theorem toConvexCone_map (S : PointedCone 𝕜 E) (f : E →ₗ[𝕜] F) :
    (S.map f : ConvexCone 𝕜 F) = (S : ConvexCone 𝕜 E).map f :=
  rfl

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
  Submodule.comap (f : E →ₗ[𝕜≥0] F) S

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
  (ConvexCone.positive 𝕜 E).toPointedCone <| ConvexCone.pointed_positive 𝕜 E

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp, norm_cast]
theorem toConvexCone_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone
section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner dual cone of a pointed cone is a pointed cone. -/
def dual (S : PointedCone ℝ E) : PointedCone ℝ E :=
  ((S : Set E).innerDualCone).toPointedCone <| pointed_innerDualCone (S : Set E)

@[simp, norm_cast]
theorem toConvexCone_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl

@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  rfl

end Dual

end PointedCone
