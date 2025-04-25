/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Geometry.Convex.Cone.Basic

/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that as a set a pointed cone is convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "𝕜≥0" => {c : R // 0 ≤ c}

/-- A pointed cone is a submodule of a module with scalars restricted to being nonnegative. -/
abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 ≤ c} E

namespace PointedCone

open Function

section Definitions

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]

/-- Every pointed cone is a convex cone. -/
@[coe]
def toConvexCone (S : PointedCone R E) : ConvexCone R E where
  carrier := S
  smul_mem' c hc _ hx := S.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := S.add_mem hx hy

instance : Coe (PointedCone R E) (ConvexCone R E) where
  coe := toConvexCone

theorem toConvexCone_injective : Injective ((↑) : PointedCone R E → ConvexCone R E) :=
  fun _ _ => by simp [toConvexCone]

@[simp]
theorem pointed_toConvexCone (S : PointedCone R E) : (S : ConvexCone R E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]

@[simp] lemma mem_toConvexCone {S : PointedCone R E} {x : E} : x ∈ S.toConvexCone ↔ x ∈ S := .rfl

@[ext]
theorem ext {S T : PointedCone R E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

lemma convex (S : PointedCone R E) : Convex R (S : Set E) := S.toConvexCone.convex

instance instZero (S : PointedCone R E) : Zero S :=
  ⟨0, S.zero_mem⟩

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def _root_.ConvexCone.toPointedCone {S : ConvexCone R E} (hS : S.Pointed) : PointedCone R E where
  carrier := S
  add_mem' hx hy := S.add_mem hx hy
  zero_mem' := hS
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hS
      convert hS
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert hpos
      · exact hx

@[simp]
lemma _root_.ConvexCone.mem_toPointedCone {S : ConvexCone R E} (hS : S.Pointed) (x : E) :
    x ∈ S.toPointedCone hS ↔ x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
lemma _root_.ConvexCone.coe_toPointedCone {S : ConvexCone R E} (hS : S.Pointed) :
    S.toPointedCone hS = S :=
  rfl

instance canLift : CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed where
  prf S hS := ⟨S.toPointedCone hS, rfl⟩

end Definitions

section Maps

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid G] [Module R G]

/-!

## Maps between pointed cones

There is already a definition of maps between submodules, `Submodule.map`. In our case, these maps
are induced from linear maps between the ambient modules that are linear over nonnegative scalars.
Such maps are unlikely to be of any use in practice. So, we construct some API to define maps
between pointed cones induced from linear maps between the ambient modules that are linear over
*all* scalars.

-/

/-- The image of a pointed cone under a `R`-linear map is a pointed cone. -/
def map (f : E →ₗ[R] F) (S : PointedCone R E) : PointedCone R F :=
  Submodule.map (f : E →ₗ[𝕜≥0] F) S

@[simp, norm_cast]
theorem toConvexCone_map (S : PointedCone R E) (f : E →ₗ[R] F) :
    (S.map f : ConvexCone R F) = (S : ConvexCone R E).map f :=
  rfl

@[simp, norm_cast]
theorem coe_map (S : PointedCone R E) (f : E →ₗ[R] F) : (S.map f : Set F) = f '' S :=
  rfl

@[simp]
theorem mem_map {f : E →ₗ[R] F} {S : PointedCone R E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl

theorem map_map (g : F →ₗ[R] G) (f : E →ₗ[R] F) (S : PointedCone R E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f S

@[simp]
theorem map_id (S : PointedCone R E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| Set.image_id _

/-- The preimage of a convex cone under a `R`-linear map is a convex cone. -/
def comap (f : E →ₗ[R] F) (S : PointedCone R F) : PointedCone R E :=
  Submodule.comap (f : E →ₗ[𝕜≥0] F) S

@[simp, norm_cast]
theorem coe_comap (f : E →ₗ[R] F) (S : PointedCone R F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : PointedCone R E) : S.comap LinearMap.id = S :=
  rfl

theorem comap_comap (g : F →ₗ[R] G) (f : E →ₗ[R] F) (S : PointedCone R G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : E →ₗ[R] F} {S : PointedCone R F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Maps

section PositiveCone

variable (R E)
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone R E :=
  (ConvexCone.positive R E).toPointedCone ConvexCone.pointed_positive

@[simp]
theorem mem_positive {x : E} : x ∈ positive R E ↔ 0 ≤ x :=
  Iff.rfl

@[simp, norm_cast]
theorem toConvexCone_positive : ↑(positive R E) = ConvexCone.positive R E :=
  rfl

end PositiveCone
end PointedCone
