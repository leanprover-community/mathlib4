/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Module.Submodule.Basic


/-!
# Pointed cones

A *pointed cone* is defined to be a convex cone which contains `0`. This is a bundled version of
`ConvexCone.Pointed`. Pointed cones have a nicer algebraic structure than convex cones. They form
a submodule of the ambient space when the scalars are restricted to being positive. This allows us
to use the `Module` API to work with convex cones.


## TODO

- Rewrite proper cones using pointed cones.
- Construct products and/or direct sums of pointed cones.

-/

variable {𝕜 E F G : Type*}

/-- A pointed cone is a `Submodule` of the ambient space with scalars restricted to being
non-negative. -/
abbrev PointedCone (𝕜 : Type*) (E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  have : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)
  Submodule { c : 𝕜 // 0 ≤ c } E

namespace PointedCone

set_option quotPrecheck false in
/-- The set of non-negative elements. -/
scoped notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

section Definitions

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- We consider the ambient space `E` as a module over just the non-negative scalars. -/
local instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

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

instance instSetLike : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.coe_injective (SetLike.coe_injective h)

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

instance instZero (S : PointedCone 𝕜 E) : Zero S :=
  ⟨0, S.zero_mem⟩

/-- The `PointedCone` constructed from a pointed `ConvexCone`. -/
def ofConvexCone (S : ConvexCone 𝕜 E) (hS : S.Pointed) : Submodule 𝕜≥0 E where
  carrier := S
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := hS
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    cases' eq_or_lt_of_le hc with hzero hpos
    · unfold ConvexCone.Pointed at hS
      convert hS
      simpa [← hzero] using smul_eq_zero_of_left rfl x
    · apply ConvexCone.smul_mem
      convert hpos
      exact hx

@[simp, norm_cast]
theorem ofConvexCone_eq_self (S : ConvexCone 𝕜 E) (hS : S.Pointed) : ofConvexCone S hS = S := by
  rfl

end Definitions

section Maps

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable [AddCommMonoid G] [Module 𝕜 G]

instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)
instance : IsScalarTower 𝕜≥0 𝕜 E := SMul.comp.isScalarTower ↑Nonneg.coeRingHom
instance : IsScalarTower 𝕜≥0 𝕜 F := SMul.comp.isScalarTower ↑Nonneg.coeRingHom

/-- The image of a pointed cone under a `𝕜`-linear map is a pointed cone. -/
def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F :=
  let f' := LinearMap.restrictScalars 𝕜≥0 f
  Submodule.map f' S

@[simp, norm_cast]
lemma coe_map (S : PointedCone 𝕜 E) (f : E →ₗ[𝕜] F) : (S.map f : Set F) = f '' S :=
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

/-- We consider the ambient space `E` as a module over just the non-negative scalars. -/
local instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone 𝕜 E :=
  ofConvexCone (ConvexCone.positive 𝕜 E) (ConvexCone.pointed_positive 𝕜 E)

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
  ofConvexCone (S : Set E).innerDualCone $ pointed_innerDualCone (S : Set E)

@[simp]
theorem coe_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl

@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop

end Dual

end PointedCone
