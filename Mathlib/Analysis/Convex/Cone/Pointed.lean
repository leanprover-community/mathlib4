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

We define a pointed cones as convex cones which contain `0`· This is a bundled version of
`ConvexCone.Pointed`· Pointed cones have a nicer algebraic structure than convex cones· The form
a submodule of the ambient space when the scalars are restricted to being positive· This allows us
to use the Module API to work with convex cones.


## TODO

- Rewrite proper cones using pointed cones.
- Construct products and/or direct sums of pointed cones.

-/

/-- A pointed cone is a convex cone that contains  `0`· -/
structure PointedCone (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommMonoid E]
     [SMul 𝕜 E] extends ConvexCone 𝕜 E where
-- `0` is in the carrier
  zero_mem' : 0 ∈ carrier

namespace PointedCone


section SMul
variable {𝕜 : Type*} [OrderedSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [SMul 𝕜 E]

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) :=
  ⟨fun K => K.1⟩

theorem ext' : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) := fun S T h => by
  cases S; cases T; congr

instance instSetLike : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.ext' (SetLike.coe_injective h)

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_coe {x : E} {S : PointedCone 𝕜 E} : x ∈ (S : ConvexCone 𝕜 E) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem zero_mem (S : PointedCone 𝕜 E) : 0 ∈ S :=
  S.zero_mem'

instance instZero (S : PointedCone 𝕜 E) : Zero S :=
  ⟨0, S.zero_mem⟩

end SMul


section Maps
variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
variable {G : Type*} [AddCommMonoid G] [Module 𝕜 G]

/-- The image of a convex cone under a `𝕜`-linear map is a convex cone· -/
def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F where
  toConvexCone := (S.toConvexCone).map f
  zero_mem' := ⟨0, by simp⟩

@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y

theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f S

@[simp]
theorem map_id (S : PointedCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| Set.image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone· -/
def comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : PointedCone 𝕜 E where
  toConvexCone := ConvexCone.comap (f : E →ₗ[𝕜] F) S
  zero_mem' := by simp [ConvexCone.comap]

@[simp]
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
variable [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module· -/
def positive : PointedCone 𝕜 E where
  toConvexCone := ConvexCone.positive 𝕜 E
  zero_mem' := ConvexCone.pointed_positive _ _

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone

section Module

/-!
## Module Instance

In this section, we put a module instance over pointed cones, where the scalars are restricted to
being non-negative· We also show that the type of pointed cones in a module is equivalent to the
type of submodules of the ambient space when the scalars are restricted to being non-negative.

-/

variable {𝕜 : Type*} [OrderedSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {S : Type*} {S : PointedCone 𝕜 E}

local instance : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

protected theorem smul_mem {c : 𝕜} {x : E} (hc : 0 ≤ c) (hx : x ∈ S) : c • x ∈ S := by
  cases' eq_or_lt_of_le hc with hzero hpos
  · rw [← hzero, zero_smul]
    exact S.zero_mem
  · exact @ConvexCone.smul_mem 𝕜 E _ _ _ S _ _ hpos hx

instance hasSmul : SMul { c : 𝕜 // 0 ≤ c } S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, S.smul_mem hc hx⟩

instance hasNsmul : SMul ℕ S where
  smul := fun n x => (n : { c : 𝕜 // 0 ≤ c }) • x

@[simp]
protected theorem coe_smul (x : S) (n : { c : 𝕜 // 0 ≤ c }) : n • x = n • (x : E) :=
  rfl

@[simp]
protected theorem nsmul_eq_smul_cast (x : S) (n : ℕ) :
    n • (x : E) = (n : { c : 𝕜 // 0 ≤ c }) • (x : E) :=
  nsmul_eq_smul_cast _ _ _

@[simp]
theorem coe_nsmul (x : S) (n : ℕ) : (n • x : E) = n • (x : E) := by
  -- simp_rw [PointedCone.coe_smul, PointedCone.nsmul_eq_smul_cast]; rfl
  simp_rw [PointedCone.nsmul_eq_smul_cast]; rfl

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance instAddMemClass : AddMemClass (PointedCone 𝕜 E) E where
  add_mem ha hb := add_mem ha hb

instance instAddCommMonoid : AddCommMonoid S :=
  Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective
    rfl (by aesop) coe_nsmul
    -- Note: linter says `coe_add` is a syntactic tautology

/-- `addMonoidHom` structure on the inclusion map of a pointed cone inside the ambient space. -/
def subtype.addMonoidHom : S →+ E where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' := by simp

@[simp]
theorem coeSubtype.addMonoidHom : (subtype.addMonoidHom : S → E) = Subtype.val := rfl

instance instModule : Module { c : 𝕜 // 0 ≤ c } S := by
  apply Function.Injective.module ({ c : 𝕜 // 0 ≤ c }) subtype.addMonoidHom
  simp only [coeSubtype.addMonoidHom, Subtype.coe_injective]
  simp -- a single `simp` does not work!

/-- `linearMap` structure on the inclusion map of a pointed cone inside the ambient space. -/
def subtype.linearMap : S →ₗ[{ c : 𝕜 // 0 ≤ c }] E where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

/-- A pointed cone is a submodule of the ambient when the scalars are restricted to be
non-negative. -/
def toSubmodule (S : PointedCone 𝕜 E) : Submodule { c : 𝕜 // 0 ≤ c } E where
  carrier := S
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    cases' eq_or_lt_of_le hc with hzero hpos
    · convert S.zero_mem
      simpa [← hzero] using smul_eq_zero_of_left rfl x
    · apply ConvexCone.smul_mem
      convert hpos
      exact hx

/-- Any submodule (over non-negative scalars) of the ambient space is a pointed cone. -/
def ofSubmodule (M : Submodule { c : 𝕜 // 0 ≤ c } E) : (PointedCone 𝕜 E) where
  carrier := M
  smul_mem' := fun c hc _ hx => M.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' := fun _ hx _ hy => M.add_mem hx hy
  zero_mem' := M.zero_mem

/-- The equivalence between pointed cones and submodules· -/
def toSubmoduleEquiv : (PointedCone 𝕜 E) ≃ (Submodule { c : 𝕜 // 0 ≤ c } E) where
  toFun := toSubmodule
  invFun := ofSubmodule
  left_inv := fun S => by aesop
  right_inv := fun M => by aesop

end Module

section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner dual cone of a pointed cone is a pointed cone· -/
def dual (S : PointedCone ℝ E) : PointedCone ℝ E where
  toConvexCone := (S : Set E).innerDualCone
  zero_mem' := pointed_innerDualCone (S : Set E)

@[simp]
theorem coe_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl

@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop

end Dual

end PointedCone
