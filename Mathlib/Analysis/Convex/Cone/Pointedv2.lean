/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Module.Submodule.Basic

variable {𝕜 : Type*} [OrderedSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

/-- We consider the ambient space `E` as a module over just the positive scalars. -/
local instance : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)
local instance : IsScalarTower { c : 𝕜 // 0 ≤ c } 𝕜 E := SMul.comp.isScalarTower ↑Nonneg.coeRingHom

abbrev PointedCone (𝕜) (E)
    [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  Submodule { c : 𝕜 // 0 ≤ c } E

namespace PointedCone

set_option quotPrecheck false in
notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) where
  coe := fun S => {
    carrier := S
    smul_mem' := fun c hc _ hx => S.smul_mem ⟨c, le_of_lt hc⟩ hx
    add_mem' := fun _ hx _ hy => S.add_mem hx hy }

theorem coe_injective : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) :=
  fun _ _ => by simp

instance instSetLike : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.coe_injective (SetLike.coe_injective h)

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

section Maps

variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
variable {G : Type*} [AddCommMonoid G] [Module 𝕜 G]

/-- This section is likely no longer relevant as maps between submodules are already defined.
The only thing I should figure out how to add is the coercion between maps between PointedCones
and maps between ConvexCones.
-/

def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F :=
  let f' := LinearMap.restrictScalars { c : 𝕜 // 0 ≤ c } f
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

/-- The preimage of a proper cone under a `𝕜`-linear map is a convex cone. -/
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

end PointedCone
