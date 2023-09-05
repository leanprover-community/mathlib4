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

abbrev PointedCone (𝕜) (E)
    [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  Submodule { c : 𝕜 // 0 ≤ c } E

namespace PointedCone

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

-- needs fixing
abbrev σ := RingHom.id { c : 𝕜 // 0 ≤ c }

/-- This section is likely no longer relevant as maps between submodules are already defined.
The only thing I should figure out how to add is the coercion between maps between PointedCones
and maps between ConvexCones.
-/

@[simp, norm_cast]
lemma map_coe (S : PointedCone 𝕜 E)
    (f : E →ₛₗ[σ] F) :
    (S.map f : Set F) = f '' S := Submodule.map_coe _ _

end Maps

end PointedCone
