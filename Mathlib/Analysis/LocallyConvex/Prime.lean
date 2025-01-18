/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Analysis.LocallyConvex.Polar

/-!
# Prime map

-/

variable {𝕜 E F : Type*}

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

namespace LinearMap

variable (C : Set E)

/-- The prime of `s : Set E` is given by the set of all `y` in `polar C` such that `B x y = 1`
for all `x ∈ s`. -/
def prime (s : Set C) : Set (B.polar C) :=
  { y : (B.polar C) | ∀ x ∈ s, B x y = 1 }

-- For now, take it as a hypothesis on C that (C′)‵ = C
-- Normally we would assume that C satisfies the hypothesis of the bipolar theorem.
variable (bipolar : B.flip.polar (B.polar C) = C)

def lower_prime :=
  (Equiv.Set.congr (Equiv.setCongr (bipolar))).toFun ∘ (B.flip.prime (B.polar C))

theorem prime_gc  :
    GaloisConnection (OrderDual.toDual ∘ (B.prime C))
      (((Equiv.Set.congr (Equiv.setCongr (bipolar))).toFun ∘ (B.flip.prime (B.polar C))) ∘
        OrderDual.ofDual) := fun s t => by
  constructor
  · intro h
    simp
    simp at h
    intro x hx
    rw [prime]
    simp [bipolar]
    intro a ha ha2
    rw [OrderDual.toDual_le] at h
    simp at h
    have e1: ⟨a, ha⟩ ∈ B.prime C s := h ha2
    rw [prime] at e1
    simp at e1
    exact e1 x (Subtype.coe_prop x) hx
  · intro h
    simp only [Function.comp_apply]
    rw [OrderDual.toDual_le]
    intro x hx
    rw [prime]
    simp
    intro a ha ha2
    have e2 : ⟨a, ha⟩ ∈ (((Equiv.Set.congr (Equiv.setCongr (bipolar))).toFun ∘
      B.flip.prime (B.polar C)) ∘ ⇑OrderDual.ofDual) t := h ha2
    simp at e2
    obtain ⟨ha, ha2⟩ := e2
    rw [prime] at ha2
    simp at ha2
    exact ha2 (↑x) x.property hx

end LinearMap
