/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Group.Submonoid.Finite
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Pi

/-!
# Pi-types of star-ordered rings
-/

variable {ι : Type*} [Finite ι]
  {A : ι → Type*} [Π i, PartialOrder (A i)] [Π i, NonUnitalSemiring (A i)]
  [Π i, StarRing (A i)] [Π i, StarOrderedRing (A i)]

open AddSubmonoid in
instance Pi.instStarOrderedRing : StarOrderedRing (Π i, A i) where
  le_iff := fun xa xy => by
    simp only [Pi.le_def, StarOrderedRing.le_iff]
    have : closure (Set.range fun s : Π i, A i ↦ star s * s) =
        pi Set.univ fun i => (closure <| Set.range fun s : A i ↦ star s * s) := by
      rw [← closure_pi (fun i => Set.mem_range.mpr ⟨0, by simp⟩)]
      congr
      ext x
      simp only [Set.mem_range, funext_iff, mul_apply, star_apply, Set.mem_pi,
        Set.mem_univ, forall_const]
      exact ⟨fun ⟨y, hy⟩ i => ⟨y i, hy i⟩, fun h => ⟨fun i => h i |>.choose,
        fun i => h i |>.choose_spec⟩⟩
    simp only [this, mem_pi, Set.mem_univ, forall_const]
    refine ⟨fun h => ?_, ?_⟩
    · simp only [funext_iff, add_apply]
      exact ⟨fun i => h i |>.choose, fun i => h i |>.choose_spec.1, fun i => h i |>.choose_spec.2⟩
    · simp only [forall_exists_index, and_imp]
      intro x h rfl i
      exact ⟨x i, by simp [h]⟩
