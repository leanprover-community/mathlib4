/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Prod
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Products of star-ordered rings
-/

variable {α β ι : Type*} {κ : ι → Type*}

open AddSubmonoid in
instance Prod.instStarOrderedRing
    [NonUnitalSemiring α] [NonUnitalSemiring β] [PartialOrder α] [PartialOrder β]
    [StarRing α] [StarRing β] [StarOrderedRing α] [StarOrderedRing β] :
    StarOrderedRing (α × β) where
  le_iff := Prod.forall.2 fun xa xy => Prod.forall.2 fun ya yb => by
    have :
        closure (Set.range fun s : α × β ↦ star s * s) =
          (closure <| Set.range fun s : α ↦ star s * s).prod
          (closure <| Set.range fun s : β ↦ star s * s) := by
      rw [← closure_prod (Set.mem_range.2 ⟨0, by simp⟩) (Set.mem_range.2 ⟨0, by simp⟩),
        Set.prod_range_range_eq]
      simp_rw [Prod.mul_def, Prod.star_def]
    simp only [mk_le_mk, Prod.exists, mk_add_mk, mk.injEq, StarOrderedRing.le_iff, this,
      AddSubmonoid.mem_prod, exists_and_exists_comm, and_and_and_comm]

open Set AddSubmonoid in
instance Pi.instStarOrderedRing
    [∀ i, NonUnitalSemiring (κ i)] [∀ i, PartialOrder (κ i)]
    [∀ i, StarRing (κ i)] [∀ i, StarOrderedRing (κ i)] :
    StarOrderedRing (∀ i, κ i) where
  le_iff f g := by
    have h₁ :
        closure (Set.range fun s : (∀ i, κ i) ↦ star s * s) =
          AddSubmonoid.pi (Set.univ : Set ι)
            (fun i => closure <| Set.range fun s : κ i => star s * s) := by
      sorry
    refine ⟨?mp, ?mpr⟩
    case mp =>
      intro hfg
      simp_rw [Pi.le_def, StarOrderedRing.le_iff] at hfg
      let q i := Classical.choose (hfg i)
      have hq i := Classical.choose_spec (hfg i)
      refine ⟨q, ?_⟩
      rw [h₁]
      refine ⟨fun i _ => (hq i).1, ?_⟩
      ext i
      simp only [add_apply]
      exact (hq i).2
    case mpr =>
      intro hfg
      simp_rw [Pi.le_def, StarOrderedRing.le_iff]
      intro i
      obtain ⟨p, hp, hp'⟩ := hfg
      rw [h₁] at hp
      exact ⟨p i, hp i (by simp), by rw [funext_iff] at hp'; exact hp' i⟩
