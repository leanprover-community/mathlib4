/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Logic.Function.FiberPartition
/-!

This file provides some API surrounding `Function.Fiber` (see
`Mathlib/Logic/Function/FiberPartition.lean`) in the presence of a topology on the domain of the
function.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/


open Function

variable {S Y : Type*} (f : S → Y)

namespace TopologicalSpace.Fiber

variable [TopologicalSpace S]

/-- The canonical map from the disjoint union induced by `f` to `S`. -/
@[simps apply]
def sigmaIsoHom : C((x : Fiber f) × x.val, S) where
  toFun | ⟨a, x⟩ => x.val

lemma sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

lemma sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

/-- The inclusion map from a component of the disjoint union induced by `f` into `S`. -/
def sigmaIncl (a : Fiber f) : C(a.val, S) where
  toFun x := x.val

/-- The inclusion map from a fiber of a composition into the intermediate fiber. -/
def sigmaInclIncl {X : Type*} (g : Y → X) (a : Fiber (g ∘ f))
    (b : Fiber (f ∘ (sigmaIncl (g ∘ f) a))) :
    C(b.val, (Fiber.mk f (b.preimage).val).val) where
  toFun x := ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image, Fiber.mk_image, this, ← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩

variable (l : LocallyConstant S Y) [CompactSpace S]

instance (x : Fiber l) : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  rw [← isCompact_iff_compactSpace, ← hy]
  exact (l.2.isClosed_fiber _).isCompact

instance : Finite (Fiber l) :=
  have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _

end TopologicalSpace.Fiber
