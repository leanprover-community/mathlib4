/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Order.Filter.Germ
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Order.Hom.Ring
--import Mathlib.Topology.NhdsSet

/-! ## Germs of a continuous function germs

TODO: add a module docstring, eventually
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped Topology

open Filter Set

namespace Filter.Germ

/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f => f x) fun f g h => by dsimp only; rw [Eventually.self_of_nhds h]

theorem value_smul {X α β : Type*} [TopologicalSpace X] {x : X} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

@[to_additive]
def valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →* E
    where
  toFun := Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

def valueₗ {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
    {x : X} : Germ (𝓝 x) E →ₗ[𝕜] E :=
  { Filter.Germ.valueAddHom with map_smul' := fun _ φ => Germ.inductionOn φ fun _ => rfl }

def valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →+* E :=
  { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

def valueOrderRingHom {X E : Type*} [OrderedSemiring E] [TopologicalSpace X] {x : X} :
    Germ (𝓝 x) E →+*o E :=
  { Filter.Germ.valueRingHom with
    monotone' := fun φ ψ =>
      Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ h => h.self_of_nhds }

def _root_.Subring.orderedSubtype {R} [OrderedRing R] (s : Subring R) : s →+*o R :=
  { s.subtype with monotone' := fun _ _ h => h }

end Filter.Germ

-- TODO: add the final 110 lines from sphere-eversion - once NhdsSet is ported
