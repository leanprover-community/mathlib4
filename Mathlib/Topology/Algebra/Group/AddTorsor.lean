/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Algebra.AddTorsor.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Topological torsors of groups

This file defines topological torsors of additive and multiplicative groups, that is, torsors where
`+ᵥ` and `-ᵥ` resp. `•` and `/ₛ` are continuous.
-/

@[expose] public section

open Topology

section Torsor

/-- A topological torsor over a topological additive group is a torsor where `+ᵥ` and `-ᵥ` are
continuous. -/
class IsTopologicalAddTorsor {V : Type*} [AddGroup V] [TopologicalSpace V]
    (P : Type*) [AddTorsor V P] [TopologicalSpace P] extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

/-- A topological torsor over a topological group is a torsor where `+ᵥ` and `-ᵥ` are continuous. -/
@[to_additive]
class IsTopologicalTorsor {V : Type*} [Group V] [TopologicalSpace V]
    (P : Type*) [Torsor V P] [TopologicalSpace P] extends ContinuousSMul V P where
  continuous_sdiv : Continuous (fun x : P × P => x.1 /ₛ x.2)

variable {V P α : Type*} [Group V] [TopologicalSpace V] [Torsor V P] [TopologicalSpace P]

export IsTopologicalAddTorsor (continuous_vsub)

export IsTopologicalTorsor (continuous_sdiv)

attribute [fun_prop] continuous_vsub continuous_sdiv

variable [IsTopologicalTorsor P]

@[to_additive]
theorem Filter.Tendsto.sdiv {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f /ₛ g) l (𝓝 (x /ₛ y)) :=
  (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[to_additive (attr := fun_prop)]
theorem Continuous.sdiv {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x /ₛ g x) :=
  continuous_sdiv.comp₂ hf hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.sdiv {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ f x /ₛ g x) x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.sdiv {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x /ₛ g x) s x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.sdiv {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x /ₛ g x) s := fun x hx ↦
  (hf x hx).sdiv (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
@[to_additive /-- The underlying group of a topological additive torsor is a topological additive
group. This is not an instance, as `P` cannot be inferred. -/]
theorem IsTopologicalTorsor.to_isTopologicalGroup : IsTopologicalGroup V where
  continuous_mul := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

/-- The map `v ↦ v +ᵥ p` as a homeomorphism between `V` and `P`. -/
@[to_additive (attr := simps!)]
def Homeomorph.smulConst (p : P) : V ≃ₜ P where
  __ := Equiv.smulConst p

end Torsor

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
instance : IsTopologicalTorsor G where
  continuous_sdiv := by simp only [sdiv_eq_div]; fun_prop

end Group

section Prod

variable
  {V W P Q : Type*}
  [CommGroup V] [TopologicalSpace V]
  [Torsor V P] [TopologicalSpace P] [IsTopologicalTorsor P]
  [CommGroup W] [TopologicalSpace W]
  [Torsor W Q] [TopologicalSpace Q] [IsTopologicalTorsor Q]

@[to_additive]
instance : IsTopologicalTorsor (P × Q) where
  continuous_smul := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι → Type*}
  [∀ i, CommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, Torsor (V i) (P i)] [∀ i, TopologicalSpace (P i)] [∀ i, IsTopologicalTorsor (P i)]

@[to_additive]
instance : IsTopologicalTorsor ((i : ι) → P i) where
  continuous_smul := continuous_pi <| by simp only [Pi.smul_apply']; fun_prop
  continuous_sdiv := continuous_pi <| by simp only [Pi.sdiv_apply]; fun_prop

end Pi
