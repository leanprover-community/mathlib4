/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
import Mathlib.Algebra.AddTorsor.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Defs

/-!
# Topological torsors of additive groups

This file defines topological torsors of additive groups, that is, torsors where `+ᵥ` and `-ᵥ` are
continuous.
-/

open Topology

section AddTorsor

variable {V P α : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P] [TopologicalSpace P]

variable (P) in
/-- A topological torsor over a topological additive group is a torsor where `+ᵥ` and `-ᵥ` are
continuous. -/
class IsTopologicalAddTorsor extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

export IsTopologicalAddTorsor (continuous_vsub)

attribute [fun_prop] continuous_vsub

variable [IsTopologicalAddTorsor P]

theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[fun_prop]
theorem Continuous.vsub {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x -ᵥ g x) :=
  continuous_vsub.comp₂ hf hg

@[fun_prop]
nonrec theorem ContinuousAt.vsub {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ f x -ᵥ g x) x :=
  hf.vsub hg

@[fun_prop]
nonrec theorem ContinuousWithinAt.vsub {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x -ᵥ g x) s x :=
  hf.vsub hg

@[fun_prop]
theorem ContinuousOn.vsub {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x -ᵥ g x) s := fun x hx ↦
  (hf x hx).vsub (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
theorem IsTopologicalAddTorsor.to_isTopologicalAddGroup : IsTopologicalAddGroup V where
  continuous_add := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 +ᵥ x.2 +ᵥ p) -ᵥ p => rw [vadd_vadd, vadd_vsub]
    fun_prop
  continuous_neg := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p -ᵥ (v +ᵥ p) => rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
    fun_prop

/-- The map `v ↦ v +ᵥ p` as a homeomorphism between `V` and `P`. -/
@[simps!]
def Homeomorph.vaddConst (p : P) : V ≃ₜ P where
  __ := Equiv.vaddConst p
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end AddTorsor

section AddGroup

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

instance : IsTopologicalAddTorsor G where
  continuous_vsub := by simp only [vsub_eq_sub]; fun_prop

end AddGroup

section Prod

variable
  {V W P Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

instance : IsTopologicalAddTorsor (P × Q) where
  continuous_vadd := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_vsub := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, AddTorsor (V i) (P i)] [∀ i, TopologicalSpace (P i)] [∀ i, IsTopologicalAddTorsor (P i)]

instance : IsTopologicalAddTorsor ((i : ι) → P i) where
  continuous_vadd := continuous_pi <| by simp only [Pi.vadd_apply']; fun_prop
  continuous_vsub := continuous_pi <| by simp only [Pi.vsub_apply]; fun_prop

end Pi
