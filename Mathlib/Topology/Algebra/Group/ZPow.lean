/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Monoid

/-!
# Integer powers in topological groups

Continuity results for integer powers and integer scalar multiplication in topological groups.
-/

public section

open Filter Topology

variable {G α : Type*}

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace α]

section ZPow

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | Int.negSucc n => by simpa using (continuous_pow (n + 1)).fun_inv

instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousConstSMul ℤ A :=
  ⟨continuous_zsmul⟩

instance AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousSMul ℤ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous (f ^ z) :=
  (continuous_zpow z).comp h

@[to_additive]
theorem continuousOn_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).continuousOn

@[to_additive]
theorem continuousAt_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).continuousAt

@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (f ^ z) s x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (f ^ z) x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (f ^ z) s := fun x hx => (hf x hx).zpow z

end ZPow
