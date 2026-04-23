/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Continuous

/-!
# Definitions about topological groups

In this file we define mixin classes `ContinuousInv`, `IsTopologicalGroup`, and `ContinuousDiv`,
as well as their additive versions.

These classes say that the corresponding operations are continuous:

- `ContinuousInv G` says that `(·⁻¹)` is continuous on `G`;
- `IsTopologicalGroup G` says that `(· * ·)` is continuous on `G × G`
  and `(·⁻¹)` is continuous on `G`;
- `ContinuousDiv G` says that `(· / ·)` is continuous on `G`.

For groups, `ContinuousDiv G` is equivalent to `IsTopologicalGroup G`,
but we use the additive version `ContinuousSub` for types like `NNReal`,
where subtraction is not given by `a - b = a + (-b)`.

We also provide convenience dot notation lemmas like `ContinuousAt.neg`.
-/

@[expose] public section

open scoped Topology

universe u

variable {G α X : Type*} [TopologicalSpace X]

/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `AddGroup M` and
`ContinuousAdd M` and `ContinuousNeg M`. -/
class ContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a

attribute [continuity, fun_prop] ContinuousNeg.continuous_neg

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `Group M` and `ContinuousMul M` and
`ContinuousInv M`. -/
@[to_additive (attr := continuity)]
class ContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹

attribute [continuity, fun_prop] ContinuousInv.continuous_inv

export ContinuousInv (continuous_inv)
export ContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value.
For the version in topological groups with zero (including topological fields)
assuming additionally that the limit is nonzero, use `Filter.Tendsto.inv₀`. -/
@[to_additive
  /-- If a function converges to a value in an additive topological group, then its
  negation converges to the negation of this value. -/]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.tendsto y).comp h

variable {f : X → G} {s : Set X} {x : X}

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ :=
  continuous_inv.comp hf

@[to_additive]
nonrec theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x)⁻¹) s x :=
  hf.inv

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => (f x)⁻¹) x :=
  hf.inv

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x)⁻¹) s := fun x hx ↦
  (hf x hx).inv

end ContinuousInv

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `IsUniformAddGroup` using
`IsTopologicalAddGroup.rightUniformSpace` and `isUniformAddGroup_of_addCommGroup`. -/
class IsTopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] : Prop
    extends ContinuousAdd G, ContinuousNeg G

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `IsUniformGroup` using
`IsTopologicalGroup.rightUniformSpace` and `isUniformGroup_of_commGroup`. -/
@[to_additive]
class IsTopologicalGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop
    extends ContinuousMul G, ContinuousInv G

/-- A typeclass saying that `p : G × G ↦ p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class ContinuousSub (G : Type*) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2

/-- A typeclass saying that `p : G × G ↦ p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`. -/
@[to_additive existing]
class ContinuousDiv (G : Type*) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) IsTopologicalGroup.to_continuousDiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : ContinuousDiv G where
  continuous_div' := by
    simp only [div_eq_mul_inv]
    exact continuous_mul.comp₂ continuous_fst <| continuous_inv.comp continuous_snd

export ContinuousSub (continuous_sub)
export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.tendsto (a, b)).comp (hf.prodMk_nhds hg)

variable {f g : X → G} {s : Set X} {x : X}

@[to_additive (attr := fun_prop) sub]
nonrec theorem ContinuousAt.div' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  hf.div' hg

@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  Filter.Tendsto.div' hf hg

@[to_additive (attr := fun_prop) sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x / g x) s := fun x hx => (hf x hx).div' (hg x hx)

@[to_additive (attr := continuity, fun_prop) sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp₂ hf hg

end ContinuousDiv
