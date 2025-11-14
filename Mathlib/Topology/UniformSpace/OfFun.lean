/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.UniformSpace.Defs

/-!
# Construct a `UniformSpace` from a `dist`-like function

In this file we provide a constructor for `UniformSpace`
given a `dist`-like function

## TODO

RFC: use `UniformSpace.Core.mkOfBasis`? This will change defeq here and there
-/

open Filter Set
open scoped Uniformity

variable {X M : Type*}

namespace UniformSpace

/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring. -/
def ofFun [AddCommMonoid M] [PartialOrder M]
    (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    UniformSpace X :=
  .ofCore
    { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r }
      refl := le_iInf₂ fun r hr => principal_mono.2 <| by simp [Set.subset_def, *]
      symm := tendsto_iInf_iInf fun r => tendsto_iInf_iInf fun _ => tendsto_principal_principal.2
        fun x hx => by rwa [mem_setOf, symm]
      comp := le_iInf₂ fun r hr => let ⟨δ, h0, hδr⟩ := half r hr; le_principal_iff.2 <|
        mem_of_superset
          (mem_lift' <| mem_iInf_of_mem δ <| mem_iInf_of_mem h0 <| mem_principal_self _)
          fun (x, z) ⟨y, h₁, h₂⟩ => (triangle _ _ _).trans_lt (hδr _ h₁ _ h₂) }

theorem hasBasis_ofFun [AddCommMonoid M] [LinearOrder M]
    (h₀ : ∃ x : M, 0 < x) (d : X → X → M) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    𝓤[.ofFun d refl symm triangle half].HasBasis ((0 : M) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  hasBasis_biInf_principal'
    (fun ε₁ h₁ ε₂ h₂ => ⟨min ε₁ ε₂, lt_min h₁ h₂, fun _x hx => lt_of_lt_of_le hx (min_le_left _ _),
      fun _x hx => lt_of_lt_of_le hx (min_le_right _ _)⟩) h₀

open scoped Topology in
/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed using the "distance",
and we make sure that the uniform space structure we construct has a topology which is defeq
to the original one. -/
def ofFunOfHasBasis [t : TopologicalSpace X] [AddCommMonoid M] [LinearOrder M]
    (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε)
    (basis : ∀ x, (𝓝 x).HasBasis (fun ε ↦ 0 < ε) (fun ε ↦ {y | d x y < ε})) :
    UniformSpace X where
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x :=
    (basis x).eq_of_same_basis <|
      (hasBasis_ofFun (basis x).ex_mem d refl symm triangle half).comap (Prod.mk x)
  __ := ofFun d refl symm triangle half

end UniformSpace
