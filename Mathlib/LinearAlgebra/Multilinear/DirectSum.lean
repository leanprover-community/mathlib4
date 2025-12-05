/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Multilinear maps from direct sums

This file describes multilinear maps on direct sums.

## Main results

* `MultilinearMap.fromDirectSumEquiv` : If `ι` is a `Fintype`, `κ i` is a family of types
  indexed by `ι` and we are given a `R`-module `M i j` for every `i : ι` and `j : κ i`, this is
  the linear equivalence between `Π p : (i : ι) → κ i, MultilinearMap R (fun i ↦ M i (p i)) M'` and
  `MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'`.
-/

@[expose] public section

namespace MultilinearMap

open DirectSum

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
variable [CommSemiring R] [Fintype ι] [(i : ι) → DecidableEq (κ i)]
variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

/-- Two multilinear maps from direct sums are equal if they agree on the generators. -/
@[ext]
theorem directSum_ext ⦃f g : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i)) =
      g.compLinearMap (fun i => DirectSum.lof _ _ _ (p i))) : f = g :=
  dfinsupp_ext h

variable [DecidableEq ι]

/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ i, M i j`. -/
def fromDirectSumEquiv :
    ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' :=
  fromDFinsuppEquiv _ _

@[simp]
theorem fromDirectSumEquiv_lof
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    fromDirectSumEquiv f (fun i => lof R _ _ _ (x i)) = f p x :=
  fromDFinsuppEquiv_single _ _ _

/-- Prefer using `fromDirectSumEquiv_lof` where possible. -/
theorem fromDirectSumEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) :
    fromDirectSumEquiv f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) :=
  fromDFinsuppEquiv_apply _ _

@[simp]
theorem fromDirectSumEquiv_symm_apply (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : Π i, κ i) :
    fromDirectSumEquiv.symm f p = f.compLinearMap (fun i ↦ DirectSum.lof _ _ _ (p i)) :=
  rfl

end MultilinearMap
