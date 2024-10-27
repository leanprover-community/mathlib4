/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Interactions between (dependent) functions and multilinear maps

This file provides `MultilinearMap.pi`, which satisfies
`piFamily f x p = f p (fun i => x i (p i))`.

This is useful because all the intermediate results are bundled:

* `MultilinearMap.pi f` is a `MultilinearMap` operating on functions `x`.
* `MultilinearMap.piₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.

-/

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR} {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

namespace MultilinearMap

section Semiring

variable [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `piFamily f` maps a family of functions (one for each domain `κ i`) into a function
from each selection of indices (with domain `Π i, κ i`).
-/
@[simps]
def piFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun x := fun p => f p (fun i => x i (p i))
  map_add' {dec} m i x y := funext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.add_apply, (f p).map_add]
  map_smul' {dec} m i c x := funext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.smul_apply, (f p).map_smul]

/-- When applied to a family of finitely-supported functions each supported on a single element,
`piFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
theorem piFamily_single [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    piFamily f (fun i => Pi.single (p i) (m i)) = Pi.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [Pi.single_eq_of_ne' hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [Pi.single_eq_of_ne' hpqi]

@[simp]
theorem piFamily_compLinearMap_lsingle [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (piFamily f).compLinearMap (fun i => LinearMap.single _ _ (p i))
      = (LinearMap.single _ _ p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| piFamily_single f p

@[simp]
theorem piFamily_zero :
    piFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
theorem piFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (f + g) = piFamily f + piFamily g := by
  ext; simp

@[simp]
theorem piFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (s • f) = s • piFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/-- `MultilinearMap.piFamily` as a linear map. -/
@[simps]
def piFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun := piFamily
  map_add' := piFamily_add
  map_smul' := piFamily_smul

end CommSemiring

end MultilinearMap
