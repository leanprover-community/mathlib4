/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `freeFinsuppEquiv` is an equivalence of multilinear maps over free modules with finitely
  supported maps.

-/

@[expose] public section

variable {ι ι' R : Type*} {κ : ι → Type*}

namespace MultilinearMap

section freeFinsuppEquiv

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/--
The linear equivalence of multilinear maps on free modules over `R` indexed by `fun i => κ i` on
the domain and `ι'` on the codomain and the finitely supported maps from
`(Π i, κ i) × ι'` into `R`.

This is the `Finsupp` version of `MultilinearMap.freeDFinsuppEquiv`.
-/
noncomputable def freeFinsuppEquiv :
    (((Π i, κ i) × ι') →₀ R) ≃ₗ[R] MultilinearMap R (fun i => (κ i →₀ R)) (ι' →₀ R) :=
  (finsuppLequivDFinsupp R) ≪≫ₗ freeDFinsuppEquiv ≪≫ₗ
  ((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm ≪≫ₗ
  LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)

theorem freeFinsuppEquiv_def (f : ((Π i, κ i) × ι') →₀ R) :
    freeFinsuppEquiv f =
      LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)
      (((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm <|
      freeDFinsuppEquiv (finsuppLequivDFinsupp R f)) :=
  rfl

/--
When `freeFinsuppEquiv` is applied to a map with a single value the resulting multilinear
map sends inputs to a single value in the codomain, taking a product over images from each
component of the domain.
-/
@[simp]
theorem freeFinsuppEquiv_single (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i →₀ R)) :
    freeFinsuppEquiv (Finsupp.single p r) x = r • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  simp [freeFinsuppEquiv_def]

theorem freeFinsuppEquiv_apply [Fintype ι']
  (f : ((Π i, κ i) × ι') →₀ R) (x : Π i, (κ i →₀ R)) :
  freeFinsuppEquiv f x = ∑ p, f p • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | single p r => simp [Finsupp.single_apply]

end freeFinsuppEquiv

end MultilinearMap
