/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# Results on finitely supported functions.

* `ofFinsuppEquiv`, the tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly
  equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct TensorProduct

attribute [local ext] TensorProduct.ext

variable {R ι : Type*} {κ M : ι → Type*}
variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, DecidableEq (M i)]

/-- If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
noncomputable def ofFinsuppEquiv :
    (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ ↦ finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm

@[simp]
theorem ofFinsuppEquiv_tprod_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    ofFinsuppEquiv (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  simp [ofFinsuppEquiv]

@[simp]
theorem ofFinsuppEquiv_apply (f : (i : ι) → (κ i →₀ M i)) (p : (i : ι) → κ i) :
    ofFinsuppEquiv (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  simp [ofFinsuppEquiv]

@[simp]
theorem ofFinsuppEquiv_symm_single_tprod (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    ofFinsuppEquiv.symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (ofFinsuppEquiv_tprod_single _ _).symm

variable [DecidableEq R]

/-- A variant of `ofFinsuppEquiv` where all modules `M i` are the ground ring. -/
noncomputable def ofFinsuppEquiv' : (⨂[R] i, (κ i →₀ R)) ≃ₗ[R] ((i : ι) → κ i) →₀ R :=
  ofFinsuppEquiv ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) → κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
theorem ofFinsuppEquiv'_apply_apply (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i) :
    ofFinsuppEquiv' (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp [ofFinsuppEquiv']

@[simp]
theorem ofFinsuppEquiv'_tprod_single (p : (i : ι) → κ i) (r : ι → R) :
    ofFinsuppEquiv' (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  simp [ofFinsuppEquiv']

end PiTensorProduct
