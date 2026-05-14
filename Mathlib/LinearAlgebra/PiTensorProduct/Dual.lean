/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attr
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# Tensor products of dual spaces

## Main definitions

* `PiTensorProduct.dualDistrib`: The canonical linear map from `⨂[R] i, Dual R (M i)` to
  `Dual R (⨂[R] i, M i)`, sending `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.

* `PiTensorProduct.dualDistribEquiv`: A linear equivalence between `⨂[R] i, Dual R (M i)`
  and `Dual R (⨂[R] i, M i)` when all `M i` are finite free modules. If
  `f : (i : ι) → Dual R (M i)`, then this equivalence sends `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the natural isomorphism `⨂[R] i, R ≃ R` given by multiplication.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct LinearMap Module TensorProduct

variable {ι : Type*}

section SemiRing

variable {R : Type*} {M : ι → Type*} [CommSemiring R] [Π i, AddCommMonoid (M i)]
  [Π i, Module R (M i)]

/-- The canonical linear map from `⨂[R] i, Dual R (M i)` to `Dual R (⨂[R] i, M i)`,
sending `⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with
the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication. -/
noncomputable def dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

@[simp]
theorem dualDistrib_apply [Fintype ι] (f : Π i, Dual R (M i)) (m : Π i, M i) :
    dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i) := by
  rw [dualDistrib, Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

end SemiRing

section Ring

variable {R : Type*} {κ : ι → Type*} {M : ι → Type*} [CommRing R] [Π i, AddCommGroup (M i)]
  [Π i, Module R (M i)]

open Classical in
/-- An inverse to `PiTensorProduct.dualDistrib` given bases. -/
noncomputable def dualDistribInvOfBasis [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    Dual R (⨂[R] i, M i) →ₗ[R] ⨂[R] i, Dual R (M i) :=
  haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R ℕ _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

open Classical in
@[simp]
theorem dualDistribInvOfBasis_apply [Fintype ι] [∀ i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i))
    (f : Dual R (⨂[R] i, M i)) : dualDistribInvOfBasis b f =
    ∑ p : (Π i, κ i), f (⨂ₜ[R] i, b i (p i)) • (⨂ₜ[R] i, (b i).dualBasis (p i)) := by
  simp only [dualDistribInvOfBasis, Basis.coe_dualBasis, ringLmapEquivSelf_symm_apply, coe_sum,
    coe_comp, coe_smulRight, End.one_apply, Finset.sum_apply, Function.comp_apply,
    applyₗ_apply_apply]
  convert rfl

theorem dualDistrib_dualDistribInvOfBasis_left_inverse [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistrib) ∘ₗ (dualDistribInvOfBasis b) = LinearMap.id := by
  haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p ↦ ?_)
  refine (Basis.piTensorProduct b).ext (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

theorem dualDistrib_dualDistribInvOfBasis_right_inverse [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistribInvOfBasis b) ∘ₗ dualDistrib = LinearMap.id := by
  haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext (fun p ↦ ?_)
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext_elem (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)`
given bases for all `M i`. If `f : (i : ι) → Dual R (s i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simps!]
noncomputable def dualDistribEquivOfBasis [Finite ι] [∀ i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  LinearEquiv.ofLinear dualDistrib (dualDistribInvOfBasis b)
    (dualDistrib_dualDistribInvOfBasis_left_inverse _)
    (dualDistrib_dualDistribInvOfBasis_right_inverse _)

variable [Π i, Module.Finite R (M i)] [Π i, Module.Free R (M i)]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)` when all
`M i` are finite free modules. If `f : (i : ι) → Dual R (M i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simp]
noncomputable def dualDistribEquiv [Finite ι] :
    (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  dualDistribEquivOfBasis (fun i ↦ Module.Free.chooseBasis R (M i))

end Ring

end PiTensorProduct
