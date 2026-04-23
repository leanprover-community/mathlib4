/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Extending intermediate fields to a larger extension

Given a tower of field extensions `K ⊆ L ⊆ M` and an intermediate field `F` of `L/K`, this file
defines `IntermediateField.extendRight F M`, the image of `F` under the inclusion `L ⊆ M`,
as an intermediate field of `M/K`. It is canonically isomorphic to `F` as a `K`-algebra.

The main motivation is to embed a subextension `F/K` of `L/K` into a larger extension `M/K`.
This is useful for instance when one needs `M/K` to be Galois.

## Main definitions

- `IntermediateField.extendRight F M`: the intermediate field of `M/K` defined as the image of `F`
  under the map `L →ₐ[K] M`.
- `IntermediateField.extendRightEquiv F M`: the `K`-algebra isomorphism `F ≃ₐ[K] extendRight F M`.

## Main instances

- `IntermediateField.extendRight.algebra`: for `S` with `Algebra S F`, `S` acts
  on `extendRight F M`.
- `IntermediateField.extendRight.isFractionRing`: transfers the `IsFractionRing S F` instance.
- `IntermediateField.extendRight.isIntegralClosure`: transfers the
  `IsIntegralClosure S R F` instance.
-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/--
The image of the intermediate field `F` of `L/K` under the inclusion `L ⊆ M`, viewed as an
intermediate field of `M/K`.
-/
def extendRight : IntermediateField K M := F.map (Algebra.algHom K L M)

/-- The isomorphism between `F` and its image `F.extendRight M` in `M`. -/
noncomputable def extendRightEquiv : F ≃ₐ[K] (F.extendRight M) := F.equivMap (Algebra.algHom K L M)

@[simp]
theorem algebraMap_extendRightEquiv (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv F M a) = algebraMap F M a := rfl

@[simp]
theorem coe_extendRightEquiv (a : F) :
    (extendRightEquiv F M a : M) = algebraMap F M a := rfl

@[simp]
theorem algebraMap_extendRightEquiv_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv F M).symm a) = a := by
  rw [← algebraMap_extendRightEquiv, AlgEquiv.apply_symm_apply, algebraMap_apply]

namespace extendRight

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra S F]

variable [Algebra S M] [IsScalarTower S F M]

theorem algebraMap_mem (s : S) : algebraMap S M s ∈ F.extendRight M := by
  rw [IsScalarTower.algebraMap_apply S F M, IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩

instance : SMul S (F.extendRight M) where
  smul s x := by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendRight M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]
theorem coe_smul (s : S) (x : F.extendRight M) :
    (s • x : F.extendRight M) = s • (x : M) := rfl

-- The algebra instance is defined this way to avoid diamonds, see below
noncomputable instance algebra : Algebra S (F.extendRight M) where
  algebraMap := (algebraMap S M).codRestrict (F.extendRight M).toSubalgebra (algebraMap_mem F M ·)
  commutes' _ _ := Subtype.ext <| by simp [Algebra.commutes]
  smul_def' s x := Subtype.ext <| by
    convert_to s • (x : M) = _
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply, ← Algebra.smul_def]

-- Check there is no diamond
example [Algebra S K] [IsScalarTower S K M] :
    ((F.extendRight M).algebra' : Algebra S (F.extendRight M)) =
      (algebra F M : Algebra S (F.extendRight M)) := by
  with_reducible_and_instances rfl

instance : IsScalarTower S (F.extendRight M) M := IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower S F (F.extendRight M) := IsScalarTower.to₁₂₃ S F (F.extendRight M) M

instance [Algebra R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
    IsScalarTower R S (F.extendRight M) :=
  IsScalarTower.to₁₂₃ R S (F.extendRight M) M

variable (S)

/--
Variant of `extendRightEquiv` giving an `S`-algebra isomorphism `F ≃ₐ[S] F.extendRight M`,
for a commutative ring `S` with `Algebra S F`.
-/
noncomputable def _root_.IntermediateField.extendRightEquiv' : F ≃ₐ[S] (F.extendRight M) :=
  AlgEquiv.ofBijective (Algebra.algHom S F (F.extendRight M)) (extendRightEquiv F M).bijective

@[simp]
theorem coe_extendRightEquiv' (a : F) :
    (extendRightEquiv' F M S a : M) = algebraMap F M a := rfl

@[simp]
theorem algebraMap_extendRightEquiv' (a : F) :
    algebraMap (F.extendRight M) M (extendRightEquiv' F M S a) = algebraMap F M a := rfl

@[simp]
theorem algebraMap_extendRightEquiv'_symm (a : F.extendRight M) :
    algebraMap F M ((extendRightEquiv' F M S).symm a) = a := by
  rw [← algebraMap_extendRightEquiv' F M S, AlgEquiv.apply_symm_apply, algebraMap_apply]

variable {S}

instance isFractionRing [IsFractionRing S F] :
    IsFractionRing S (F.extendRight M) :=
  .of_algEquiv (R := S) (L := F.extendRight M) (K := F) <| F.extendRightEquiv' M S

instance isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M]
    [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendRight M) := by
  refine .of_algEquiv S (F.extendRightEquiv' M R) fun x ↦ ?_
  rw [Subtype.ext_iff, ← algebraMap_apply (F.extendRight M), ← algebraMap_apply (F.extendRight M),
    algebraMap_extendRightEquiv', ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

end IntermediateField.extendRight
