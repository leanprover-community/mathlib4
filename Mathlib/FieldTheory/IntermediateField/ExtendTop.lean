/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Extending intermediate fields to a larger extension

Given a tower of field extensions `K ⊆ L ⊆ M` and an intermediate field `F` of `L/K`, this file
defines `IntermediateField.extendTop F M`, the image of `F` under the inclusion `L ⊆ M`,
as an intermediate field of `M/K`. It is canonically isomorphic to `F` as a `K`-algebra.

The main motivation is to embed a subextension `F/K` of `L/K` into a larger extension `M/K`.
This is useful for instance when one needs `M/K` to be Galois.

## Main definitions

- `IntermediateField.extendTop F M`: the intermediate field of `M/K` defined as the image of `F`
  under the map `L →ₐ[K] M`.
- `IntermediateField.extendTopEquiv F M`: the `K`-algebra isomorphism `F ≃ₐ[K] extendTop F M`.

## Main instances

- `IntermediateField.extendTop.algebra`: for `S` with `Algebra S F`, `S` acts on `extendTop F M`.
- `IntermediateField.extendTop.isFractionRing`: transfers the `IsFractionRing S F` instance.
- `IntermediateField.extendTop.isIntegralClosure`: transfers the `IsIntegralClosure S R F` instance.
-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/--
The image of the intermediate field `F` of `L/K` under the inclusion `L ⊆ M`, viewed as an
intermediate field of `M/K`.
-/
abbrev extendTop : IntermediateField K M := F.map (Algebra.algHom K L M)

/-- The isomorphism between `F` and its image `F.extendTop M` in `M`. -/
noncomputable abbrev extendTopEquiv : F ≃ₐ[K] (F.extendTop M) := F.equivMap (Algebra.algHom K L M)

theorem algebraMap_extendTopEquiv (a : F) :
    algebraMap (F.extendTop M) M (extendTopEquiv F M a) = algebraMap F M a := rfl

theorem algebraMap_extendTopEquiv_symm (a : F.extendTop M) :
    algebraMap F M ((extendTopEquiv F M).symm a) = a := by
  rw [← algebraMap_extendTopEquiv, AlgEquiv.apply_symm_apply, algebraMap_apply]

namespace extendTop

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra S F]

variable [Algebra S M] [IsScalarTower S F M]

theorem algebraMap_mem (s : S) : algebraMap S M s ∈ F.extendTop M := by
  rw [IsScalarTower.algebraMap_apply S F M, IsScalarTower.algebraMap_apply F L M]
  exact ⟨algebraMap F L (algebraMap S F s), by simp, rfl⟩

instance : SMul S (F.extendTop M) where
  smul s x := by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    exact (F.extendTop M).mul_mem (algebraMap_mem F M s) x.prop

@[simp]
theorem coe_smul (s : S) (x : F.extendTop M) :
    (s • x : F.extendTop M) = s • (x : M) := rfl

-- The algebra instance is defined this way to avoid diamonds, see below
noncomputable instance algebra : Algebra S (F.extendTop M) where
  algebraMap := (algebraMap S M).codRestrict (F.extendTop M) fun x ↦ algebraMap_mem F M x
  commutes' _ _ := Subtype.ext <| by simp [Algebra.commutes]
  smul_def' s x := Subtype.ext <| by
    convert_to s • (x : M) = _
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply, ← Algebra.smul_def]

-- Check there is no diamond
example [Algebra S K] [IsScalarTower S K M] :
    ((F.extendTop M).algebra' : Algebra S (F.extendTop M)) =
      (algebra F M : Algebra S (F.extendTop M)) := rfl

instance : IsScalarTower S (F.extendTop M) M := IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower S F (F.extendTop M) := IsScalarTower.to₁₂₃ S F (F.extendTop M) M

instance [Algebra R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
    IsScalarTower R S (F.extendTop M) :=
  IsScalarTower.to₁₂₃ R S (F.extendTop M) M

/--
Variant of `extendTopEquiv` giving an `S`-algebra isomorphism `F ≃ₐ[S] F.extendTop M`,
for a commutative ring `S` with `Algebra S F`.
-/
@[simps! apply_coe]
noncomputable def _root_.IntermediateField.extendTopEquiv' : F ≃ₐ[S] (F.extendTop M) :=
  AlgEquiv.ofBijective (Algebra.algHom S F (F.extendTop M)) (extendTopEquiv F M).bijective

instance isFractionRing [IsFractionRing S F] :
    IsFractionRing S (F.extendTop M) :=
  .of_algEquiv (R := S) (L := F.extendTop M) (K := F) <| F.extendTopEquiv' M

instance isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M]
    [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendTop M) := by
  refine .of_algEquiv S (F.extendTopEquiv' M) fun x ↦ ?_
  rw [Subtype.ext_iff, extendTopEquiv'_apply_coe, ← IsScalarTower.algebraMap_apply,
    ← algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end IntermediateField.extendTop
